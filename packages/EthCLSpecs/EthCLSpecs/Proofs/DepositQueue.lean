/-!
# `EthCLSpecs.Proofs.DepositQueue`: the list argument behind the validator index assignment

`process_pending_deposits` is the one step of a fork's state transition that appends to the
validator registry. This module holds the part of the index-assignment proof that reads no
spec code: plain lists of keys and deposits, and the three facts about them.

* A scan consumes a prefix of the queue, and each consumed deposit adds at most one key at
  the end of the key list (`stepKeys`, `Scan`).
* A chain that consumes deposits of a fixed queue `Q` alone has the keys of some prefix of
  `Q` (`OnQueue`). A chain with no such limit has those keys too, until it has consumed all of
  `Q`, and then its key list extends the keys of all of `Q` (`Tracks`).
* Two such key lists are prefixes of one list, so one is a prefix of the other
  (`comparable`), and they agree at each index both have (`getElem_eq_of_comparable`).

Two more facts serve the proof across the Gloas upgrade, which takes deposits out of the
middle of the queue.

* A scan of a queue is a scan of the filtered queue, when the filter drops no consumed
  deposit with a valid signature (`Scan.filter`). A scan is also a scan of a copy of the
  queue at another deposit type (`Scan.map`).
* `Chain` packs `OnQueue` and `Tracks` for one state of a chain, so one induction per fork
  carries both.

The module is generic in the key type `κ` and the deposit type `δ`. Each fork declares its own
`PendingDeposit`, so the Fulu and Gloas proofs both instantiate it. `key` reads a deposit's
public key, and `valid` is the proof-of-possession check.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.DepositQueue

section

variable {κ δ : Type} [DecidableEq κ] (key : δ → κ) (valid : δ → Bool)

/-! ## One deposit, and a run of deposits -/

/-- The key list after one consumed deposit. A key the list holds is a top-up and adds
nothing. A new key joins at the end when its signature is valid. -/
def stepKeys (K : List κ) (d : δ) : List κ :=
  if key d ∈ K then K else if valid d then K ++ [key d] else K

/-- The key list after the deposits `l`, consumed in order from `K`. -/
def keysAfter (K : List κ) (l : List δ) : List κ := l.foldl (stepKeys key valid) K

theorem prefix_stepKeys (K : List κ) (d : δ) : K <+: stepKeys key valid K d := by
  unfold stepKeys
  split
  · exact List.prefix_rfl
  · split
    · exact List.prefix_append _ _
    · exact List.prefix_rfl

/-- Consuming deposits only appends keys. -/
theorem prefix_keysAfter (K : List κ) (l : List δ) : K <+: keysAfter key valid K l := by
  induction l generalizing K with
  | nil => exact List.prefix_rfl
  | cons d l ih => exact (prefix_stepKeys key valid K d).trans (ih _)

theorem keysAfter_append (K : List κ) (l l' : List δ) :
    keysAfter key valid K (l ++ l') = keysAfter key valid (keysAfter key valid K l) l' :=
  List.foldl_append

theorem stepKeys_of_mem {K : List κ} {d : δ} (h : key d ∈ K) : stepKeys key valid K d = K := by
  simp [stepKeys, h]

/-- Deposits for keys the list holds change nothing. -/
theorem keysAfter_of_forall_mem {K : List κ} {l : List δ} (h : ∀ e ∈ l, key e ∈ K) :
    keysAfter key valid K l = K := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    show keysAfter key valid (stepKeys key valid K d) l = K
    rw [stepKeys_of_mem key valid (h d List.mem_cons_self)]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-! ## One scan of the queue -/

/-- One run of the queue scan, from keys `K` and queue `q` to keys `K'` and queue `q'`. The
scan consumes the first `n` deposits, each of which satisfies `fin` (its slot is finalized).
The new queue is the rest of the old one, then the postponed deposits `post`. A postponed
deposit names a key the registry holds. -/
def Scan (fin : δ → Prop) (K K' : List κ) (q q' : List δ) : Prop :=
  ∃ (n : Nat) (post : List δ),
    K' = keysAfter key valid K (q.take n) ∧ q' = q.drop n ++ post ∧
    (∀ e ∈ post, key e ∈ K') ∧ (∀ e ∈ q.take n, fin e)

/-- A scan that consumes nothing. -/
theorem Scan.refl (fin : δ → Prop) (K : List κ) (q : List δ) : Scan key valid fin K K q q :=
  ⟨0, [], rfl, by simp, by simp, by simp⟩

/-- A scan under a stronger reading of `fin`. -/
theorem Scan.mono {fin fin' : δ → Prop} {K K' : List κ} {q q' : List δ}
    (h : Scan key valid fin K K' q q') (hf : ∀ e, fin e → fin' e) :
    Scan key valid fin' K K' q q' := by
  obtain ⟨n, post, hK, hq, hpost, hcons⟩ := h
  exact ⟨n, post, hK, hq, hpost, fun e he => hf e (hcons e he)⟩

theorem Scan.prefix {fin : δ → Prop} {K K' : List κ} {q q' : List δ}
    (h : Scan key valid fin K K' q q') : K <+: K' := by
  obtain ⟨n, post, hK, -, -, -⟩ := h
  exact hK ▸ prefix_keysAfter key valid K _

/-! ## A scan of a filtered queue

A deposit with an invalid signature adds no key: `stepKeys` returns the key list it was given.
So a queue and the same queue without some of those deposits give one key list. `p` is the
filter, and it may drop a deposit of the consumed part only when that deposit is invalid. The
Gloas upgrade is the user: it takes deposits out of the middle of the queue, and the proof
reads each chain's queue through one filter (`Proofs/Gloas/IndexAssignmentFromFulu.lean`). -/

/-- An invalid deposit adds no key. -/
theorem stepKeys_of_not_valid (K : List κ) {d : δ} (h : valid d = false) :
    stepKeys key valid K d = K := by
  simp [stepKeys, h]

/-- Dropping invalid deposits from a run changes no key. -/
theorem keysAfter_filter (p : δ → Bool) (K : List κ) {l : List δ}
    (h : ∀ e ∈ l, valid e = true → p e = true) :
    keysAfter key valid K (l.filter p) = keysAfter key valid K l := by
  induction l generalizing K with
  | nil => rfl
  | cons d l ih =>
    have hl : ∀ e ∈ l, valid e = true → p e = true :=
      fun e he => h e (List.mem_cons_of_mem _ he)
    by_cases hp : p d = true
    · rw [List.filter_cons_of_pos hp]
      exact ih _ hl
    · rw [List.filter_cons_of_neg hp]
      have hv : valid d = false := by
        cases hvd : valid d with
        | false => rfl
        | true => exact absurd (h d List.mem_cons_self hvd) hp
      show keysAfter key valid K (l.filter p) = keysAfter key valid (stepKeys key valid K d) l
      rw [stepKeys_of_not_valid key valid K hv]
      exact ih _ hl

/-- A filter splits at the point where `take n` and `drop n` split the list: the filtered
list, cut at the length of the filtered prefix, gives the two filtered parts. -/
theorem filter_take_drop (p : δ → Bool) (q : List δ) (n : Nat) :
    (q.filter p).take ((q.take n).filter p).length = (q.take n).filter p ∧
    (q.filter p).drop ((q.take n).filter p).length = (q.drop n).filter p := by
  have hq : q.filter p = (q.take n).filter p ++ (q.drop n).filter p := by
    rw [← List.filter_append, List.take_append_drop]
  constructor
  · rw [hq, List.take_left]
  · rw [hq, List.drop_left]

/-- A scan of a queue is a scan of the filtered queue, when each consumed deposit the filter
drops is invalid. The consumed part of the filtered queue is the filtered consumed part, and
`keysAfter_filter` gives it the same keys. -/
theorem Scan.filter {fin : δ → Prop} {K K' : List κ} {q q' : List δ} (p : δ → Bool)
    (h : Scan key valid fin K K' q q') (hp : ∀ e, fin e → valid e = true → p e = true) :
    Scan key valid fin K K' (q.filter p) (q'.filter p) := by
  obtain ⟨n, post, hK, hq, hpost, hcons⟩ := h
  obtain ⟨htake, hdrop⟩ := filter_take_drop p q n
  refine ⟨((q.take n).filter p).length, post.filter p, ?_, ?_, ?_, ?_⟩
  · rw [htake, hK]
    exact (keysAfter_filter key valid p K fun e he => hp e (hcons e he)).symm
  · rw [hdrop, hq, List.filter_append]
  · exact fun e he => hpost e (List.mem_filter.mp he).1
  · rw [htake]
    exact fun e he => hcons e (List.mem_filter.mp he).1

/-! ## A scan read at another deposit type

Each fork declares its own `PendingDeposit`, and the Gloas upgrade copies the queue of the
Fulu state one deposit at a time. A scan of the Fulu queue is then a scan of the copied
queue, when the copy `f` keeps the key and the validity of each deposit. -/

section Map

variable {δ' : Type} (key' : δ' → κ) (valid' : δ' → Bool) (f : δ → δ')

theorem stepKeys_map (hkey : ∀ e, key' (f e) = key e) (hvalid : ∀ e, valid' (f e) = valid e)
    (K : List κ) (d : δ) : stepKeys key' valid' K (f d) = stepKeys key valid K d := by
  simp [stepKeys, hkey, hvalid]

theorem keysAfter_map (hkey : ∀ e, key' (f e) = key e) (hvalid : ∀ e, valid' (f e) = valid e)
    (K : List κ) (l : List δ) :
    keysAfter key' valid' K (l.map f) = keysAfter key valid K l := by
  induction l generalizing K with
  | nil => rfl
  | cons d l ih =>
    show keysAfter key' valid' (stepKeys key' valid' K (f d)) (l.map f) = _
    rw [stepKeys_map key valid key' valid' f hkey hvalid, ih]
    rfl

/-- A scan of a queue is a scan of the copied queue, at the copy's reading `fin'` of
"finalized". -/
theorem Scan.map {fin : δ → Prop} {fin' : δ' → Prop} {K K' : List κ} {q q' : List δ}
    (h : Scan key valid fin K K' q q') (hkey : ∀ e, key' (f e) = key e)
    (hvalid : ∀ e, valid' (f e) = valid e) (hfin : ∀ e, fin e → fin' (f e)) :
    Scan key' valid' fin' K K' (q.map f) (q'.map f) := by
  obtain ⟨n, post, hK, hq, hpost, hcons⟩ := h
  refine ⟨n, post.map f, ?_, ?_, ?_, ?_⟩
  · rw [← List.map_take, keysAfter_map key valid key' valid' f hkey hvalid]
    exact hK
  · rw [hq, List.map_append, List.map_drop]
  · intro e he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    rw [hkey]
    exact hpost e₀ he₀
  · intro e he
    rw [← List.map_take] at he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    exact hfin e₀ (hcons e₀ he₀)

end Map

/-! ## A chain that stays on the queue `Q` -/

/-- The keys `K` and queue `q` of a chain that started at keys `R` and queue `Q` and has
consumed a prefix of `Q` and no other deposit that adds a key. The queue is the rest of `Q`,
then the deposits `X` that joined later. Each of those names a key the registry holds, or
satisfies `adm`, the reading "a scan cannot consume it". -/
def OnQueue (R : List κ) (Q : List δ) (adm : δ → Prop) (K : List κ) (q : List δ) : Prop :=
  ∃ (k : Nat) (X : List δ),
    q = Q.drop k ++ X ∧ K = keysAfter key valid R (Q.take k) ∧ ∀ e ∈ X, key e ∈ K ∨ adm e

theorem OnQueue.start (R : List κ) (Q : List δ) (adm : δ → Prop) :
    OnQueue key valid R Q adm R Q :=
  ⟨0, [], by simp, rfl, by simp⟩

/-- Appends of admitted deposits, or of deposits for held keys, keep the chain on the queue. -/
theorem OnQueue.append {R : List κ} {Q : List δ} {adm : δ → Prop} {K : List κ} {q : List δ}
    (h : OnQueue key valid R Q adm K q) {X' : List δ} (hX : ∀ e ∈ X', key e ∈ K ∨ adm e) :
    OnQueue key valid R Q adm K (q ++ X') := by
  obtain ⟨k, X, hq, hK, hadm⟩ := h
  refine ⟨k, X ++ X', by rw [hq, List.append_assoc], hK, ?_⟩
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact hadm e h
  · exact hX e h

/-- A scan keeps the chain on the queue, when no deposit it consumes is an admitted one. The
consumed deposits are then a stretch of `Q` followed by deposits for held keys, and the
second part adds nothing. -/
theorem OnQueue.scan {R : List κ} {Q : List δ} {adm fin : δ → Prop} {K K' : List κ}
    {q q' : List δ} (h : OnQueue key valid R Q adm K q) (hs : Scan key valid fin K K' q q')
    (hfin : ∀ e, fin e → ¬ adm e) : OnQueue key valid R Q adm K' q' := by
  have hpre : K <+: K' := hs.prefix
  obtain ⟨k, X, hq, hK, hadm⟩ := h
  obtain ⟨n, post, hK', hq', hpost, hcons⟩ := hs
  subst hq
  rw [List.take_append] at hK' hcons
  rw [List.drop_append] at hq'
  have hXcons : ∀ e ∈ X.take (n - (Q.drop k).length), key e ∈ K := by
    intro e he
    have hfe : fin e := hcons e (List.mem_append_right _ he)
    rcases hadm e (List.mem_of_mem_take he) with h | h
    · exact h
    · exact absurd h (hfin e hfe)
  refine ⟨k + n, X.drop (n - (Q.drop k).length) ++ post, ?_, ?_, ?_⟩
  · rw [hq', List.drop_drop, List.append_assoc]
  · rw [hK', keysAfter_append, List.take_add, keysAfter_append, ← hK]
    exact keysAfter_of_forall_mem key valid fun e he =>
      (prefix_keysAfter key valid K _).subset (hXcons e he)
  · intro e he
    rcases List.mem_append.mp he with h | h
    · rcases hadm e (List.mem_of_mem_drop h) with h' | h'
      · exact Or.inl (hpre.subset h')
      · exact Or.inr h'
    · exact Or.inl (hpost e h)

/-- A chain on the queue has a prefix of the keys of the whole queue. -/
theorem OnQueue.prefix_full {R : List κ} {Q : List δ} {adm : δ → Prop} {K : List κ}
    {q : List δ} (h : OnQueue key valid R Q adm K q) : K <+: keysAfter key valid R Q := by
  obtain ⟨k, X, -, hK, -⟩ := h
  have hQ : keysAfter key valid R Q = keysAfter key valid K (Q.drop k) := by
    rw [hK, ← keysAfter_append, List.take_append_drop]
  rw [hQ]
  exact prefix_keysAfter key valid K _

/-! ## A chain with no limit -/

/-- The keys and queue of any chain that started at keys `R` and queue `Q`. Either the chain
is still on the queue, with no condition on the later deposits, or it has consumed all of `Q`
and its keys extend the keys of the whole queue. -/
def Tracks (R : List κ) (Q : List δ) (K : List κ) (q : List δ) : Prop :=
  OnQueue key valid R Q (fun _ => True) K q ∨ keysAfter key valid R Q <+: K

theorem Tracks.start (R : List κ) (Q : List δ) : Tracks key valid R Q R Q :=
  Or.inl (OnQueue.start key valid R Q _)

theorem Tracks.append {R : List κ} {Q : List δ} {K : List κ} {q : List δ}
    (h : Tracks key valid R Q K q) (X' : List δ) : Tracks key valid R Q K (q ++ X') := by
  rcases h with h | h
  · exact Or.inl (h.append key valid fun _ _ => Or.inr trivial)
  · exact Or.inr h

/-- Any scan keeps `Tracks`. While the scan stays inside `Q` the chain stays on the queue.
Once it passes the end of `Q`, the keys extend the keys of the whole queue. -/
theorem Tracks.scan {R : List κ} {Q : List δ} {fin : δ → Prop} {K K' : List κ} {q q' : List δ}
    (h : Tracks key valid R Q K q) (hs : Scan key valid fin K K' q q') :
    Tracks key valid R Q K' q' := by
  have hpre : K <+: K' := hs.prefix
  rcases h with h | h
  · obtain ⟨k, X, hq, hK, -⟩ := h
    obtain ⟨n, post, hK', hq', -, -⟩ := hs
    subst hq
    rw [List.take_append] at hK'
    rw [List.drop_append] at hq'
    by_cases hn : n ≤ (Q.drop k).length
    · have h0 : n - (Q.drop k).length = 0 := Nat.sub_eq_zero_of_le hn
      rw [h0, List.take_zero, List.append_nil] at hK'
      rw [h0, List.drop_zero] at hq'
      refine Or.inl ⟨k + n, X ++ post, ?_, ?_, fun _ _ => Or.inr trivial⟩
      · rw [hq', List.drop_drop, List.append_assoc]
      · rw [hK', List.take_add, keysAfter_append, ← hK]
    · have hall : (Q.drop k).take n = Q.drop k :=
        List.take_of_length_le (Nat.le_of_lt (Nat.lt_of_not_le hn))
      rw [hall, keysAfter_append] at hK'
      have hQ : keysAfter key valid R Q = keysAfter key valid K (Q.drop k) := by
        rw [hK, ← keysAfter_append, List.take_append_drop]
      refine Or.inr ?_
      rw [hK', hQ]
      exact prefix_keysAfter key valid _ _
  · exact Or.inr (h.trans hpre)

/-! ## Two chains from one start -/

/-- A chain on the queue and any other chain from the same start have comparable key lists:
one is a prefix of the other. -/
theorem comparable {R : List κ} {Q : List δ} {adm : δ → Prop} {K₁ K₂ : List κ} {q₁ q₂ : List δ}
    (h₁ : OnQueue key valid R Q adm K₁ q₁) (h₂ : Tracks key valid R Q K₂ q₂) :
    K₁ <+: K₂ ∨ K₂ <+: K₁ := by
  have p₁ := h₁.prefix_full
  rcases h₂ with h₂ | h₂
  · exact List.prefix_or_prefix_of_prefix p₁ h₂.prefix_full
  · exact Or.inl (p₁.trans h₂)

/-! ## A chain from the common state

`Chain` packs the two facts above for one state of a chain, with the three numbers the steps
read. The proof across the Gloas upgrade runs one induction per fork on it
(`Proofs/Gloas/IndexAssignmentFromFulu.lean`). -/

/-- The state of a chain that started at keys `R` and queue `Q`, at slot `d`. `slot` is the
state's slot, `fin` the first slot of its finalized epoch, `K` its keys and `q` its queue.
`slotOf` reads the slot a deposit carries.

* The chain has not gone back: `d ≤ slot`.
* While the chain has finalized no slot at or after `d`, it is on the queue `Q`. A deposit
  that joined later then names a held key, or carries a slot at or after `d`.
* The chain tracks `Q`, with no condition. -/
structure Chain (slotOf : δ → Nat) (R : List κ) (Q : List δ) (d fin slot : Nat) (K : List κ)
    (q : List δ) : Prop where
  slot_le : d ≤ slot
  onQueue : fin < d → OnQueue key valid R Q (fun e => d ≤ slotOf e) K q
  tracks : Tracks key valid R Q K q

/-- The common state itself. -/
theorem Chain.start (slotOf : δ → Nat) (R : List κ) (Q : List δ) (d fin : Nat) :
    Chain key valid slotOf R Q d fin d R Q :=
  ⟨Nat.le_refl _, fun _ => OnQueue.start key valid R Q _, Tracks.start key valid R Q⟩

/-- A scan keeps the chain. The finalized slot and the slot do not fall, and each consumed
deposit carries a slot at or below the new finalized slot. When that slot is below `d`, the
scan consumed no deposit of a block at or after `d`, so the chain stays on the queue. -/
theorem Chain.scan {slotOf : δ → Nat} {R : List κ} {Q : List δ} {d fin fin' slot slot' : Nat}
    {K K' : List κ} {q q' : List δ} {consumed : δ → Prop}
    (h : Chain key valid slotOf R Q d fin slot K q) (hs : Scan key valid consumed K K' q q')
    (hfin : fin ≤ fin') (hslot : slot ≤ slot') (hcons : ∀ e, consumed e → slotOf e ≤ fin') :
    Chain key valid slotOf R Q d fin' slot' K' q' :=
  ⟨Nat.le_trans h.slot_le hslot,
    fun hlt => (h.onQueue (Nat.lt_of_le_of_lt hfin hlt)).scan key valid hs fun e he hadm =>
      Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans hadm (hcons e he)) hlt),
    h.tracks.scan key valid hs⟩

/-- A block keeps the chain. It appends deposits to the queue, and each names a held key or
carries the slot of the block, which is the slot of the state. -/
theorem Chain.append {slotOf : δ → Nat} {R : List κ} {Q : List δ} {d fin slot : Nat}
    {K : List κ} {q : List δ} (h : Chain key valid slotOf R Q d fin slot K q) {X : List δ}
    (hX : ∀ e ∈ X, key e ∈ K ∨ slot ≤ slotOf e) :
    Chain key valid slotOf R Q d fin slot K (q ++ X) :=
  ⟨h.slot_le,
    fun hlt => (h.onQueue hlt).append key valid fun e he =>
      (hX e he).imp id (Nat.le_trans h.slot_le),
    h.tracks.append key valid X⟩

/-- Two chains that started at one key list and one queue have comparable key lists, when the
first has finalized no slot at or after its start slot. The two start slots may differ: the
second chain enters through `Tracks`, which reads no slot. -/
theorem Chain.comparable {slotOf : δ → Nat} {R : List κ} {Q : List δ}
    {d₁ d₂ fin₁ fin₂ slot₁ slot₂ : Nat} {K₁ K₂ : List κ} {q₁ q₂ : List δ}
    (h₁ : Chain key valid slotOf R Q d₁ fin₁ slot₁ K₁ q₁) (hfin : fin₁ < d₁)
    (h₂ : Chain key valid slotOf R Q d₂ fin₂ slot₂ K₂ q₂) : K₁ <+: K₂ ∨ K₂ <+: K₁ :=
  DepositQueue.comparable key valid (h₁.onQueue hfin) h₂.tracks

end

/-- Comparable lists agree at each index both have. -/
theorem getElem_eq_of_comparable {α : Type} {K₁ K₂ : List α} (h : K₁ <+: K₂ ∨ K₂ <+: K₁)
    (i : Nat) (h₁ : i < K₁.length) (h₂ : i < K₂.length) : K₁[i] = K₂[i] := by
  rcases h with h | h
  · exact h.getElem h₁
  · exact (h.getElem h₂).symm

end EthCLSpecs.Proofs.DepositQueue
