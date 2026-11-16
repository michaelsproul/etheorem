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

end

/-- Comparable lists agree at each index both have. -/
theorem getElem_eq_of_comparable {α : Type} {K₁ K₂ : List α} (h : K₁ <+: K₂ ∨ K₂ <+: K₁)
    (i : Nat) (h₁ : i < K₁.length) (h₂ : i < K₂.length) : K₁[i] = K₂[i] := by
  rcases h with h | h
  · exact h.getElem h₁
  · exact (h.getElem h₂).symm

end EthCLSpecs.Proofs.DepositQueue
