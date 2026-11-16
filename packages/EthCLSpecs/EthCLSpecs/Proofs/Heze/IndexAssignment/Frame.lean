import EthCLSpecs.Proofs.Heze.StateInvariants
import EthCLSpecs.Heze.Transition

/-!
# `EthCLSpecs.Proofs.Heze.IndexAssignment.Frame`: what a Heze step may do to the keys and the queue

The Heze counterpart of `Proofs/Gloas/IndexAssignment/Frame.lean`. `Proofs/Fulu/IndexAssignment/Frame.lean`
explains the frame, the in-block contexts, and the names the shared tactics read. The
definitions are the same, over the Heze `BeaconState`, whose registry lists are progressive
as in Gloas.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze.IndexAssignment

open EthCLLib.Proofs (Preserves)
open EthCLLib.Spec (HasherTag)
open EthCLSpecs.Heze (Preset BeaconState Slot Epoch BLSPubkey PendingDeposit Validator
  computeEpochAtSlot)
open EthCLSpecs.Heze.Const (farFutureEpoch)
open EthCLSpecs.Proofs.Heze (RegistrySizes)

/-- The public keys of the registry, in index order. Entry `i` is the key of validator `i`,
so the index assignment of a state is this array. -/
def registryKeys [Preset] (v : BeaconState) : Array BLSPubkey := v.validators.val.map (·.pubkey)

/-- The activation eligibility epochs of the registry, in index order. Entry `i` is the
`activation_eligibility_epoch` of validator `i`. -/
def registryElig [Preset] (v : BeaconState) : Array Epoch :=
  v.validators.val.map (·.activationEligibilityEpoch)

/-- What steps that start at slot `σ` may do to the eligibility epochs. Each entry of `new` is
the entry of `old` at its index, or `FAR_FUTURE_EPOCH`, or the epoch after the epoch of `σ`.
A new validator starts at `FAR_FUTURE_EPOCH` (`get_validator_from_deposit`), and
`process_registry_updates` writes `current_epoch + 1`.

`old[j]? = some new[j]` reads "index `j` is in `old`, with the same value" in one equation. -/
def EligStep [Preset] (σ : Slot) (old new : Array Epoch) : Prop :=
  ∀ (j : Nat) (h : j < new.size),
    old[j]? = some new[j] ∨ new[j] = farFutureEpoch ∨ new[j] = computeEpochAtSlot σ + 1

theorem EligStep.refl [Preset] (σ : Slot) (a : Array Epoch) : EligStep σ a a :=
  fun _ h => Or.inl (Array.getElem?_eq_getElem h)

theorem EligStep.of_eq [Preset] {σ : Slot} {a b : Array Epoch} (h : b = a) : EligStep σ a b :=
  h ▸ EligStep.refl σ a

/-- Two runs of steps at one slot compose. An entry the second run kept has the status the
first run gave it. -/
theorem EligStep.trans [Preset] {σ : Slot} {a b c : Array Epoch} (h₁ : EligStep σ a b)
    (h₂ : EligStep σ b c) : EligStep σ a c := by
  intro j hj
  rcases h₂ j hj with h | h | h
  · obtain ⟨hjb, hbc⟩ := Array.getElem?_eq_some_iff.mp h
    rcases h₁ j hjb with h' | h' | h'
    · exact Or.inl (by rw [h', hbc])
    · exact Or.inr (Or.inl (by rw [← hbc, h']))
    · exact Or.inr (Or.inr (by rw [← hbc, h']))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The write of `process_registry_updates`: one entry becomes the epoch after the epoch of
`σ`. Out of range the write does nothing. -/
theorem EligStep.set [Preset] {σ : Slot} {a b : Array Epoch} (h : EligStep σ a b) (i : Nat) :
    EligStep σ a (b.setIfInBounds i (computeEpochAtSlot σ + 1)) := by
  intro j hj
  have hjb : j < b.size := by simpa using hj
  rw [Array.getElem_setIfInBounds hjb]
  split
  · exact Or.inr (Or.inr rfl)
  · exact h j hjb

/-- New validators: entries appended at `FAR_FUTURE_EPOCH`. -/
theorem EligStep.append [Preset] {σ : Slot} {a b : Array Epoch} (h : EligStep σ a b)
    (extra : Array Epoch) (hx : ∀ e ∈ extra, e = farFutureEpoch) : EligStep σ a (b ++ extra) := by
  intro j hj
  by_cases hjb : j < b.size
  · rw [Array.getElem_append_left hjb]
    exact h j hjb
  · rw [Array.getElem_append_right (Nat.le_of_not_lt hjb)]
    exact Or.inr (Or.inl (hx _ (Array.getElem_mem _)))

/-- What the registry append does to the eligibility epochs: `new` is `old`, then one
`FAR_FUTURE_EPOCH` per new validator. The queue scan gives this relation, at any slot. -/
def EligExt [Preset] (old new : Array Epoch) : Prop :=
  ∃ extra : Array Epoch, new = old ++ extra ∧ ∀ e ∈ extra, e = farFutureEpoch

theorem EligExt.refl [Preset] (a : Array Epoch) : EligExt a a := ⟨#[], by simp, by simp⟩

theorem EligExt.of_eq [Preset] {a b : Array Epoch} (h : b = a) : EligExt a b :=
  h ▸ EligExt.refl a

theorem EligExt.trans [Preset] {a b c : Array Epoch} (h₁ : EligExt a b) (h₂ : EligExt b c) :
    EligExt a c := by
  obtain ⟨x, rfl, hx⟩ := h₁
  obtain ⟨y, rfl, hy⟩ := h₂
  refine ⟨x ++ y, by simp, fun e he => ?_⟩
  rcases Array.mem_append.mp he with h | h
  · exact hx e h
  · exact hy e h

/-- One new validator. -/
theorem EligExt.push [Preset] (a : Array Epoch) : EligExt a (a.push farFutureEpoch) :=
  ⟨#[farFutureEpoch], by simp, by simp⟩

/-- An extension is a step at every slot. -/
theorem EligExt.eligStep [Preset] {a b : Array Epoch} (h : EligExt a b) (σ : Slot) :
    EligStep σ a b := by
  obtain ⟨x, rfl, hx⟩ := h
  exact (EligStep.refl σ a).append x hx

/-- The three values a frame step keeps as they are: the slot, the finalized epoch, and the
pending-deposit queue. -/
structure CoreFields [Preset] where
  slot : Slot
  finalizedEpoch : Epoch
  queue : Array PendingDeposit

/-- Project a state onto the three values `CoreFields` holds. -/
def coreFields [Preset] (v : BeaconState) : CoreFields where
  slot := v.slot
  finalizedEpoch := v.finalizedCheckpoint.epoch
  queue := v.pendingDeposits.val

/-- The key list, the eligibility epochs, and the sizes of the four lists that run parallel to
`validators`. The name is the one the shared `frame_eq` tactic unfolds. The first two
components are `registryKeys v` and `registryElig v`, written out so that `simp` reaches each
`Array.map`. -/
def listSizes [Preset] (v : BeaconState) :
    Array BLSPubkey × Array Epoch × Nat × Nat × Nat × Nat :=
  (v.validators.val.map (·.pubkey), v.validators.val.map (·.activationEligibilityEpoch),
    v.balances.size, v.inactivityScores.size,
    v.previousEpochParticipation.size, v.currentEpochParticipation.size)

/-- `w` agrees with `v` on the three core values, on the key list, on the eligibility epochs,
and on the four list sizes. A record update that writes other fields, or overwrites a
validator record without its `pubkey` and its `activationEligibilityEpoch`, gives such a
pair. -/
def FrameEq [Preset] (w v : BeaconState) : Prop :=
  coreFields w = coreFields v ∧ listSizes w = listSizes v

theorem FrameEq.refl [Preset] (v : BeaconState) : FrameEq v v := ⟨rfl, rfl⟩

/-- What a step is measured against: the slot, finalized epoch, keys, eligibility epochs and
queue where it starts, and whether it runs inside a block. -/
structure Ctx [Preset] where
  slot : Slot
  finalizedEpoch : Epoch
  keys : Array BLSPubkey
  elig : Array Epoch
  queue : Array PendingDeposit
  inBlock : Bool

/-- The context of a step that starts at `v`. -/
def Ctx.of [Preset] (v : BeaconState) (inBlock : Bool) : Ctx where
  slot := v.slot
  finalizedEpoch := v.finalizedCheckpoint.epoch
  keys := registryKeys v
  elig := registryElig v
  queue := v.pendingDeposits.val
  inBlock := inBlock

/-- A deposit a step may append to the queue. Only a step inside a block appends. The
deposit then names a key the registry holds, or it carries the block's slot. -/
def Admitted [Preset] (c : Ctx) (e : PendingDeposit) : Prop :=
  c.inBlock = true ∧ (e.pubkey ∈ c.keys ∨ e.slot = c.slot)

/-- The step invariant at the context `c`. The slot, the finalized epoch and the keys are the
context's. The queue is the context's queue followed by admitted deposits. The registry sizes
agree, which the registry append needs to take its append branch on all five lists. The
eligibility epochs are the context's, up to `EligStep` at the context's slot. -/
def StepInv [Preset] (c : Ctx) (v : BeaconState) : Prop :=
  v.slot = c.slot ∧ v.finalizedCheckpoint.epoch = c.finalizedEpoch ∧ registryKeys v = c.keys ∧
  (∃ extra : Array PendingDeposit,
    v.pendingDeposits.val = c.queue ++ extra ∧ ∀ e ∈ extra, Admitted c e) ∧
  RegistrySizes v ∧ EligStep c.slot c.elig (registryElig v)

/-- The registry-size part of the invariant. -/
theorem StepInv.registrySizes [Preset] {c : Ctx} {v : BeaconState} (hv : StepInv c v) :
    RegistrySizes v := hv.2.2.2.2.1

/-- The eligibility part of the invariant. -/
theorem StepInv.elig [Preset] {c : Ctx} {v : BeaconState} (hv : StepInv c v) :
    EligStep c.slot c.elig (registryElig v) := hv.2.2.2.2.2

/-- A state satisfies the invariant at its own context, with nothing appended. -/
theorem StepInv.start [Preset] (v : BeaconState) (inBlock : Bool) (hr : RegistrySizes v) :
    StepInv (Ctx.of v inBlock) v :=
  ⟨rfl, rfl, rfl, ⟨#[], by simp [Ctx.of], by simp⟩, hr, EligStep.refl _ _⟩

/-- An equal key list and equal list sizes carry the registry-size equalities. The registry's
own size is the size of the key list. The eligibility epochs play no part, so the lemma reads
the first component of `listSizes` and its last four. -/
theorem registrySizes_of_keys_sizes [Preset] {v w : BeaconState}
    (hk : (listSizes w).1 = (listSizes v).1) (hsz : (listSizes w).2.2 = (listSizes v).2.2)
    (hv : RegistrySizes v) : RegistrySizes w := by
  obtain ⟨hb, hi, hp, hq⟩ := hv
  simp only [listSizes, Prod.mk.injEq] at hk hsz
  obtain ⟨sb, si, sp, sq⟩ := hsz
  have sv : w.validators.size = v.validators.size := by
    have := congrArg Array.size hk
    simpa [SizzLean.Repr.ProgressiveList.size] using this
  exact ⟨by rw [sb, sv]; exact hb, by rw [si, sv]; exact hi, by rw [sp, sv]; exact hp,
    by rw [sq, sv]; exact hq⟩

/-- Equal `listSizes` carry the registry-size equalities. -/
theorem registrySizes_of_listSizes [Preset] {v w : BeaconState} (h : listSizes w = listSizes v)
    (hv : RegistrySizes v) : RegistrySizes w :=
  registrySizes_of_keys_sizes (congrArg (·.1) h) (congrArg (·.2.2) h) hv

/-- Equal `listSizes` carry the eligibility epochs: they are the second component. -/
theorem registryElig_of_listSizes [Preset] {v w : BeaconState} (h : listSizes w = listSizes v) :
    registryElig w = registryElig v := congrArg (·.2.1) h

/-- A state that agrees with a `StepInv` state under `FrameEq` satisfies `StepInv` too. The
leaf of most frame proofs, and the lemma `frame_leaf` applies. -/
theorem StepInv.of_frameEq [Preset] {c : Ctx} {v w : BeaconState} (hv : StepInv c v)
    (h : FrameEq w v) : StepInv c w := by
  obtain ⟨hs, hf, hk, ⟨extra, hq, hadm⟩, hr, he⟩ := hv
  obtain ⟨hcore, hsizes⟩ := h
  simp only [coreFields, CoreFields.mk.injEq] at hcore
  obtain ⟨e1, e2, e3⟩ := hcore
  have hkeys : registryKeys w = registryKeys v := congrArg Prod.fst hsizes
  exact ⟨e1.trans hs, e2.trans hf, hkeys.trans hk, ⟨extra, e3.trans hq, hadm⟩,
    registrySizes_of_listSizes hsizes hr, registryElig_of_listSizes hsizes ▸ he⟩

/-- `StepInv` from its parts, for a leaf that rebuilds a list: the core values, the keys and
the eligibility epochs agree with a `StepInv` state, and the registry sizes are proved
apart. -/
theorem StepInv.of_parts [Preset] {c : Ctx} {v w : BeaconState} (hv : StepInv c v)
    (hc : coreFields w = coreFields v) (hk : registryKeys w = registryKeys v)
    (he : registryElig w = registryElig v) (hr : RegistrySizes w) : StepInv c w := by
  obtain ⟨hs, hf, hk', ⟨extra, hq, hadm⟩, -, he'⟩ := hv
  simp only [coreFields, CoreFields.mk.injEq] at hc
  obtain ⟨e1, e2, e3⟩ := hc
  exact ⟨e1.trans hs, e2.trans hf, hk.trans hk', ⟨extra, e3.trans hq, hadm⟩, hr, he ▸ he'⟩

/-- The leaf of the eligibility write of `process_registry_updates`. `w` has the core values,
the keys and the list sizes of a `StepInv` state `v`, and its eligibility epochs are those of
`v` with entry `i` set to `e`, the epoch after the context's. The hypotheses read the
components of `listSizes`, so `simp` proves each as it proves a `frame_eq` leaf. -/
theorem StepInv.of_eligWrite [Preset] {c : Ctx} {v w : BeaconState} (hv : StepInv c v)
    (hc : coreFields w = coreFields v) (hk : (listSizes w).1 = (listSizes v).1)
    (hsz : (listSizes w).2.2 = (listSizes v).2.2) (i : Nat) (e : Epoch)
    (hE : e = computeEpochAtSlot c.slot + 1)
    (he : (listSizes w).2.1 = ((listSizes v).2.1).setIfInBounds i e) : StepInv c w := by
  obtain ⟨hs, hf, hk', ⟨extra, hq, hadm⟩, hr, he'⟩ := hv
  simp only [coreFields, CoreFields.mk.injEq] at hc
  obtain ⟨e1, e2, e3⟩ := hc
  have hel : registryElig w = (registryElig v).setIfInBounds i (computeEpochAtSlot c.slot + 1) :=
    hE ▸ he
  exact ⟨e1.trans hs, e2.trans hf, Eq.trans hk hk', ⟨extra, e3.trans hq, hadm⟩,
    registrySizes_of_keys_sizes hk hsz hr, hel ▸ he'.set i⟩

/-- Outside a block the queue is the context's queue: the context admits no deposit, so the
appended part is empty. -/
theorem StepInv.queue_eq [Preset] {c : Ctx} {v : BeaconState} (hv : StepInv c v)
    (hc : c.inBlock = false) : v.pendingDeposits.val = c.queue := by
  obtain ⟨-, -, -, ⟨extra, hq, hadm⟩, -⟩ := hv
  have hnil : extra = #[] := by
    apply Array.eq_empty_of_size_eq_zero
    apply Nat.eq_zero_of_not_pos
    intro hpos
    have := (hadm extra[0] (Array.getElem_mem hpos)).1
    rw [hc] at this
    exact Bool.false_ne_true this
  rw [hq, hnil, Array.append_empty]

/-- The leaf of a step that appends one admitted deposit `e` to the queue and keeps the rest
of the frame. -/
theorem StepInv.of_push [Preset] {c : Ctx} {v w : BeaconState} (hv : StepInv c v)
    (e : PendingDeposit) (hs : w.slot = v.slot)
    (hf : w.finalizedCheckpoint.epoch = v.finalizedCheckpoint.epoch)
    (hk : listSizes w = listSizes v)
    (hq : w.pendingDeposits.val = v.pendingDeposits.val.push e) (he : Admitted c e) :
    StepInv c w := by
  obtain ⟨hs', hf', hk', ⟨extra, hq', hadm⟩, hr, hel⟩ := hv
  have hkeys : registryKeys w = registryKeys v := congrArg Prod.fst hk
  refine ⟨hs.trans hs', hf.trans hf', hkeys.trans hk', ⟨extra.push e, ?_, ?_⟩,
    registrySizes_of_listSizes hk hr, registryElig_of_listSizes hk ▸ hel⟩
  · rw [hq, hq', Array.push_append]
  · intro x hx
    rcases Array.mem_push.mp hx with h | h
    · exact hadm x h
    · exact h ▸ he

/-- A run of `act` keeps the frame at every context. The property of a step that appends no
deposit and no validator. -/
abbrev KeepsFrame [Preset] [HasherTag] {α : Type} (act : HezeRun α) : Prop :=
  ∀ c, Preserves (StepInv c) act

/-- A run of `act` keeps the frame at every in-block context. The property of a step that
appends admitted deposits, which only a block does. -/
abbrev KeepsFrameInBlock [Preset] [HasherTag] {α : Type} (act : HezeRun α) : Prop :=
  ∀ c : Ctx, c.inBlock = true → Preserves (StepInv c) act

theorem KeepsFrame.inBlock [Preset] [HasherTag] {α : Type} {act : HezeRun α}
    (h : KeepsFrame act) : KeepsFrameInBlock act := fun c _ => h c

/-! ## The key list and the eligibility epochs under a validator record write

`modValidator` overwrites entry `i` of `validators` with a record built from the old entry.
The lemmas below close the key-list goal that leaves, when the new key is the old one, and
the same goal for the eligibility epochs. -/

/-- Setting entry `i` of the key list to the key of entry `i` changes nothing. In range the
two agree, and out of range the write is a no-op. -/
@[simp] theorem keys_setIfInBounds_self [Preset]
    (xs : SizzLean.Repr.ProgressiveList Validator) (i : Nat) :
    (Array.map (fun x : Validator => x.pubkey) xs.val).setIfInBounds i (xs[i]!).pubkey
      = Array.map (fun x : Validator => x.pubkey) xs.val := by
  by_cases h : i < xs.val.size
  · apply Array.ext
    · simp
    · intro j h1 h2
      rw [Array.getElem_setIfInBounds]
      split
      · next hij =>
        subst hij
        -- `getElem!_pos` swaps the total read for the proof-carrying one, at the list's
        -- validity predicate `i < xs.size`.
        rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.ProgressiveList Validator) i => i < xs.size)
          (h := h)]
        simp
        rfl
      · rfl
  · exact Array.setIfInBounds_eq_of_size_le (by simpa using Nat.le_of_not_lt h)

/-- A second write at one index reads the first write back. When the first write kept the
key, the read-back has the original key. -/
@[simp] theorem set!_getElem!_pubkey [Preset]
    (xs : SizzLean.Repr.ProgressiveList Validator) (i : Nat) (x : Validator)
    (h : x.pubkey = (xs[i]!).pubkey) : ((xs.set! i x)[i]!).pubkey = (xs[i]!).pubkey := by
  by_cases hi : i < xs.size
  · rw [SizzLean.Proofs.progressiveListSet!_getElem!_self xs i x hi, h]
  · rw [SizzLean.Proofs.progressiveListSet!_eq_of_size_le xs i x (Nat.le_of_not_lt hi)]

/-- Setting entry `i` of the eligibility epochs to the epoch of entry `i` changes nothing. The
twin of `keys_setIfInBounds_self`. -/
@[simp] theorem elig_setIfInBounds_self [Preset]
    (xs : SizzLean.Repr.ProgressiveList Validator) (i : Nat) :
    (Array.map (fun x : Validator => x.activationEligibilityEpoch) xs.val).setIfInBounds i
        (xs[i]!).activationEligibilityEpoch
      = Array.map (fun x : Validator => x.activationEligibilityEpoch) xs.val := by
  by_cases h : i < xs.val.size
  · apply Array.ext
    · simp
    · intro j h1 h2
      rw [Array.getElem_setIfInBounds]
      split
      · next hij =>
        subst hij
        rw [getElem!_pos (dom := fun (xs : SizzLean.Repr.ProgressiveList Validator) i => i < xs.size)
          (h := h)]
        simp
        rfl
      · rfl
  · exact Array.setIfInBounds_eq_of_size_le (by simpa using Nat.le_of_not_lt h)

/-- A second write at one index reads the first write back. When the first write kept the
eligibility epoch, the read-back has the original one. The twin of `set!_getElem!_pubkey`. -/
@[simp] theorem set!_getElem!_elig [Preset]
    (xs : SizzLean.Repr.ProgressiveList Validator) (i : Nat) (x : Validator)
    (h : x.activationEligibilityEpoch = (xs[i]!).activationEligibilityEpoch) :
    ((xs.set! i x)[i]!).activationEligibilityEpoch = (xs[i]!).activationEligibilityEpoch := by
  by_cases hi : i < xs.size
  · rw [SizzLean.Proofs.progressiveListSet!_getElem!_self xs i x hi, h]
  · rw [SizzLean.Proofs.progressiveListSet!_eq_of_size_le xs i x (Nat.le_of_not_lt hi)]

/-- A second write at one index, after a first write that changed the eligibility epoch: the
read-back is the first write's record in range, and out of range neither write happens. So
setting entry `i` to the read-back's epoch sets it to the first record's epoch. -/
@[simp] theorem elig_setIfInBounds_set!_getElem! [Preset]
    (xs : SizzLean.Repr.ProgressiveList Validator) (i : Nat) (x : Validator) :
    (Array.map (fun x : Validator => x.activationEligibilityEpoch) xs.val).setIfInBounds i
        ((xs.set! i x)[i]!).activationEligibilityEpoch
      = (Array.map (fun x : Validator => x.activationEligibilityEpoch) xs.val).setIfInBounds i
          x.activationEligibilityEpoch := by
  by_cases hi : i < xs.size
  · rw [SizzLean.Proofs.progressiveListSet!_getElem!_self xs i x hi]
  · have hle : (Array.map (fun x : Validator => x.activationEligibilityEpoch) xs.val).size ≤ i := by
      simpa [SizzLean.Repr.ProgressiveList.size] using Nat.le_of_not_lt hi
    rw [Array.setIfInBounds_eq_of_size_le hle, Array.setIfInBounds_eq_of_size_le hle]

/-- The key list under a record write in the folded shape `(xs.set! i x).val`: the write keeps
the key list when the new record has the old key. `simp` discharges `h` by the projection of
the record literal. -/
@[simp] theorem keys_set! [Preset] (xs : SizzLean.Repr.ProgressiveList Validator) (i : Nat)
    (x : Validator) (h : x.pubkey = (xs[i]!).pubkey) :
    Array.map (fun x : Validator => x.pubkey) (xs.set! i x).val
      = Array.map (fun x : Validator => x.pubkey) xs.val := by
  have hset : (xs.set! i x).val = xs.val.setIfInBounds i x := rfl
  rw [hset]
  simp only [Array.map_setIfInBounds, h]
  exact keys_setIfInBounds_self xs i

/-- The eligibility epochs under a record write in the folded shape: entry `i` takes the new
record's epoch. The proof of `processRegistryUpdates_keepsFrame` passes this lemma to `simp`
for the write that changes the epoch. -/
theorem elig_set!_eq [Preset] (xs : SizzLean.Repr.ProgressiveList Validator) (i : Nat)
    (x : Validator) :
    Array.map (fun x : Validator => x.activationEligibilityEpoch) (xs.set! i x).val
      = (Array.map (fun x : Validator => x.activationEligibilityEpoch) xs.val).setIfInBounds i
          x.activationEligibilityEpoch := by
  have hset : (xs.set! i x).val = xs.val.setIfInBounds i x := rfl
  rw [hset, Array.map_setIfInBounds]

/-- The eligibility epochs under a record write in the folded shape, when the new record has
the old epoch. The twin of `keys_set!`. -/
@[simp] theorem elig_set! [Preset] (xs : SizzLean.Repr.ProgressiveList Validator) (i : Nat)
    (x : Validator) (h : x.activationEligibilityEpoch = (xs[i]!).activationEligibilityEpoch) :
    Array.map (fun x : Validator => x.activationEligibilityEpoch) (xs.set! i x).val
      = Array.map (fun x : Validator => x.activationEligibilityEpoch) xs.val := by
  rw [elig_set!_eq, h]
  exact elig_setIfInBounds_self xs i

/-- A validator that `sszGetIdx` read from the registry has its key in the key list. -/
theorem mem_keys_of_get? [Preset] {xs : SizzLean.Repr.ProgressiveList Validator}
    {i : Nat} {x : Validator} (h : EthCLLib.Spec.IdxRead.get? xs i = some x) :
    x.pubkey ∈ Array.map (fun x : Validator => x.pubkey) xs.val := by
  -- `IdxRead.get?` on a `ProgressiveList` is `xs.val[i]?`, by its reducible instance.
  have hx : xs.val[i]? = some x := h
  exact Array.mem_map.mpr ⟨x, Array.mem_of_getElem? hx, rfl⟩

end EthCLSpecs.Proofs.Heze.IndexAssignment
