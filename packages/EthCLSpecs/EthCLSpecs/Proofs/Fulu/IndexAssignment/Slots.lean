import EthCLSpecs.Proofs.Fulu.IndexAssignment.Epoch
import EthCLSpecs.Proofs.Fulu.IndexAssignment.Deposits
import EthCLSpecs.Proofs.Fulu.Invariants.Slots

/-!
# `EthCLSpecs.Proofs.Fulu.IndexAssignment.Slots`: what a run of slots does to the keys and the queue

`processSlots` (`Fulu/Transition.lean:72-77`) runs `processSlot`, then `processEpoch` at the
last slot of an epoch, then the slot increment, once per slot. This module states the effect
of one iteration on the keys and the queue as one relation, `DepositProgress`. `SlotProgress`
adds what the iteration did to the eligibility epochs, and the slot count. The module carries
any predicate that one `SlotProgress` step keeps through the loop.

## One epoch

`processEpoch_progress` joins three facts.

* Justification keeps the keys and the queue, and the finalized epoch does not fall
  (`processJustificationAndFinalization_frame`). The new finalized epoch is the old one, or
  one of the two old justified epochs, and `SimpleStateInvariants` orders all three.
* The thirteen frame substeps keep the keys, the queue and the finalized epoch
  (`SameDeposits`).
* `processPendingDeposits` is one `Scan`. It reads the finalized checkpoint after
  justification, which is the checkpoint the epoch ends with.

So an epoch is one `Scan` whose consumed deposits have a slot at or below the finalized slot
of the end state.

The slot stays through the epoch. The frame substeps move the eligibility epochs by `EligStep`
at that slot, and the scan extends them (`EligExt`). So an epoch is also one `EligStep`.

## The loop

`processSlots_progress` takes a predicate `P` and a proof that one `SlotProgress` step keeps
it, between two states that satisfy `SimpleStateInvariants`. The loop is the one
`processSlots_ensures` walks, with `P` added to its invariant. An iteration off an epoch
boundary keeps the keys, the queue and the finalized epoch, which is a `DepositProgress` that
consumes nothing.

The caller picks `P`. The index-assignment theorem uses two, one per chain, and the
finalized-validator theorem uses `Follows` (`Proofs/Fulu/FinalizedValidators.lean`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu.IndexAssignment

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub)
open EthCLSpecs.Fulu
open EthCLSpecs.Fulu.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt)
open EthCLSpecs.Proofs.DepositQueue

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## Justification and finalization -/

/-- Step over a read-only call with any postcondition: the state after it is the state before
it. -/
local macro "call_reads " h:term : tactic =>
  `(tactic| (refine EthCLLib.Proofs.RunEnsures.weaken ($h _) (fun _ _ hro => ?_); subst hro))

set_option maxHeartbeats 4000000 in
omit [Config] [CryptoBackend] in
/-- The weighing step writes the checkpoints and the justification bits. It keeps the slot,
the queue and `listSizes`, and the finalized epoch does not fall. The step sets the finalized
checkpoint to the old one, the old previous-justified one, or the old current-justified one,
and `hv` puts the old finalized epoch below both. The walk is the one of
`Proofs/Fulu/Invariants/Justification.lean`. -/
theorem weighJustificationAndFinalization_frame (total prevT currT : Gwei) (v : BeaconState)
    (hv : CheckpointsBelowPrevious v) :
    RunEnsures v (weighJustificationAndFinalization (StateTransition := FuluRun) total prevT currT)
      (fun _ w => w.slot = v.slot ∧ w.pendingDeposits = v.pendingDeposits ∧
        listSizes w = listSizes v ∧
        v.finalizedCheckpoint.epoch ≤ w.finalizedCheckpoint.epoch) := by
  unfold weighJustificationAndFinalization
  run_ensures
  all_goals try (call_reads getBlockRoot_readsOnly _ _; run_ensures)
  all_goals try (call_reads getBlockRoot_readsOnly _ _; run_ensures)
  all_goals refine runEnsures_modifyThe_view ?_ ?_
  all_goals simp only [box_reduce, Id.run, *]
  all_goals repeat' split_ite
  all_goals first
    | rfl
    | exact ⟨rfl, rfl, rfl, by
        first
          | exact UInt64.le_refl _
          | exact hv.1
          | exact UInt64.le_trans hv.1 hv.2.1⟩

omit [Config] [CryptoBackend] in
/-- Justification and finalization keeps the slot, the queue and `listSizes`, and the finalized
epoch does not fall. In the first two epochs the step does nothing. -/
theorem processJustificationAndFinalization_frame (v : BeaconState)
    (hv : CheckpointsBelowPrevious v) :
    RunEnsures v (processJustificationAndFinalization (StateTransition := FuluRun))
      (fun _ w => w.slot = v.slot ∧ w.pendingDeposits = v.pendingDeposits ∧
        listSizes w = listSizes v ∧
        v.finalizedCheckpoint.epoch ≤ w.finalizedCheckpoint.epoch) := by
  unfold processJustificationAndFinalization
  run_ensures
  · exact ⟨trivial, trivial, trivial, UInt64.le_refl _⟩
  · exact weighJustificationAndFinalization_frame _ _ _ v hv

/-! ## What one epoch, and any run of slots, does to the keys and the queue -/

/-- The slot the queue scan compares a deposit's slot with: the first slot of the finalized
epoch. -/
def finalizedSlot (v : BeaconState) : Slot := computeStartSlotAtEpoch v.finalizedCheckpoint.epoch

/-- `y` has the keys, the queue and the finalized epoch of `x`. -/
def SameDeposits (x y : BeaconState) : Prop :=
  registryKeys y = registryKeys x ∧ y.pendingDeposits.val = x.pendingDeposits.val ∧
  y.finalizedCheckpoint.epoch = x.finalizedCheckpoint.epoch

omit [HasherTag] [Config] [CryptoBackend] in
theorem SameDeposits.refl (x : BeaconState) : SameDeposits x x := ⟨rfl, rfl, rfl⟩

omit [HasherTag] [Config] [CryptoBackend] in
theorem SameDeposits.trans {x y z : BeaconState} (h₁ : SameDeposits x y) (h₂ : SameDeposits y z) :
    SameDeposits x z :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

omit [HasherTag] [Config] [CryptoBackend] in
/-- A frame step outside a block keeps the keys, the queue and the finalized epoch. -/
theorem StepInv.sameDeposits {x y : BeaconState} (h : StepInv (Ctx.of x false) y) :
    SameDeposits x y :=
  ⟨h.2.2.1, h.queue_eq rfl, h.2.1⟩

/-- The effect of a run of slots on the keys and the queue, from `v` to `w`: the finalized
epoch does not fall, and the queue scan consumed deposits whose slots are finalized at `w`. -/
def DepositProgress (v w : BeaconState) : Prop :=
  v.finalizedCheckpoint.epoch ≤ w.finalizedCheckpoint.epoch ∧
  Scan (fun e : PendingDeposit => e.pubkey) depositValid (fun e => e.slot ≤ finalizedSlot w)
    (registryKeys v).toList (registryKeys w).toList
    v.pendingDeposits.val.toList w.pendingDeposits.val.toList

/-- A step that keeps the keys, the queue and the finalized epoch is progress that consumes
nothing. -/
theorem DepositProgress.of_same {x y : BeaconState} (h : SameDeposits x y) :
    DepositProgress x y := by
  obtain ⟨hk, hq, hf⟩ := h
  refine ⟨by rw [hf]; exact UInt64.le_refl _, ?_⟩
  rw [hk, hq]
  exact Scan.refl _ _ _ _ _

/-- Progress read from an earlier state with the same keys, queue and finalized epoch. -/
theorem DepositProgress.same_left {x x' z : BeaconState} (h : SameDeposits x x')
    (hp : DepositProgress x' z) : DepositProgress x z := by
  obtain ⟨hk, hq, hf⟩ := h
  obtain ⟨hfin, hscan⟩ := hp
  rw [hk, hq] at hscan
  exact ⟨hf ▸ hfin, hscan⟩

/-- Progress read up to a later state with the same keys, queue and finalized epoch. -/
theorem DepositProgress.same_right {x z z' : BeaconState} (hp : DepositProgress x z)
    (h : SameDeposits z z') : DepositProgress x z' := by
  obtain ⟨hk, hq, hf⟩ := h
  obtain ⟨hfin, hscan⟩ := hp
  unfold DepositProgress finalizedSlot at *
  rw [hk, hq, hf]
  exact ⟨hfin, hscan⟩

omit [Config] [CryptoBackend] in
/-- `process_slot` caches roots and fills the header's state root. It keeps the frame. -/
theorem processSlot_keepsFrame : KeepsFrame (processSlot (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processSlot
  run_ensures
  frame_close

/-- One epoch transition is one `DepositProgress` step, and one `EligStep` at the slot it runs
at. The three intermediate states are `w1` after justification, `w2` before the queue scan and
`w3` after it. The frame substeps on each side of the scan give `SameDeposits`, and the scan
reads the finalized epoch of `w2`, which is the finalized epoch of the end state. The slot
stays through all four parts, so the four eligibility relations compose. -/
theorem processEpoch_progress (v : BeaconState) (hv : SimpleStateInvariants v) :
    RunEnsures v (processEpoch (StateTransition := FuluRun))
      (fun _ w => DepositProgress v w ∧ EligStep v.slot (registryElig v) (registryElig w)) := by
  unfold processEpoch
  run_ensures
  refine (processJustificationAndFinalization_frame v hv.checkpointOrder).weaken
    fun _ w1 h1 => ?_
  obtain ⟨hs1, hq1, hl1, hfin1⟩ := h1
  have hr1 : RegistrySizes w1 := registrySizes_of_listSizes hl1 hv.registrySizes
  have hk1 : registryKeys w1 = registryKeys v := congrArg Prod.fst hl1
  have _hst : StepInv (Ctx.of w1 false) w1 := StepInv.start w1 false hr1
  run_ensures
  call processInactivityUpdates_keepsFrame
  run_ensures
  call processRewardsAndPenalties_keepsFrame
  run_ensures
  call processRegistryUpdates_keepsFrame
  run_ensures
  call processSlashings_keepsFrame
  run_ensures
  call processEth1DataReset_keepsFrame
  run_ensures
  rename_i w2 hw2
  have hs2 : SameDeposits w1 w2 := hw2.sameDeposits
  refine (processPendingDeposits_ensures w2 hw2.registrySizes).weaken fun _ w3 h3 => ?_
  obtain ⟨hs3, hf3, hr3, hscan, he3⟩ := h3
  have _hst3 : StepInv (Ctx.of w3 false) w3 := StepInv.start w3 false hr3
  run_ensures
  call processPendingConsolidations_keepsFrame
  run_ensures
  call processEffectiveBalanceUpdates_keepsFrame
  run_ensures
  call processSlashingsReset_keepsFrame
  run_ensures
  call processRandaoMixesReset_keepsFrame
  run_ensures
  call processHistoricalSummariesUpdate_keepsFrame
  run_ensures
  call processParticipationFlagUpdates_keepsFrame
  run_ensures
  call processSyncCommitteeUpdates_keepsFrame
  run_ensures
  call processProposerLookahead_keepsFrame
  rename_i w hw
  have hs : SameDeposits w3 w := hw.sameDeposits
  have h23 : DepositProgress w2 w3 :=
    ⟨by rw [hf3]; exact UInt64.le_refl _, by unfold finalizedSlot; rw [hf3]; exact hscan⟩
  obtain ⟨hfin, hsc⟩ := (h23.same_left hs2).same_right hs
  have hq1' : w1.pendingDeposits.val = v.pendingDeposits.val := congrArg (·.val) hq1
  refine ⟨⟨UInt64.le_trans hfin1 hfin, ?_⟩, ?_⟩
  · rw [← hk1, ← hq1']
    exact hsc
  · -- The four parts: justification keeps the epochs, the frame steps before the scan give
    -- `EligStep` at the slot of `w1`, the scan extends, and the frame steps after it give
    -- `EligStep` at the slot of `w3`. Each of those slots is the slot of `v`.
    have h12 : EligStep w1.slot (registryElig w1) (registryElig w2) := hw2.elig
    have h34 : EligStep w3.slot (registryElig w3) (registryElig w) := hw.elig
    have hs2 : w2.slot = w1.slot := hw2.1
    rw [hs1, registryElig_of_listSizes hl1] at h12
    rw [hs3, hs2, hs1] at h34
    exact (h12.trans (he3.eligStep _)).trans h34

/-! ## `process_slots` -/

/-- One slot of progress, from `x` to `z`: what the slot did to the keys and the queue, what it
did to the eligibility epochs, and the slot count. -/
structure SlotProgress (x z : BeaconState) : Prop where
  deposits : DepositProgress x z
  elig : EligStep x.slot (registryElig x) (registryElig z)
  slot : z.slot.toNat = x.slot.toNat + 1

/-- `processSlots` carries any predicate that one slot of progress keeps. The loop is the one
`processSlots_ensures` walks, and the invariant adds `P` to it. An iteration off an epoch
boundary keeps the keys, the queue, the finalized epoch and the eligibility epochs. An
iteration at a boundary gives `processEpoch_progress`. -/
theorem processSlots_progress (P : BeaconState → Prop)
    (hstep : ∀ x z, SimpleStateInvariants x → SimpleStateInvariants z → SlotProgress x z →
      P x → P z)
    (target : Slot) (v : BeaconState) (hv : SimpleStateInvariants v) (hP : P v) :
    RunEnsures v (processSlots (StateTransition := FuluRun) target) (fun _ w => P w) := by
  unfold processSlots
  run_ensures
  rename_i hlt
  simp only [box_reduce] at hlt
  have hlt' : v.slot.toNat < target.toNat := UInt64.lt_iff_toNat_lt.mp hlt
  have hn : (target - v.slot).toNat = target.toNat - v.slot.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hlt)
  have hn' : (target - (pureState v).view.slot).toNat = target.toNat - v.slot.toNat := hn
  have htgt : target.toNat < 2 ^ 64 := target.toNat_lt
  refine runEnsures_forIn_range _
    (fun (i : Nat) (_ : PUnit) (w : BeaconState) =>
      w.slot.toNat = v.slot.toNat + i ∧ SimpleStateInvariants w ∧ P w) _ ?_ ?_ _ ⟨by simp, hv, hP⟩
  · intro i b w hi ⟨hw, hinv, hPw⟩
    refine runEnsures_bind (((processSlot_keepsCore (Fulu.coreFields w) w
      ⟨rfl, hinv.registrySizes⟩).and (processSlot_keepsFrame (Ctx.of w false) w
        (StepInv.start w false hinv.registrySizes))).weaken fun _ w1 h1 => ?_)
    obtain ⟨h1, hf1⟩ := h1
    have hsame1 : SameDeposits w w1 := hf1.sameDeposits
    have hel1 : EligStep w.slot (registryElig w) (registryElig w1) := hf1.elig
    have hinv1 := SimpleStateInvariants.of_coreFields_eq h1.1 h1.2 hinv
    have hs1 : w1.slot = w.slot := congrArg Fulu.CoreFields.slot h1.1
    have hno : w1.slot.toNat + 1 < 2 ^ 64 := by rw [hs1]; omega
    run_ensures
    · rename_i hb
      simp only [box_reduce, beq_iff_eq] at hb
      have hb' : (w1.slot.toNat + 1) % slotsPerEpoch = 0 := by
        have := congrArg UInt64.toNat hb
        rwa [UInt64.toNat_mod, slot_succ_toNat _ hno, UInt64.toNat_ofNat_of_lt' slotsPerEpochLt]
          at this
      refine ((processEpoch_ensures w1 hinv1).and (processEpoch_progress w1 hinv1)).weaken
        fun _ w2 h2 => ?_
      obtain ⟨⟨e1, e2, e3, e4, e5⟩, hprog⟩ := h2
      run_ensures
      show ({ w2 with slot := w2.slot + 1 } : BeaconState).slot.toNat = v.slot.toNat + (i + 1) ∧
        SimpleStateInvariants { w2 with slot := w2.slot + 1 } ∧ P { w2 with slot := w2.slot + 1 }
      have hno2 : w2.slot.toNat + 1 < 2 ^ 64 := by rw [e1]; exact hno
      have hinv2 : SimpleStateInvariants { w2 with slot := w2.slot + 1 } :=
        SimpleStateInvariants.succ_slot_boundary (by rw [e2, e1]; exact hinv1.headerSlotLe) e5 e4
          (by rw [e3, e1]; exact hinv1.forkConsistent) hno2 (by rw [e1]; exact hb')
      have hslot2 : (w2.slot + 1).toNat = w.slot.toNat + 1 := by
        rw [slot_succ_toNat _ hno2, e1, hs1]
      refine ⟨?_, hinv2, hstep w _ hinv hinv2 ⟨?_, ?_, hslot2⟩ hPw⟩
      · show (w2.slot + 1).toNat = _
        rw [hslot2, hw]; omega
      · exact (hprog.1.same_left hsame1).same_right ⟨rfl, rfl, rfl⟩
      · have h2 : EligStep w1.slot (registryElig w1) (registryElig w2) := hprog.2
        rw [hs1] at h2
        exact hel1.trans h2
    · rename_i hb
      simp only [box_reduce, beq_iff_eq] at hb
      have hb' : (w1.slot.toNat + 1) % slotsPerEpoch ≠ 0 := by
        intro h
        apply hb
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mod, slot_succ_toNat _ hno, UInt64.toNat_ofNat_of_lt' slotsPerEpochLt, h]
        rfl
      show ({ w1 with slot := w1.slot + 1 } : BeaconState).slot.toNat = v.slot.toNat + (i + 1) ∧
        SimpleStateInvariants { w1 with slot := w1.slot + 1 } ∧ P { w1 with slot := w1.slot + 1 }
      have hinv2 : SimpleStateInvariants { w1 with slot := w1.slot + 1 } := hinv1.succ_slot hno hb'
      have hslot1 : (w1.slot + 1).toNat = w.slot.toNat + 1 := by
        rw [slot_succ_toNat _ hno, hs1]
      refine ⟨?_, hinv2, hstep w _ hinv hinv2 ⟨?_, hel1, hslot1⟩ hPw⟩
      · show (w1.slot + 1).toNat = _
        rw [hslot1, hw]; omega
      · exact DepositProgress.of_same (hsame1.trans ⟨rfl, rfl, rfl⟩)
  · intro b w ⟨_, _, hPw⟩
    run_ensures
    exact hPw

end

end EthCLSpecs.Proofs.Fulu.IndexAssignment
