import EthCLSpecs.Proofs.Heze.Invariants.Helpers
import EthCLLib.Proofs.Arith

/-!
# `EthCLSpecs.Proofs.Heze.Invariants.Justification`: justification moves the checkpoint bound

The Heze counterpart of `Proofs/Gloas/Invariants/Justification.lean`. Heze inherits both
justification bodies, so the argument is the same: the step moves the bound on the
current-justified epoch from the previous epoch to the current one, keeps the checkpoint
order, and writes no other value `SimpleStateInvariants` reads.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub)
open EthCLSpecs.Heze

section

variable [Preset] [HasherTag]

def CheckpointsBelowPrevious (v : BeaconState) : Prop :=
  v.finalizedCheckpoint.epoch ≤ v.previousJustifiedCheckpoint.epoch ∧
  v.previousJustifiedCheckpoint.epoch ≤ v.currentJustifiedCheckpoint.epoch ∧
  v.currentJustifiedCheckpoint.epoch ≤ saturatingSub (computeEpochAtSlot v.slot) 1

def CheckpointsBelowCurrent (v : BeaconState) : Prop :=
  v.finalizedCheckpoint.epoch ≤ v.previousJustifiedCheckpoint.epoch ∧
  v.previousJustifiedCheckpoint.epoch ≤ v.currentJustifiedCheckpoint.epoch ∧
  v.currentJustifiedCheckpoint.epoch ≤ computeEpochAtSlot v.slot

def JFFrame (w v : BeaconState) : Prop :=
  w.slot = v.slot ∧ w.latestBlockHeader.slot = v.latestBlockHeader.slot ∧
  w.forkData = v.forkData ∧ listSizes w = listSizes v

omit [Preset] [HasherTag] in
theorem checkpoint_order_step {fin prev curr e fin' curr' : UInt64}
    (h1 : fin ≤ prev) (h2 : prev ≤ curr) (h3 : curr ≤ saturatingSub e 1)
    (hcurr' : curr' = curr ∨ curr' = saturatingSub e 1 ∨ curr' = e)
    (hfin' : fin' = fin ∨ fin' = prev ∨ fin' = curr) :
    fin' ≤ curr ∧ curr ≤ curr' ∧ curr' ≤ e := by
  have hp : (saturatingSub e 1).toNat = e.toNat - 1 := EthCLLib.Proofs.saturatingSub_toNat e 1
  simp only [UInt64.le_iff_toNat_le] at h1 h2 h3 ⊢
  rcases hcurr' with rfl | rfl | rfl <;> rcases hfin' with rfl | rfl | rfl <;> omega

variable [Config] [CryptoBackend]

local macro "call_reads " h:term : tactic =>
  `(tactic| (refine EthCLLib.Proofs.RunEnsures.weaken ($h _) (fun _ _ hro => ?_); subst hro))

local macro "pick_choice" : tactic =>
  `(tactic| first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl))

set_option maxHeartbeats 4000000 in
omit [Config] [CryptoBackend] in
theorem weighJustificationAndFinalization_ensures (total prevT currT : Gwei) (v : BeaconState)
    (hv : CheckpointsBelowPrevious v) :
    RunEnsures v (weighJustificationAndFinalization (StateTransition := HezeRun) total prevT currT)
      (fun _ w => JFFrame w v ∧ CheckpointsBelowCurrent w) := by
  unfold weighJustificationAndFinalization
  run_ensures
  all_goals try (call_reads getBlockRoot_readsOnly _ _; run_ensures)
  all_goals try (call_reads getBlockRoot_readsOnly _ _; run_ensures)
  all_goals refine runEnsures_modifyThe_view ?_ ?_
  all_goals simp only [box_reduce, Id.run, *]
  all_goals repeat' split_ite
  all_goals first
    | rfl
    | exact ⟨⟨rfl, rfl, rfl, rfl⟩,
        checkpoint_order_step hv.1 hv.2.1 hv.2.2 (by pick_choice) (by pick_choice)⟩

omit [HasherTag] [Config] [CryptoBackend] in
theorem CheckpointsBelowPrevious.belowCurrent {v : BeaconState} (hv : CheckpointsBelowPrevious v) :
    CheckpointsBelowCurrent v :=
  ⟨hv.1, hv.2.1, by
    have h := hv.2.2
    have hle := EthCLLib.Proofs.saturatingSub_le (computeEpochAtSlot v.slot) 1
    simp only [UInt64.le_iff_toNat_le] at h hle ⊢
    omega⟩

omit [Config] [CryptoBackend] in
theorem processJustificationAndFinalization_ensures (v : BeaconState)
    (hv : CheckpointsBelowPrevious v) :
    RunEnsures v (processJustificationAndFinalization (StateTransition := HezeRun))
      (fun _ w => JFFrame w v ∧ CheckpointsBelowCurrent w) := by
  unfold processJustificationAndFinalization
  run_ensures
  · exact ⟨⟨rfl, rfl, rfl, rfl⟩, hv.belowCurrent⟩
  · exact weighJustificationAndFinalization_ensures _ _ _ v hv

end

end EthCLSpecs.Proofs.Heze
