import EthCLSpecs.Proofs.Gloas.IndexAssignment.Frame
import EthCLSpecs.Proofs.Gloas.Invariants.Helpers

/-!
# `EthCLSpecs.Proofs.Gloas.IndexAssignment.Helpers`: the Gloas mutators keep the deposit frame

The Gloas counterpart of `Proofs/Fulu/IndexAssignment/Helpers.lean`. Each mutator keeps the
frame of `Frame.lean`, by the proof of `Proofs/Gloas/Invariants/Helpers.lean` run against this
namespace's `StepInv`. Gloas overrides `slashValidator`, which ends by voiding the slashed
proposer's pending builder payments; that write touches `builderPendingPayments` alone.

`queueExcessActiveBalance` appends a deposit under the key of the validator it read. The
pending-deposit queue is a progressive list in Gloas, so the append cannot fail and the proof
has one leaf. The fact is `KeepsFrameInBlock`, as in Fulu.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas.IndexAssignment

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Gloas

section

variable [Preset] [HasherTag]

/-- `increaseBalance` writes only the box it is handed. The returned box agrees with the handed
one under `FrameEq`: the write is to `balances`. -/
theorem increaseBalance_ensures (s v : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    RunEnsures v (increaseBalance (StateTransition := GloasRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ FrameEq s' s) := by
  unfold increaseBalance
  run_ensures
  exact ⟨trivial, _, rfl, by frame_eq⟩

/-- `decreaseBalance` writes only the box it is handed, as `increaseBalance` does. -/
theorem decreaseBalance_ensures (s v : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    RunEnsures v (decreaseBalance (StateTransition := GloasRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ FrameEq s' s) := by
  unfold decreaseBalance
  run_ensures
  exact ⟨trivial, _, rfl, by frame_eq⟩

/-- A box write that keeps `FrameEq` carries `StepInv` from the handed value to the returned
one: the form `call_box` reads. -/
theorem stepInv_of_box_ensures {act : GloasRun State} {s v : BeaconState} {c : Ctx}
    (h : RunEnsures v act (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ FrameEq s' s))
    (hs : StepInv c s) :
    RunEnsures v act (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') :=
  h.weaken fun _ _ ⟨hw, s', hb, hf⟩ => ⟨hw, s', hb, hs.of_frameEq hf⟩

theorem increaseBalance_keepsFrame (i : ValidatorIndex) (d : Gwei) {c : Ctx}
    {s v : BeaconState} (hs : StepInv c s) :
    RunEnsures v (increaseBalance (StateTransition := GloasRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') :=
  stepInv_of_box_ensures (increaseBalance_ensures s v i d) hs

theorem decreaseBalance_keepsFrame (i : ValidatorIndex) (d : Gwei) {c : Ctx}
    {s v : BeaconState} (hs : StepInv c s) :
    RunEnsures v (decreaseBalance (StateTransition := GloasRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') :=
  stepInv_of_box_ensures (decreaseBalance_ensures s v i d) hs

variable [Config] [CryptoBackend]

/-! ## Churn accounting and the validator-lifecycle mutators -/

omit [CryptoBackend] in
theorem computeExitEpochAndUpdateChurn_keepsFrame (b : Gwei) :
    KeepsFrame (computeExitEpochAndUpdateChurn (StateTransition := GloasRun) b) := by
  intro c v hv
  unfold computeExitEpochAndUpdateChurn
  run_ensures
  all_goals frame_close

omit [CryptoBackend] in
theorem computeConsolidationEpochAndUpdateChurn_keepsFrame (b : Gwei) :
    KeepsFrame (computeConsolidationEpochAndUpdateChurn (StateTransition := GloasRun) b) := by
  intro c v hv
  unfold computeConsolidationEpochAndUpdateChurn
  run_ensures
  all_goals frame_close

omit [CryptoBackend] in
theorem initiateValidatorExit_keepsFrame (i : ValidatorIndex) :
    KeepsFrame (initiateValidatorExit (StateTransition := GloasRun) i) := by
  intro c v hv
  unfold initiateValidatorExit
  run_ensures
  all_goals try frame_close
  call computeExitEpochAndUpdateChurn_keepsFrame _
  run_ensures
  frame_close

omit [CryptoBackend] in
theorem slashValidator_keepsFrame (i : ValidatorIndex) :
    KeepsFrame (slashValidator (StateTransition := GloasRun) i) := by
  intro c v hv
  unfold slashValidator
  run_ensures
  call initiateValidatorExit_keepsFrame _
  run_ensures
  call_box decreaseBalance_keepsFrame _ _
  run_ensures
  call_box increaseBalance_keepsFrame _ _
  run_ensures
  call_box increaseBalance_keepsFrame _ _
  run_ensures
  refine runEnsures_modifyThe (pureState_forIn_range_inv (StepInv c)
    (by intro _ _ _; dsimp only; split <;> exact ⟨_, rfl, by frame_close⟩) _ _ (by frame_close))

omit [Config] [CryptoBackend] in
/-- The excess-balance deposit names the validator the step read, so its key is in the key
list, and the in-block context admits it. The queue is a progressive list, so the append is a
push and `StepInv.of_push` closes the leaf. -/
theorem queueExcessActiveBalance_keepsFrame (i : ValidatorIndex) :
    KeepsFrameInBlock (queueExcessActiveBalance (StateTransition := GloasRun) i) := by
  intro c hc v hv
  unfold queueExcessActiveBalance
  run_ensures
  all_goals try frame_close
  refine StepInv.of_push hv _ (by simp [box_reduce]) (by simp [box_reduce])
    (by simp [listSizes, box_reduce, SizzLean.Proofs.progressiveListSet!_size])
    (by simp only [box_reduce]; rfl) ⟨hc, Or.inl ?_⟩
  rw [← hv.2.2.1]
  exact mem_keys_of_get? (by assumption)

omit [Config] [CryptoBackend] in
theorem switchToCompoundingValidator_keepsFrame (i : ValidatorIndex) :
    KeepsFrameInBlock (switchToCompoundingValidator (StateTransition := GloasRun) i) := by
  intro c hc v hv
  unfold switchToCompoundingValidator
  run_ensures
  refine Preserves.run (queueExcessActiveBalance_keepsFrame _ c hc) (by frame_close)
    (fun _ _ _ => ?_)
  run_ensures
  frame_close

end

end EthCLSpecs.Proofs.Gloas.IndexAssignment
