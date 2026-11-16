import EthCLSpecs.Proofs.Fulu.IndexAssignment.Frame
import EthCLSpecs.Proofs.Fulu.Invariants.Helpers

/-!
# `EthCLSpecs.Proofs.Fulu.IndexAssignment.Helpers`: the shared mutators keep the deposit frame

The epoch and block steps reach the state through a small set of shared mutators: the
balance writes, the churn accounting, exits, slashing, and the compounding switch. Each keeps
the frame of `Frame.lean`. The proofs are the ones of `Proofs/Fulu/Invariants/Helpers.lean`,
run against this namespace's `StepInv`: a balance write touches no key, and a validator record
write keeps the record's `pubkey`.

`queueExcessActiveBalance` is the one mutator here that appends to the queue. The deposit it
appends carries the key of the validator it read, so the deposit names a key the registry
holds. That is an admitted deposit, and only inside a block, so the fact is
`KeepsFrameInBlock`. `switchToCompoundingValidator` calls it and has the same property.

The read-only accessors need no second proof. `ReadsOnly` does not name an invariant, so the
facts of the `Invariants` modules serve here as they are.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu.IndexAssignment

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Fulu

section

variable [Preset] [HasherTag]

/-- `increaseBalance` writes only the box it is handed. The returned box agrees with the handed
one under `FrameEq`: the write is to `balances`. -/
theorem increaseBalance_ensures (s v : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    RunEnsures v (increaseBalance (StateTransition := FuluRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ FrameEq s' s) := by
  unfold increaseBalance
  run_ensures
  exact ⟨trivial, _, rfl, by frame_eq⟩

/-- `decreaseBalance` writes only the box it is handed, as `increaseBalance` does. -/
theorem decreaseBalance_ensures (s v : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    RunEnsures v (decreaseBalance (StateTransition := FuluRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ FrameEq s' s) := by
  unfold decreaseBalance
  run_ensures
  exact ⟨trivial, _, rfl, by frame_eq⟩

/-- A box write that keeps `FrameEq` carries `StepInv` from the handed value to the returned
one: the form `call_box` reads. -/
theorem stepInv_of_box_ensures {act : FuluRun State} {s v : BeaconState} {c : Ctx}
    (h : RunEnsures v act (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ FrameEq s' s))
    (hs : StepInv c s) :
    RunEnsures v act (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') :=
  h.weaken fun _ _ ⟨hw, s', hb, hf⟩ => ⟨hw, s', hb, hs.of_frameEq hf⟩

theorem increaseBalance_keepsFrame (i : ValidatorIndex) (d : Gwei) {c : Ctx}
    {s v : BeaconState} (hs : StepInv c s) :
    RunEnsures v (increaseBalance (StateTransition := FuluRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') :=
  stepInv_of_box_ensures (increaseBalance_ensures s v i d) hs

theorem decreaseBalance_keepsFrame (i : ValidatorIndex) (d : Gwei) {c : Ctx}
    {s v : BeaconState} (hs : StepInv c s) :
    RunEnsures v (decreaseBalance (StateTransition := FuluRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') :=
  stepInv_of_box_ensures (decreaseBalance_ensures s v i d) hs

variable [Config] [CryptoBackend]

omit [CryptoBackend] in
theorem computeExitEpochAndUpdateChurn_keepsFrame (b : Gwei) :
    KeepsFrame (computeExitEpochAndUpdateChurn (StateTransition := FuluRun) b) := by
  intro c v hv
  unfold computeExitEpochAndUpdateChurn
  run_ensures
  all_goals frame_close

omit [CryptoBackend] in
theorem computeConsolidationEpochAndUpdateChurn_keepsFrame (b : Gwei) :
    KeepsFrame (computeConsolidationEpochAndUpdateChurn (StateTransition := FuluRun) b) := by
  intro c v hv
  unfold computeConsolidationEpochAndUpdateChurn
  run_ensures
  all_goals frame_close

omit [CryptoBackend] in
theorem initiateValidatorExit_keepsFrame (i : ValidatorIndex) :
    KeepsFrame (initiateValidatorExit (StateTransition := FuluRun) i) := by
  intro c v hv
  unfold initiateValidatorExit
  run_ensures
  all_goals try frame_close
  call computeExitEpochAndUpdateChurn_keepsFrame _
  run_ensures
  frame_close

omit [CryptoBackend] in
theorem slashValidator_keepsFrame (i : ValidatorIndex) :
    KeepsFrame (slashValidator (StateTransition := FuluRun) i) := by
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
  frame_close

omit [Config] [CryptoBackend] in
/-- The excess-balance deposit names the validator the step read, so its key is in the key
list, and the in-block context admits it. `StepInv.of_push` takes the five facts: the slot,
the finalized epoch and `listSizes` stay, the queue grows by the one deposit, and the deposit
is admitted. -/
theorem queueExcessActiveBalance_keepsFrame (i : ValidatorIndex) :
    KeepsFrameInBlock (queueExcessActiveBalance (StateTransition := FuluRun) i) := by
  intro c hc v hv
  unfold queueExcessActiveBalance
  run_ensures
  all_goals try frame_close
  append_split
  all_goals run_ensures
  refine StepInv.of_push hv _ (by simp [box_reduce]) (by simp [box_reduce])
    (by simp [listSizes, box_reduce, SizzLean.Proofs.sszListSet!_size])
    (by simp only [box_reduce]; assumption) ⟨hc, Or.inl ?_⟩
  rw [← hv.2.2.1]
  exact mem_keys_of_get? (by assumption)

omit [Config] [CryptoBackend] in
theorem switchToCompoundingValidator_keepsFrame (i : ValidatorIndex) :
    KeepsFrameInBlock (switchToCompoundingValidator (StateTransition := FuluRun) i) := by
  intro c hc v hv
  unfold switchToCompoundingValidator
  run_ensures
  refine Preserves.run (queueExcessActiveBalance_keepsFrame _ c hc) (by frame_close)
    (fun _ _ _ => ?_)
  run_ensures
  frame_close

end

end EthCLSpecs.Proofs.Fulu.IndexAssignment
