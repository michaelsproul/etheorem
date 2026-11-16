import EthCLSpecs.Proofs.Heze.StateInvariants
import EthCLSpecs.Heze.Transition

/-!
# `EthCLSpecs.Proofs.Heze.Invariants.Helpers`: the shared mutators keep the core values

The Heze counterpart of `Proofs/Gloas/Invariants/Helpers.lean`. Heze inherits each of these
mutators from Gloas, and each inheritance is a separate constant, so each proof is restated
here over the Heze state. Heze overrides `applyPendingDeposit` (EIP-8365): a deposit for a
new key with BLS credentials returns at once, which adds one branch that writes nothing.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Heze

section

variable [Preset] [HasherTag]

/-! ## Box-returning balance writes -/

theorem increaseBalance_ensures (s v : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    RunEnsures v (increaseBalance (StateTransition := HezeRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ FrameEq s' s) := by
  unfold increaseBalance
  run_ensures
  exact ⟨trivial, _, rfl, by frame_eq⟩

theorem decreaseBalance_ensures (s v : BeaconState) (i : ValidatorIndex) (d : Gwei) :
    RunEnsures v (decreaseBalance (StateTransition := HezeRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ FrameEq s' s) := by
  unfold decreaseBalance
  run_ensures
  exact ⟨trivial, _, rfl, by frame_eq⟩

theorem stepInv_of_box_ensures {act : HezeRun State} {s v : BeaconState} {c : CoreFields}
    (h : RunEnsures v act (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ FrameEq s' s))
    (hs : StepInv c s) :
    RunEnsures v act (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') :=
  h.weaken fun _ _ ⟨hw, s', hb, hf⟩ => ⟨hw, s', hb, hs.of_frameEq hf⟩

theorem increaseBalance_keepsCore (i : ValidatorIndex) (d : Gwei) {c : CoreFields}
    {s v : BeaconState} (hs : StepInv c s) :
    RunEnsures v (increaseBalance (StateTransition := HezeRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') :=
  stepInv_of_box_ensures (increaseBalance_ensures s v i d) hs

theorem decreaseBalance_keepsCore (i : ValidatorIndex) (d : Gwei) {c : CoreFields}
    {s v : BeaconState} (hs : StepInv c s) :
    RunEnsures v (decreaseBalance (StateTransition := HezeRun) (pureState s) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') :=
  stepInv_of_box_ensures (decreaseBalance_ensures s v i d) hs

/-! ## Read-only accessors -/

theorem getBlockRootAtSlot_readsOnly (s : BeaconState) (sl : Slot) :
    ReadsOnly (getBlockRootAtSlot (StateTransition := HezeRun) (pureState s) sl) := by
  intro v
  unfold getBlockRootAtSlot
  run_ensures
  all_goals rfl

theorem getBlockRoot_readsOnly (s : BeaconState) (e : Epoch) :
    ReadsOnly (getBlockRoot (StateTransition := HezeRun) (pureState s) e) :=
  getBlockRootAtSlot_readsOnly s _

theorem getRandaoMix_readsOnly (e : Epoch) :
    ReadsOnly (getRandaoMix (StateTransition := HezeRun) e) := by
  intro v
  unfold getRandaoMix
  run_ensures

theorem getCurrentEpoch_readsOnly : ReadsOnly (getCurrentEpoch (StateTransition := HezeRun)) := by
  intro v
  unfold getCurrentEpoch
  run_ensures

variable [Config] [CryptoBackend]

/-! ## Churn accounting and the validator-lifecycle mutators -/

omit [CryptoBackend] in
theorem computeExitEpochAndUpdateChurn_keepsCore (b : Gwei) :
    KeepsCore (computeExitEpochAndUpdateChurn (StateTransition := HezeRun) b) := by
  intro c v hv
  unfold computeExitEpochAndUpdateChurn
  run_ensures
  all_goals frame_close

omit [CryptoBackend] in
theorem computeConsolidationEpochAndUpdateChurn_keepsCore (b : Gwei) :
    KeepsCore (computeConsolidationEpochAndUpdateChurn (StateTransition := HezeRun) b) := by
  intro c v hv
  unfold computeConsolidationEpochAndUpdateChurn
  run_ensures
  all_goals frame_close

omit [CryptoBackend] in
theorem initiateValidatorExit_keepsCore (i : ValidatorIndex) :
    KeepsCore (initiateValidatorExit (StateTransition := HezeRun) i) := by
  intro c v hv
  unfold initiateValidatorExit
  run_ensures
  all_goals try frame_close
  call computeExitEpochAndUpdateChurn_keepsCore _
  run_ensures
  frame_close

omit [CryptoBackend] in
theorem slashValidator_keepsCore (i : ValidatorIndex) :
    KeepsCore (slashValidator (StateTransition := HezeRun) i) := by
  intro c v hv
  unfold slashValidator
  run_ensures
  call initiateValidatorExit_keepsCore _
  run_ensures
  call_box decreaseBalance_keepsCore _ _
  run_ensures
  call_box increaseBalance_keepsCore _ _
  run_ensures
  call_box increaseBalance_keepsCore _ _
  run_ensures
  refine runEnsures_modifyThe (pureState_forIn_range_inv (StepInv c)
    (by intro _ _ _; dsimp only; split <;> exact ⟨_, rfl, by frame_close⟩) _ _ (by frame_close))

/-! ## Compounding and the registry append -/

omit [Config] [CryptoBackend] in
theorem queueExcessActiveBalance_keepsCore (i : ValidatorIndex) :
    KeepsCore (queueExcessActiveBalance (StateTransition := HezeRun) i) := by
  intro c v hv
  unfold queueExcessActiveBalance
  run_ensures
  all_goals frame_close

omit [Config] [CryptoBackend] in
theorem switchToCompoundingValidator_keepsCore (i : ValidatorIndex) :
    KeepsCore (switchToCompoundingValidator (StateTransition := HezeRun) i) := by
  intro c v hv
  unfold switchToCompoundingValidator
  run_ensures
  call queueExcessActiveBalance_keepsCore _
  run_ensures
  frame_close

section RegistryAppend

local macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| (with_reducible refine runEnsures_ite (fun hc => ?_) (fun hc => ?_))
              <;> try (simp [*, box_reduce] at hc; done))

omit [Config] [CryptoBackend] in
theorem addValidatorToRegistry_keepsCore (pk : BLSPubkey) (wc : Bytes32) (amt : Gwei) :
    KeepsCore (addValidatorToRegistry (StateTransition := HezeRun) pk wc amt) := by
  intro c v hv
  obtain ⟨hcore, hb, hi, hp, hq⟩ := hv
  simp only [SizzLean.Repr.ProgressiveList.size] at hb hi hp hq
  unfold addValidatorToRegistry
  run_ensures
  simp only [StepInv, coreFields, RegistrySizes, SizzLean.Repr.ProgressiveList.size, box_reduce,
    SizzLean.Repr.ProgressiveList.push, Array.size_push]
  exact ⟨hcore, by omega, by omega, by omega, by omega⟩

end RegistryAppend

theorem applyPendingDeposit_keepsCore (d : PendingDeposit) :
    KeepsCore (applyPendingDeposit (StateTransition := HezeRun) d) := by
  intro c v hv
  unfold applyPendingDeposit
  run_ensures
  split
  · run_ensures
    call_box increaseBalance_keepsCore _ _
    run_ensures
    frame_close
  · run_ensures
    all_goals try frame_close
    call addValidatorToRegistry_keepsCore _ _ _
    frame_close

end

end EthCLSpecs.Proofs.Heze
