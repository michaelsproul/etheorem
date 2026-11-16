import EthCLSpecs.Proofs.Heze.Invariants.Slots
import EthCLSpecs.Proofs.Heze.Invariants.Block
import EthCLSpecs.Proofs.Heze.Reachable
import EthCLSpecs.Proofs.Gloas.ReachableInvariants

/-!
# `EthCLSpecs.Proofs.Heze.ReachableInvariants`: every reachable Heze state satisfies the invariants

The Heze counterpart of `Proofs/Gloas/ReachableInvariants.lean`.
`ReachableState.simpleStateInvariants` is the induction over the Heze inductive.

* `anchor`: a hypothesis on the Heze anchors.
* `upgrade`: the Gloas state satisfies the Gloas invariants
  (`EthCLSpecs.Proofs.Gloas.ReachableState.simpleStateInvariants`), and `upgradeToHeze`
  (`Heze/Upgrade.lean:88-138`) carries them over (`upgradeToHeze_invariants`). The upgrade copies
  every value the invariants read and writes a `fork` field for the current epoch and Heze's
  version. It has no closing step, so the upgraded state is the reachable one.
* `slots` and `block`: `processSlots_ensures` and `processBlock_ensures`.

The Heze block (`Heze/Transition.lean:71-79`) is the Gloas one without `process_eth1_data`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Heze
open EthCLSpecs.Heze.Const (hezeForkVersion)
open scoped EthCLSpecs.Heze.Downgrade EthCLSpecs.Gloas.Downgrade

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## The upgrade -/

omit [HasherTag] [CryptoBackend] in
/-- `upgradeToHeze` carries the Gloas invariants to the Heze ones. The upgrade rejects when the
eth1 deposit queue has not drained, so the hypothesis is that it returned a state. That state
copies every value the invariants read, maps the registry lists element by element, and has a
`fork` field for the current epoch and Heze's version. -/
theorem upgradeToHeze_invariants {u : EthCLSpecs.Gloas.BeaconState} {w : BeaconState}
    (hu : EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (h : upgradeToHeze hezeForkVersion u = .ok w) : SimpleStateInvariants w := by
  unfold upgradeToHeze at h
  split at h
  · -- The assert passed: the bind returns the record, so `w` is that record.
    injection h with h
    subst h
    obtain ⟨hh, hr, hc, _⟩ := hu
    refine ⟨hh, ?_, hc, ⟨UInt64.le_refl _, rfl⟩⟩
    obtain ⟨hb, hi, hp, hq⟩ := hr
    simp only [SizzLean.Repr.ProgressiveList.size] at hb hi hp hq
    simp only [RegistrySizes, SizzLean.Repr.ProgressiveList.size, Array.size_map]
    exact ⟨hb, hi, hp, hq⟩
  · cases h

/-! ## The header step and `process_block` -/

omit [CryptoBackend] in
/-- `process_block_header` writes a header whose slot is the block's, which it asserts is the
state's. Every other value the invariants read stays. -/
theorem processBlockHeader_ensures (block : BeaconBlock) (v : BeaconState)
    (hv : SimpleStateInvariants v) :
    RunEnsures v (processBlockHeader (StateTransition := HezeRun) block)
      (fun _ w => w.slot = v.slot ∧ SimpleStateInvariants w) := by
  unfold processBlockHeader
  run_ensures
  have h : (block.slot == (pureState v).view.slot) = true := by with_reducible assumption
  simp only [box_reduce, beq_iff_eq] at h
  refine ⟨rfl, ?_, hv.registrySizes, hv.checkpointOrder, hv.forkConsistent⟩
  show block.slot ≤ v.slot
  rw [h]
  exact UInt64.le_refl _

omit [HasherTag] [CryptoBackend] in
/-- The `KeepsCore` block substeps keep the post-header core values, so the final state has
the start's slot and satisfies the invariants. -/
theorem slot_inv_of_stepInv {v w1 w : BeaconState} (hs : w1.slot = v.slot)
    (hinv : SimpleStateInvariants w1) (hw : StepInv (coreFields w1) w) :
    w.slot = v.slot ∧ SimpleStateInvariants w :=
  ⟨(congrArg CoreFields.slot hw.1).trans hs, SimpleStateInvariants.of_coreFields_eq hw.1 hw.2 hinv⟩

/-- The Heze block applies the parent payload before the header, as the Gloas block does. Both
the payload step and the substeps after the header keep the core values, so the slot stays and
the invariants hold. -/
theorem processBlock_ensures (block : BeaconBlock) (v : BeaconState)
    (hv : SimpleStateInvariants v) :
    RunEnsures v (processBlock (StateTransition := HezeRun) block)
      (fun _ w => w.slot = v.slot ∧ SimpleStateInvariants w) := by
  unfold processBlock
  run_ensures
  refine Preserves.run (processParentExecutionPayload_keepsCore _ (coreFields v))
    ⟨rfl, hv.registrySizes⟩ (fun _ w0 h0 => ?_)
  have hinv0 := SimpleStateInvariants.of_coreFields_eq h0.1 h0.2 hv
  have hs0 : w0.slot = v.slot := congrArg CoreFields.slot h0.1
  run_ensures
  refine (processBlockHeader_ensures block w0 hinv0).weaken fun _ w1 h1 => ?_
  obtain ⟨hs1, hinv1⟩ := h1
  have _hst : StepInv (coreFields w1) w1 := ⟨rfl, hinv1.registrySizes⟩
  run_ensures
  call processWithdrawals_keepsCore
  run_ensures
  call processExecutionPayloadBid_keepsCore _
  run_ensures
  call processRandao_keepsCore _
  run_ensures
  call processOperations_keepsCore _ _
  run_ensures
  call processSyncAggregate_keepsCore _
  exact slot_inv_of_stepInv (hs1.trans hs0) hinv1 (by assumption)

/-! ## The induction -/

namespace ReachableState

variable {anchors : Anchors} {validated : Bool} {nextForkEpoch : Epoch}

/-- Every reachable Heze state satisfies `SimpleStateInvariants`, once every Fulu, Gloas and
Heze anchor satisfies its fork's invariants. -/
theorem simpleStateInvariants
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ v, anchors.heze v → SimpleStateInvariants v)
    {v : BeaconState} (h : ReachableState anchors validated nextForkEpoch v) :
    SimpleStateInvariants v := by
  induction h with
  | anchor ha _ => exact hH _ ha
  | upgrade hu _ _ hup =>
    exact upgradeToHeze_invariants
      (EthCLSpecs.Proofs.Gloas.ReachableState.simpleStateInvariants hF hG hu) hup
  | slots target _ _ hrun ih => exact ((processSlots_ensures target _ ih).runPure_ok hrun).2.2
  | block sb _ _ _ hrun _ ih => exact ((processBlock_ensures _ _ ih).runPure_ok hrun).2

end ReachableState

end

end EthCLSpecs.Proofs.Heze
