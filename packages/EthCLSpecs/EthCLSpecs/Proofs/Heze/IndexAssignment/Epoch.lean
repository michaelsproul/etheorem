import EthCLSpecs.Proofs.Heze.IndexAssignment.Helpers
import EthCLSpecs.Proofs.Heze.Invariants.Epoch

/-!
# `EthCLSpecs.Proofs.Heze.IndexAssignment.Epoch`: the Heze epoch substeps keep the deposit frame

The Heze counterpart of `Proofs/Gloas/IndexAssignment/Epoch.lean`. The Heze `processEpoch`
(`Heze/Transition.lean:30-46`) runs the Gloas substeps without `process_eth1_data_reset`
(EIP-8015), so fourteen of its sixteen substeps keep the frame of `Frame.lean`.

Justification has its fact in `Slots.lean`, and the queue scan has its contract in
`Deposits.lean`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze.IndexAssignment

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Heze

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [CryptoBackend] in
theorem processInactivityUpdates_keepsFrame :
    KeepsFrame (processInactivityUpdates (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processInactivityUpdates
  run_ensures
  all_goals try frame_close
  refine runEnsures_modifyThe (pureState_forIn_array_inv (StepInv c)
    (by intro _ _ _; exact ⟨_, rfl, by frame_close⟩) _ _ hv)

omit [Config] [CryptoBackend] in
theorem applyDeltas_keepsFrame (rewards penalties : Array Gwei) {c : Ctx}
    {s v : BeaconState} (hs : StepInv c s) :
    RunEnsures v (applyDeltas (StateTransition := HezeRun) rewards penalties (pureState s))
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') := by
  unfold applyDeltas
  run_ensures
  refine (runEnsures_forIn_range_box (StepInv c) _ (fun i s w _ hs => ?_) s v hs).weaken ?_
  · run_ensures
    call_box increaseBalance_keepsFrame _ _
    run_ensures
    call_box decreaseBalance_keepsFrame _ _
    run_ensures
    exact ⟨rfl, _, rfl, ‹_›⟩
  · intro b w hb
    run_ensures
    exact hb

omit [CryptoBackend] in
theorem processRewardsAndPenalties_keepsFrame :
    KeepsFrame (processRewardsAndPenalties (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processRewardsAndPenalties
  run_ensures
  all_goals try frame_close
  refine (Preserves.forIn_list _ _ (fun x _ w hw => ?_)).run (by frame_close) (fun _ w hw => ?_)
  · obtain ⟨_, _⟩ := x
    run_ensures
    call_box applyDeltas_keepsFrame _ _
    run_ensures
    frame_close
  · run_ensures
    call_box applyDeltas_keepsFrame _ _
    run_ensures
    frame_close

omit [CryptoBackend] in
/-- `process_registry_updates` keeps the frame. It is the one frame step that writes an
`activation_eligibility_epoch`: a validator that enters the activation queue gets
`current_epoch + 1`, which `EligStep` allows at the context's slot.

The walk leaves six goals per loop iteration, one per path through the three guards. A path
through the eligibility write ends in a state `StepInv.of_eligWrite` covers, and `elig_leaf`
applies it. It must run before `frame_close`: `frame_eq` proves its leaves in a nested `by`,
which logs an error on such a state where a tactic would fail. -/
theorem processRegistryUpdates_keepsFrame :
    KeepsFrame (processRegistryUpdates (StateTransition := HezeRun)) := by
  intro c v hv
  -- `currentEpochOf` reads the slot of the state the step starts at, which is the context's.
  have hcur : currentEpochOf (pureState v) + 1 = computeEpochAtSlot c.slot + 1 := by
    rw [← hv.1]; rfl
  unfold processRegistryUpdates
  run_ensures
  refine (Preserves.forIn_range _ _ (fun i _ _ w hw => ?_)).run hv (fun _ _ h => ?_)
  · run_ensures
    -- The two call sites of `initiateValidatorExit`. `c` is explicit, since the premise is a
    -- goal here and no tactic block fixes it.
    all_goals try (
      refine Preserves.run (initiateValidatorExit_keepsFrame _ c) ?_ (fun _ _ _ => ?_))
    all_goals try run_ensures
    all_goals first
      | (refine StepInv.of_eligWrite hw ?_ ?_ ?_ (UInt64.ofNat i).toNat _ hcur ?_
         <;> simp [coreFields, listSizes, box_reduce, elig_set!_eq]
         <;> done)
      | frame_close
  · run_ensures
    exact h

omit [Config] [CryptoBackend] in
theorem processSlashings_keepsFrame :
    KeepsFrame (processSlashings (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processSlashings
  run_ensures
  refine (runEnsures_forIn_range_box (StepInv c) _ (fun i s w _ hs => ?_) v v hv).weaken ?_
  · run_ensures
    · call_box decreaseBalance_keepsFrame _ _
      run_ensures
      exact ⟨rfl, _, rfl, ‹_›⟩
    · exact ⟨rfl, _, rfl, hs⟩
  · intro b w ⟨hw, s', hb, hs'⟩
    subst hw hb
    run_ensures
    exact hs'

omit [Config] [CryptoBackend] in
theorem pcLoop_keepsFrame (cons : Array PendingConsolidation) (nextEpoch : Epoch) :
    KeepsFrame (pcLoop (StateTransition := HezeRun) cons nextEpoch) := by
  intro c
  unfold pcLoop
  refine Preserves.fuelLoop _ _ _ (fun _ w hw => ?_)
  run_ensures
  all_goals try frame_close
  call_box decreaseBalance_keepsFrame _ _
  run_ensures
  call_box increaseBalance_keepsFrame _ _
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processPendingConsolidations_keepsFrame :
    KeepsFrame (processPendingConsolidations (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processPendingConsolidations
  run_ensures
  call pcLoop_keepsFrame _ _
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processEffectiveBalanceUpdates_keepsFrame :
    KeepsFrame (processEffectiveBalanceUpdates (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processEffectiveBalanceUpdates
  refine runEnsures_modifyThe (pureState_forIn_range_inv (StepInv c)
    (by intro _ _ _; dsimp only; split <;> exact ⟨_, rfl, by frame_close⟩) _ _ hv)

omit [Config] [CryptoBackend] in
theorem processSlashingsReset_keepsFrame :
    KeepsFrame (processSlashingsReset (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processSlashingsReset
  run_ensures
  call_ro getCurrentEpoch_readsOnly
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processRandaoMixesReset_keepsFrame :
    KeepsFrame (processRandaoMixesReset (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processRandaoMixesReset
  run_ensures
  call_ro getCurrentEpoch_readsOnly
  run_ensures
  call_ro getRandaoMix_readsOnly _
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processHistoricalSummariesUpdate_keepsFrame :
    KeepsFrame (processHistoricalSummariesUpdate (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processHistoricalSummariesUpdate
  run_ensures
  call_ro getCurrentEpoch_readsOnly
  run_ensures
  all_goals try frame_close
  append_split
  all_goals run_ensures
  all_goals frame_close

omit [Config] [CryptoBackend] in
/-- The rotation rebuilds both participation lists at the registry's length. The core values,
the keys and the eligibility epochs stay by `StepInv.of_parts`, and the sizes are proved as in
the `Invariants` module. -/
theorem processParticipationFlagUpdates_keepsFrame :
    KeepsFrame (processParticipationFlagUpdates (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processParticipationFlagUpdates
  run_ensures
  refine hv.of_parts (by simp only [coreFields, box_reduce])
    (by simp only [registryKeys, box_reduce]) (by simp only [registryElig, box_reduce]) ?_
  obtain ⟨hb, hi, hp, hq⟩ := hv.registrySizes
  simp only [RegistrySizes, SizzLean.Repr.ProgressiveList.size, box_reduce, Array.size_replicate]
  simp only [SizzLean.Repr.ProgressiveList.size] at hb hi hp hq
  exact ⟨hb, hi, hq, trivial⟩

omit [Config] in
theorem processSyncCommitteeUpdates_keepsFrame :
    KeepsFrame (processSyncCommitteeUpdates (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processSyncCommitteeUpdates
  run_ensures
  all_goals frame_close

omit [Config] [CryptoBackend] in
theorem processProposerLookahead_keepsFrame :
    KeepsFrame (processProposerLookahead (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processProposerLookahead
  run_ensures
  frame_close

/-! ## The EIP-7732 substeps -/

omit [Config] [CryptoBackend] in
theorem processBuilderPendingPayments_keepsFrame :
    KeepsFrame (processBuilderPendingPayments (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processBuilderPendingPayments
  run_ensures
  refine (Preserves.forIn_range _ _ (fun _ _ _ w hw => ?_)).run hv (fun _ w hw => ?_)
  · run_ensures
    all_goals frame_close
  · run_ensures
    frame_close

omit [Config] [CryptoBackend] in
theorem processPtcWindow_keepsFrame :
    KeepsFrame (processPtcWindow (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processPtcWindow
  run_ensures
  frame_close

end

end EthCLSpecs.Proofs.Heze.IndexAssignment
