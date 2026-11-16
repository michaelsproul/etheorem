import EthCLSpecs.Proofs.Heze.Invariants.Helpers

/-!
# `EthCLSpecs.Proofs.Heze.Invariants.Epoch`: the epoch substeps keep the core values

The Heze counterpart of `Proofs/Gloas/Invariants/Epoch.lean`. The Heze `processEpoch`
(`Heze/Transition.lean:30-46`) is the Gloas one without `process_eth1_data_reset` (EIP-8015), so
sixteen substeps run and fifteen are `KeepsCore`. The fact for
`processJustificationAndFinalization` is in `Proofs/Heze/Invariants/Justification.lean`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Heze

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [CryptoBackend] in
theorem processInactivityUpdates_keepsCore :
    KeepsCore (processInactivityUpdates (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processInactivityUpdates
  run_ensures
  all_goals try frame_close
  refine runEnsures_modifyThe (pureState_forIn_array_inv (StepInv c)
    (by intro _ _ _; exact ⟨_, rfl, by frame_close⟩) _ _ hv)

omit [Config] [CryptoBackend] in
theorem applyDeltas_keepsCore (rewards penalties : Array Gwei) {c : CoreFields}
    {s v : BeaconState} (hs : StepInv c s) :
    RunEnsures v (applyDeltas (StateTransition := HezeRun) rewards penalties (pureState s))
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ StepInv c s') := by
  unfold applyDeltas
  run_ensures
  refine (runEnsures_forIn_range_box (StepInv c) _ (fun i s w _ hs => ?_) s v hs).weaken ?_
  · run_ensures
    call_box increaseBalance_keepsCore _ _
    run_ensures
    call_box decreaseBalance_keepsCore _ _
    run_ensures
    exact ⟨rfl, _, rfl, ‹_›⟩
  · intro b w hb
    run_ensures
    exact hb

omit [CryptoBackend] in
theorem processRewardsAndPenalties_keepsCore :
    KeepsCore (processRewardsAndPenalties (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processRewardsAndPenalties
  run_ensures
  all_goals try frame_close
  refine (Preserves.forIn_list _ _ (fun x _ w hw => ?_)).run (by frame_close) (fun _ w hw => ?_)
  · obtain ⟨_, _⟩ := x
    run_ensures
    call_box applyDeltas_keepsCore _ _
    run_ensures
    frame_close
  · run_ensures
    call_box applyDeltas_keepsCore _ _
    run_ensures
    frame_close

omit [CryptoBackend] in
theorem processRegistryUpdates_keepsCore :
    KeepsCore (processRegistryUpdates (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processRegistryUpdates
  run_ensures
  refine (Preserves.forIn_range _ _ (fun _ _ _ w hw => ?_)).run hv (fun _ _ h => ?_)
  · run_ensures
    all_goals try frame_close
    all_goals try (call initiateValidatorExit_keepsCore _; run_ensures)
    all_goals frame_close
  · run_ensures
    exact h

omit [Config] [CryptoBackend] in
theorem processSlashings_keepsCore :
    KeepsCore (processSlashings (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processSlashings
  run_ensures
  refine (runEnsures_forIn_range_box (StepInv c) _ (fun i s w _ hs => ?_) v v hv).weaken ?_
  · run_ensures
    · call_box decreaseBalance_keepsCore _ _
      run_ensures
      exact ⟨rfl, _, rfl, ‹_›⟩
    · exact ⟨rfl, _, rfl, hs⟩
  · intro b w ⟨hw, s', hb, hs'⟩
    subst hw hb
    run_ensures
    exact hs'

theorem ppdLoop_keepsCore (deposits : Array PendingDeposit) (finalizedSlot avail : Gwei)
    (nextEpoch : Epoch) :
    KeepsCore (ppdLoop (StateTransition := HezeRun) deposits finalizedSlot avail nextEpoch) := by
  intro c
  unfold ppdLoop
  refine Preserves.fuelLoop _ _ _ (fun _ w hw => ?_)
  run_ensures
  all_goals try frame_close
  all_goals try (split <;> run_ensures)
  all_goals try frame_close
  all_goals (call applyPendingDeposit_keepsCore _; run_ensures; frame_close)

theorem processPendingDeposits_keepsCore :
    KeepsCore (processPendingDeposits (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processPendingDeposits
  run_ensures
  call ppdLoop_keepsCore _ _ _ _
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem pcLoop_keepsCore (cons : Array PendingConsolidation) (nextEpoch : Epoch) :
    KeepsCore (pcLoop (StateTransition := HezeRun) cons nextEpoch) := by
  intro c
  unfold pcLoop
  refine Preserves.fuelLoop _ _ _ (fun _ w hw => ?_)
  run_ensures
  all_goals try frame_close
  call_box decreaseBalance_keepsCore _ _
  run_ensures
  call_box increaseBalance_keepsCore _ _
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processPendingConsolidations_keepsCore :
    KeepsCore (processPendingConsolidations (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processPendingConsolidations
  run_ensures
  call pcLoop_keepsCore _ _
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processEffectiveBalanceUpdates_keepsCore :
    KeepsCore (processEffectiveBalanceUpdates (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processEffectiveBalanceUpdates
  refine runEnsures_modifyThe (pureState_forIn_range_inv (StepInv c)
    (by intro _ _ _; dsimp only; split <;> exact ⟨_, rfl, by frame_close⟩) _ _ hv)

omit [Config] [CryptoBackend] in
theorem processSlashingsReset_keepsCore :
    KeepsCore (processSlashingsReset (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processSlashingsReset
  run_ensures
  call_ro getCurrentEpoch_readsOnly
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processRandaoMixesReset_keepsCore :
    KeepsCore (processRandaoMixesReset (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processRandaoMixesReset
  run_ensures
  call_ro getCurrentEpoch_readsOnly
  run_ensures
  call_ro getRandaoMix_readsOnly _
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processHistoricalSummariesUpdate_keepsCore :
    KeepsCore (processHistoricalSummariesUpdate (StateTransition := HezeRun)) := by
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
theorem processParticipationFlagUpdates_keepsCore :
    KeepsCore (processParticipationFlagUpdates (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processParticipationFlagUpdates
  run_ensures
  obtain ⟨hc, hb, hi, hp, hq⟩ := hv
  refine ⟨by rw [← hc]; rfl, ?_⟩
  simp only [RegistrySizes, SizzLean.Repr.ProgressiveList.size, box_reduce, Array.size_replicate]
  simp only [SizzLean.Repr.ProgressiveList.size] at hb hi hp hq
  exact ⟨hb, hi, hq, trivial⟩

omit [Config] in
theorem processSyncCommitteeUpdates_keepsCore :
    KeepsCore (processSyncCommitteeUpdates (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processSyncCommitteeUpdates
  run_ensures
  all_goals frame_close

omit [Config] [CryptoBackend] in
theorem processProposerLookahead_keepsCore :
    KeepsCore (processProposerLookahead (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processProposerLookahead
  run_ensures
  frame_close

/-! ## The EIP-7732 substeps -/

omit [Config] [CryptoBackend] in
theorem processBuilderPendingPayments_keepsCore :
    KeepsCore (processBuilderPendingPayments (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processBuilderPendingPayments
  run_ensures
  refine (Preserves.forIn_range _ _ (fun _ _ _ w hw => ?_)).run hv (fun _ w hw => ?_)
  · run_ensures
    all_goals frame_close
  · run_ensures
    frame_close

omit [Config] [CryptoBackend] in
theorem processPtcWindow_keepsCore :
    KeepsCore (processPtcWindow (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processPtcWindow
  run_ensures
  frame_close

end

end EthCLSpecs.Proofs.Heze
