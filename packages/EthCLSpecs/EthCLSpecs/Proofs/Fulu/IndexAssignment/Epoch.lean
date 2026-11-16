import EthCLSpecs.Proofs.Fulu.IndexAssignment.Helpers
import EthCLSpecs.Proofs.Fulu.Invariants.Epoch

/-!
# `EthCLSpecs.Proofs.Fulu.IndexAssignment.Epoch`: the epoch substeps keep the deposit frame

`processEpoch` (`Fulu/Transition.lean:53-68`) runs fifteen substeps. Thirteen keep the frame
of `Frame.lean`, at every context: they write balances, validator records, scores, mixes and
committees, and none writes a `pubkey`, the queue, the slot or the finalized checkpoint. The
proofs are those of `Proofs/Fulu/Invariants/Epoch.lean`, run against this namespace's
`StepInv`.

The other two have their own facts. `processJustificationAndFinalization` writes the finalized
checkpoint (`Slots.lean`). `processPendingDeposits` consumes the queue and appends keys
(`Deposits.lean`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu.IndexAssignment

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Fulu

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [CryptoBackend] in
theorem processInactivityUpdates_keepsFrame :
    KeepsFrame (processInactivityUpdates (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processInactivityUpdates
  run_ensures
  all_goals try frame_close
  refine runEnsures_modifyThe (pureState_forIn_array_inv (StepInv c)
    (by intro _ _ _; exact ⟨_, rfl, by frame_close⟩) _ _ hv)

omit [Config] [CryptoBackend] in
theorem applyDeltas_keepsFrame (rewards penalties : Array Gwei) {c : Ctx}
    {s v : BeaconState} (hs : StepInv c s) :
    RunEnsures v (applyDeltas (StateTransition := FuluRun) rewards penalties (pureState s))
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
    KeepsFrame (processRewardsAndPenalties (StateTransition := FuluRun)) := by
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
    KeepsFrame (processRegistryUpdates (StateTransition := FuluRun)) := by
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
         <;> simp [coreFields, listSizes, box_reduce]
         <;> done)
      | frame_close
  · run_ensures
    exact h

omit [Config] [CryptoBackend] in
theorem processSlashings_keepsFrame :
    KeepsFrame (processSlashings (StateTransition := FuluRun)) := by
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
theorem processEth1DataReset_keepsFrame :
    KeepsFrame (processEth1DataReset (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processEth1DataReset
  run_ensures
  call_ro getCurrentEpoch_readsOnly
  run_ensures
  all_goals frame_close

omit [Config] [CryptoBackend] in
theorem pcLoop_keepsFrame (cons : Array PendingConsolidation) (nextEpoch : Epoch) :
    KeepsFrame (pcLoop (StateTransition := FuluRun) cons nextEpoch) := by
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
    KeepsFrame (processPendingConsolidations (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processPendingConsolidations
  run_ensures
  call pcLoop_keepsFrame _ _
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processEffectiveBalanceUpdates_keepsFrame :
    KeepsFrame (processEffectiveBalanceUpdates (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processEffectiveBalanceUpdates
  refine runEnsures_modifyThe (pureState_forIn_range_inv (StepInv c)
    (by intro _ _ _; dsimp only; split <;> exact ⟨_, rfl, by frame_close⟩) _ _ hv)

omit [Config] [CryptoBackend] in
theorem processSlashingsReset_keepsFrame :
    KeepsFrame (processSlashingsReset (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processSlashingsReset
  run_ensures
  call_ro getCurrentEpoch_readsOnly
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processRandaoMixesReset_keepsFrame :
    KeepsFrame (processRandaoMixesReset (StateTransition := FuluRun)) := by
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
    KeepsFrame (processHistoricalSummariesUpdate (StateTransition := FuluRun)) := by
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
    KeepsFrame (processParticipationFlagUpdates (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processParticipationFlagUpdates
  run_ensures
  rename_i l hl
  refine hv.of_parts (by simp only [coreFields, box_reduce])
    (by simp only [registryKeys, box_reduce]) (by simp only [registryElig, box_reduce]) ?_
  obtain ⟨hb, hi, hp, hq⟩ := hv.registrySizes
  simp only [RegistrySizes, SizzLean.Repr.SSZList.size, box_reduce]
  simp only [SizzLean.Repr.SSZList.size] at hb hi hp hq
  refine ⟨hb, hi, hq, ?_⟩
  rw [hl]
  simp

omit [Config] in
theorem processSyncCommitteeUpdates_keepsFrame :
    KeepsFrame (processSyncCommitteeUpdates (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processSyncCommitteeUpdates
  run_ensures
  all_goals frame_close

omit [Config] [CryptoBackend] in
theorem processProposerLookahead_keepsFrame :
    KeepsFrame (processProposerLookahead (StateTransition := FuluRun)) := by
  intro c v hv
  unfold processProposerLookahead
  run_ensures
  frame_close

end

end EthCLSpecs.Proofs.Fulu.IndexAssignment
