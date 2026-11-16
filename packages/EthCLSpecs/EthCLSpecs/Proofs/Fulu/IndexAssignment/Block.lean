import EthCLSpecs.Proofs.Fulu.IndexAssignment.Helpers
import EthCLSpecs.Proofs.Fulu.Invariants.Block

/-!
# `EthCLSpecs.Proofs.Fulu.IndexAssignment.Block`: a block keeps the keys and extends the queue

`processBlock` (`Fulu/Transition.lean:207-214`) never appends a validator, so it keeps the
registry's keys. It keeps the slot and the finalized epoch. It appends to the queue in two
places, and `processBlock_keepsFrame` states both through the in-block frame of `Frame.lean`.

* `processDepositRequest` appends one deposit that carries the state's slot, the slot of the
  block.
* `processConsolidationRequest` can switch a validator to compounding, which queues the
  validator's excess balance under the validator's own key.

Every other block step keeps the frame at every context, by the proofs of
`Proofs/Fulu/Invariants/Block.lean`. The header step writes `latestBlockHeader` alone, so it
is a frame step here.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu.IndexAssignment

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Fulu

/-- Step over a call to a step that keeps the frame inside a block: `h` is the step's fact at
the context in scope. -/
local macro "call_in " h:term : tactic =>
  `(tactic| refine EthCLLib.Proofs.Preserves.run $h (by frame_close) (fun _ _ _ => ?_))

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

omit [Config] [CryptoBackend] in
theorem processWithdrawals_keepsFrame (payload : ExecutionPayload) :
    KeepsFrame (processWithdrawals (StateTransition := FuluRun) payload) := by
  intro c v hv
  unfold processWithdrawals
  run_ensures
  call_ro getExpectedWithdrawals_readsOnly _
  run_ensures
  refine (runEnsures_forIn_array_box (StepInv c) _ (fun _ s w hs => ?_) v _ hv).weaken
    (fun b w hb => ?_)
  · run_ensures
    call_box decreaseBalance_keepsFrame _ _
    run_ensures
    exact ⟨rfl, _, rfl, ‹_›⟩
  · obtain ⟨hw, s', hb, hs'⟩ := hb
    subst hw hb
    run_ensures
    all_goals frame_close

/-! ## Payload, RANDAO, eth1 vote, sync aggregate -/

omit [CryptoBackend] in
theorem processExecutionPayload_keepsFrame (body : BeaconBlockBody) :
    KeepsFrame (processExecutionPayload (StateTransition := FuluRun) body) := by
  intro c v hv
  unfold processExecutionPayload
  run_ensures
  frame_close

omit [Config] in
theorem processRandao_keepsFrame (body : BeaconBlockBody) :
    KeepsFrame (processRandao (StateTransition := FuluRun) body) := by
  intro c v hv
  unfold processRandao
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processEth1Data_keepsFrame (body : BeaconBlockBody) :
    KeepsFrame (processEth1Data (StateTransition := FuluRun) body) := by
  intro c v hv
  unfold processEth1Data
  run_ensures
  append_split
  all_goals run_ensures
  all_goals frame_close

omit [Config] in
theorem processSyncAggregate_keepsFrame (agg : SyncAggregate) :
    KeepsFrame (processSyncAggregate (StateTransition := FuluRun) agg) := by
  intro c v hv
  unfold processSyncAggregate
  run_ensures
  call_ro getBlockRootAtSlot_readsOnly _ _
  run_ensures
  refine (runEnsures_forIn'_range_inv _ (BoxInv (StepInv c) _)
    (fun _ _ b w hb => ?_) _ ⟨rfl, v, rfl, hv⟩).weaken (fun b w hb => ?_)
  · obtain ⟨hw, s, hb, hs⟩ := hb
    subst hw hb
    run_ensures
    run_ensures_beta
    split
    · run_ensures
      · call_box increaseBalance_keepsFrame _ _
        run_ensures
        call_box increaseBalance_keepsFrame _ _
        run_ensures
        exact ⟨rfl, _, rfl, ‹_›⟩
      · call_box decreaseBalance_keepsFrame _ _
        run_ensures
        exact ⟨rfl, _, rfl, ‹_›⟩
    · run_ensures
      exact ⟨rfl, _, rfl, hs⟩
  · obtain ⟨hw, s, hb, hs⟩ := hb
    subst hw hb
    run_ensures
    exact hs

/-! ## Operations -/

omit [Config] in
theorem processAttestation_keepsFrame (att : Attestation) :
    KeepsFrame (processAttestation (StateTransition := FuluRun) att) := by
  intro c v hv
  unfold processAttestation
  run_ensures
  call_ro getAttestationParticipationFlagIndices_readsOnly _ _ _
  run_ensures
  run_ensures_beta
  split
  all_goals run_ensures
  refine (runEnsures_forIn_array_boxFst (StepInv c) _ (fun _ s n w hs => ?_) v _ 0 hv).weaken
    (fun acc w hacc => ?_)
  · run_ensures
    refine (runEnsures_forIn_range_boxFst (StepInv c) 3 (fun _ s' n' w' _ hs' => ?_) s w n hs).weaken
      (fun acc' w' hacc' => ?_)
    · run_ensures
      all_goals first
        | exact ⟨rfl, _, rfl, hs'⟩
        | (refine ⟨rfl, ?_⟩
           split_ite
           all_goals first
             | (exfalso; contradiction)
             | exact ⟨_, rfl, by frame_close⟩)
    · obtain ⟨b', n''⟩ := acc'
      obtain ⟨hw', s'', hb', hs''⟩ := hacc'
      try simp only at hb'
      subst hw' hb'
      run_ensures
      exact ⟨rfl, _, rfl, hs''⟩
  · obtain ⟨b, n⟩ := acc
    obtain ⟨hw, s', hb, hs'⟩ := hacc
    try simp only at hb
    subst hw hb
    run_ensures
    call_box increaseBalance_keepsFrame _ _
    run_ensures
    frame_close

theorem processProposerSlashing_keepsFrame (ps : ProposerSlashing) :
    KeepsFrame (processProposerSlashing (StateTransition := FuluRun) ps) := by
  intro c v hv
  unfold processProposerSlashing
  run_ensures
  call slashValidator_keepsFrame _
  frame_close

theorem processAttesterSlashing_keepsFrame (asl : AttesterSlashing) :
    KeepsFrame (processAttesterSlashing (StateTransition := FuluRun) asl) := by
  intro c v hv
  unfold processAttesterSlashing
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ w hw => ?_)).run hv (fun _ w hw => ?_)
  · run_ensures
    · call slashValidator_keepsFrame _
      run_ensures
      frame_close
    · frame_close
  · run_ensures
    frame_close

theorem processVoluntaryExit_keepsFrame (sve : SignedVoluntaryExit) :
    KeepsFrame (processVoluntaryExit (StateTransition := FuluRun) sve) := by
  intro c v hv
  unfold processVoluntaryExit
  run_ensures
  call initiateValidatorExit_keepsFrame _
  frame_close

theorem processBlsToExecutionChange_keepsFrame (sbc : SignedBLSToExecutionChange) :
    KeepsFrame (processBlsToExecutionChange (StateTransition := FuluRun) sbc) := by
  intro c v hv
  unfold processBlsToExecutionChange
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
/-- A deposit request appends one deposit whose slot is the state's slot. The in-block context
admits it through its second arm, `e.slot = c.slot`. -/
theorem processDepositRequest_keepsFrame (dr : DepositRequest) :
    KeepsFrameInBlock (processDepositRequest (StateTransition := FuluRun) dr) := by
  intro c hc v hv
  unfold processDepositRequest
  run_ensures
  append_split
  all_goals run_ensures
  exact StepInv.of_push hv _ (by simp [box_reduce]) (by simp [box_reduce])
    (by simp [listSizes, box_reduce]) (by simp only [box_reduce]; assumption)
    ⟨hc, Or.inr hv.1⟩

omit [CryptoBackend] in
theorem processWithdrawalRequest_keepsFrame (wr : WithdrawalRequest) :
    KeepsFrame (processWithdrawalRequest (StateTransition := FuluRun) wr) := by
  intro c v hv
  unfold processWithdrawalRequest
  run_ensures
  all_goals try frame_close
  run_ensures_beta
  split
  all_goals run_ensures
  all_goals try frame_close
  all_goals try (call initiateValidatorExit_keepsFrame _; run_ensures; frame_close)
  call computeExitEpochAndUpdateChurn_keepsFrame _
  run_ensures
  append_split
  all_goals run_ensures
  all_goals frame_close

omit [CryptoBackend] in
theorem processConsolidationRequest_keepsFrame (req : ConsolidationRequest) :
    KeepsFrameInBlock (processConsolidationRequest (StateTransition := FuluRun) req) := by
  intro c hc v hv
  unfold processConsolidationRequest
  run_ensures
  all_goals try frame_close
  all_goals (run_ensures_beta; split)
  all_goals run_ensures
  all_goals try frame_close
  all_goals try (call_in switchToCompoundingValidator_keepsFrame _ c hc; run_ensures; frame_close)
  call computeConsolidationEpochAndUpdateChurn_keepsFrame _
  run_ensures
  append_split
  all_goals run_ensures
  all_goals frame_close

theorem processOperations_keepsFrame (body : BeaconBlockBody) :
    KeepsFrameInBlock (processOperations (StateTransition := FuluRun) body) := by
  intro c hc v hv
  unfold processOperations
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hv (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processProposerSlashing_keepsFrame _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processAttesterSlashing_keepsFrame _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processAttestation_keepsFrame _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processVoluntaryExit_keepsFrame _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processBlsToExecutionChange_keepsFrame _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call_in processDepositRequest_keepsFrame _ c hc; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processWithdrawalRequest_keepsFrame _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call_in processConsolidationRequest_keepsFrame _ c hc; run_ensures; frame_close
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processBlockHeader_keepsFrame (block : BeaconBlock) :
    KeepsFrame (processBlockHeader (StateTransition := FuluRun) block) := by
  intro c v hv
  unfold processBlockHeader
  run_ensures
  frame_close

/-- A block keeps the in-block frame: the keys, the slot and the finalized epoch stay, and the
queue grows by admitted deposits. `processOperations` is the one substep that needs the
in-block context. -/
theorem processBlock_keepsFrame (block : BeaconBlock) :
    KeepsFrameInBlock (processBlock (StateTransition := FuluRun) block) := by
  intro c hc v hv
  unfold processBlock
  run_ensures
  call processBlockHeader_keepsFrame _
  run_ensures
  call processWithdrawals_keepsFrame _
  run_ensures
  call processExecutionPayload_keepsFrame _
  run_ensures
  call processRandao_keepsFrame _
  run_ensures
  call processEth1Data_keepsFrame _
  run_ensures
  call_in processOperations_keepsFrame _ c hc
  run_ensures
  call processSyncAggregate_keepsFrame _
  assumption

end

end EthCLSpecs.Proofs.Fulu.IndexAssignment
