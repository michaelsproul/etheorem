import EthCLSpecs.Proofs.Heze.IndexAssignment.Helpers
import EthCLSpecs.Proofs.Heze.Invariants.Block

/-!
# `EthCLSpecs.Proofs.Heze.IndexAssignment.Block`: a Heze block keeps the keys and extends the queue

The Heze counterpart of `Proofs/Gloas/IndexAssignment/Block.lean`. The Heze `processBlock`
(`Heze/Transition.lean:71-79`) is the Gloas one without `process_eth1_data` (EIP-8015). The
execution requests of the parent payload run in `applyParentExecutionPayload`, so
`processParentExecutionPayload` is the block substep that needs the in-block context, as in
Gloas.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze.IndexAssignment

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Heze

/-- Step over a call to a step that keeps the frame inside a block: `h` is the step's fact at
the context in scope. -/
local macro "call_in " h:term : tactic =>
  `(tactic| refine EthCLLib.Proofs.Preserves.run $h (by frame_close) (fun _ _ _ => ?_))

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## Withdrawals -/

omit [Config] [CryptoBackend] in
theorem applyWithdrawals_keepsFrame (ws : Array Withdrawal) :
    KeepsFrame (applyWithdrawals (StateTransition := HezeRun) ws) := by
  intro c v hv
  unfold applyWithdrawals
  run_ensures
  refine (runEnsures_forIn_array_box (StepInv c) _ (fun _ s w hs => ?_) v _ hv).weaken
    (fun b w hb => ?_)
  · run_ensures
    · exact ⟨rfl, _, rfl, by frame_close⟩
    · call_box decreaseBalance_keepsFrame _ _
      run_ensures
      exact ⟨rfl, _, rfl, ‹_›⟩
  · obtain ⟨hw, s', hb, hs'⟩ := hb
    subst hw hb
    run_ensures
    exact hs'

omit [Config] [CryptoBackend] in
theorem processWithdrawals_keepsFrame :
    KeepsFrame (processWithdrawals (StateTransition := HezeRun)) := by
  intro c v hv
  unfold processWithdrawals
  run_ensures
  all_goals try frame_close
  call_ro getExpectedWithdrawals_readsOnly
  run_ensures
  call applyWithdrawals_keepsFrame _
  run_ensures
  all_goals write_split
  all_goals run_ensures
  all_goals frame_close

/-! ## The bid, the parent payload, and the builder requests -/

omit [Config] [CryptoBackend] in
theorem settleBuilderPayment_keepsFrame (i : Nat) :
    KeepsFrame (settleBuilderPayment (StateTransition := HezeRun) i) := by
  intro c v hv
  unfold settleBuilderPayment
  run_ensures
  all_goals frame_close

theorem processExecutionPayloadBid_keepsFrame (sb : SignedExecutionPayloadBid) :
    KeepsFrame (processExecutionPayloadBid (StateTransition := HezeRun) sb) := by
  intro c v hv
  unfold processExecutionPayloadBid
  run_ensures
  all_goals (call_ro getBlockRootAtSlot_readsOnly _ _; run_ensures)
  all_goals (call_ro getRandaoMix_readsOnly _; run_ensures)
  all_goals frame_close

omit [CryptoBackend] in
theorem initiateBuilderExit_keepsFrame (bi : BuilderIndex) :
    KeepsFrame (initiateBuilderExit (StateTransition := HezeRun) bi) := by
  intro c v hv
  unfold initiateBuilderExit
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem addBuilderToRegistry_keepsFrame (pk : BLSPubkey) (ver : UInt8) (addr : ExecutionAddress)
    (amt : Gwei) (slot : Slot) :
    KeepsFrame (addBuilderToRegistry (StateTransition := HezeRun) pk ver addr amt slot) := by
  intro c v hv
  unfold addBuilderToRegistry
  run_ensures
  all_goals frame_close

theorem processBuilderDepositRequest_keepsFrame (r : BuilderDepositRequest) :
    KeepsFrame (processBuilderDepositRequest (StateTransition := HezeRun) r) := by
  intro c v hv
  unfold processBuilderDepositRequest
  run_ensures
  all_goals try frame_close
  run_ensures_beta
  split
  all_goals run_ensures
  all_goals try (call addBuilderToRegistry_keepsFrame _ _ _ _ _; run_ensures)
  all_goals frame_close

omit [CryptoBackend] in
theorem processBuilderExitRequest_keepsFrame (r : BuilderExitRequest) :
    KeepsFrame (processBuilderExitRequest (StateTransition := HezeRun) r) := by
  intro c v hv
  unfold processBuilderExitRequest
  run_ensures
  run_ensures_beta
  split
  all_goals run_ensures
  all_goals try (call initiateBuilderExit_keepsFrame _; run_ensures)
  all_goals frame_close

/-! ## The execution requests and the parent payload -/

omit [Config] [CryptoBackend] in
/-- A deposit request appends one deposit whose slot is the state's slot. The in-block context
admits it through its second arm, `e.slot = c.slot`. -/
theorem processDepositRequest_keepsFrame (dr : DepositRequest) :
    KeepsFrameInBlock (processDepositRequest (StateTransition := HezeRun) dr) := by
  intro c hc v hv
  unfold processDepositRequest
  run_ensures
  exact StepInv.of_push hv _ (by simp [box_reduce]) (by simp [box_reduce])
    (by simp [listSizes, box_reduce]) (by simp only [box_reduce]; rfl)
    ⟨hc, Or.inr hv.1⟩

omit [CryptoBackend] in
theorem processWithdrawalRequest_keepsFrame (wr : WithdrawalRequest) :
    KeepsFrame (processWithdrawalRequest (StateTransition := HezeRun) wr) := by
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
  frame_close

omit [CryptoBackend] in
theorem processConsolidationRequest_keepsFrame (req : ConsolidationRequest) :
    KeepsFrameInBlock (processConsolidationRequest (StateTransition := HezeRun) req) := by
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
  frame_close

theorem applyParentExecutionPayload_keepsFrame (requests : ExecutionRequests) :
    KeepsFrameInBlock (applyParentExecutionPayload (StateTransition := HezeRun) requests) := by
  intro c hc v hv
  unfold applyParentExecutionPayload
  run_ensures
  all_goals try (call settleBuilderPayment_keepsFrame _; run_ensures)
  all_goals
    refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run (by frame_close) (fun _ w hw => ?_)
    · intro w hw; run_ensures; call_in processDepositRequest_keepsFrame _ c hc; run_ensures; frame_close
    run_ensures
    refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
    · intro w hw; run_ensures; call processWithdrawalRequest_keepsFrame _; run_ensures; frame_close
    run_ensures
    refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
    · intro w hw; run_ensures; call_in processConsolidationRequest_keepsFrame _ c hc; run_ensures
      frame_close
    run_ensures
    refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
    · intro w hw; run_ensures; call processBuilderDepositRequest_keepsFrame _; run_ensures
      frame_close
    run_ensures
    refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
    · intro w hw; run_ensures; call processBuilderExitRequest_keepsFrame _; run_ensures
      frame_close
    run_ensures
    frame_close

theorem processParentExecutionPayload_keepsFrame (block : BeaconBlock) :
    KeepsFrameInBlock (processParentExecutionPayload (StateTransition := HezeRun) block) := by
  intro c hc v hv
  unfold processParentExecutionPayload
  run_ensures
  all_goals try frame_close
  call_in applyParentExecutionPayload_keepsFrame _ c hc
  frame_close

/-! ## Attestations and payload attestations -/

theorem processPayloadAttestation_keepsFrame (pa : PayloadAttestation) :
    KeepsFrame (processPayloadAttestation (StateTransition := HezeRun) pa) := by
  intro c v hv
  unfold processPayloadAttestation
  run_ensures
  call_ro getIndexedPayloadAttestation_readsOnly _ _
  run_ensures
  frame_close

omit [Config] in
theorem processAttestation_keepsFrame (att : Attestation) (parentSlot : Slot) :
    KeepsFrame (processAttestation (StateTransition := HezeRun) att parentSlot) := by
  intro c v hv
  unfold processAttestation
  run_ensures
  call_ro getAttestationParticipationFlagIndices_readsOnly _ _ _ _
  run_ensures
  run_ensures_beta
  split
  all_goals run_ensures
  call_ro isAttestationSameSlot_readsOnly _ _
  run_ensures
  refine (runEnsures_forIn_array_boxFst (StepInv c) _ (fun _ s n w hs => ?_) v _ _ hv).weaken
    (fun acc w hacc => ?_)
  · run_ensures
    all_goals refine (runEnsures_forIn_range_boxFst (StepInv c) 3
      (fun _ s' n' w' _ hs' => ?_) s w _ hs).weaken (fun acc' w' hacc' => ?_)
    all_goals first
      | (obtain ⟨b', n''⟩ := acc'
         obtain ⟨hw', s'', hb', hs''⟩ := hacc'
         try simp only at hb'
         subst hw' hb'
         run_ensures
         all_goals exact ⟨rfl, _, rfl, hs''⟩)
      | (run_ensures
         all_goals first
           | exact ⟨rfl, _, rfl, hs'⟩
           | (refine ⟨rfl, ?_⟩
              split_ite
              all_goals first
                | (exfalso; contradiction)
                | exact ⟨_, rfl, by frame_close⟩))
  · obtain ⟨b, n⟩ := acc
    obtain ⟨hw, s', hb, hs'⟩ := hacc
    try simp only at hb
    subst hw hb
    run_ensures
    call_box increaseBalance_keepsFrame _ _
    run_ensures
    frame_close

/-! ## RANDAO, the eth1 vote, the sync aggregate, and the inherited operations -/

omit [Config] in
theorem processRandao_keepsFrame (body : BeaconBlockBody) :
    KeepsFrame (processRandao (StateTransition := HezeRun) body) := by
  intro c v hv
  unfold processRandao
  run_ensures
  frame_close

omit [Config] in
theorem processSyncAggregate_keepsFrame (agg : SyncAggregate) :
    KeepsFrame (processSyncAggregate (StateTransition := HezeRun) agg) := by
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

theorem processProposerSlashing_keepsFrame (ps : ProposerSlashing) :
    KeepsFrame (processProposerSlashing (StateTransition := HezeRun) ps) := by
  intro c v hv
  unfold processProposerSlashing
  run_ensures
  call slashValidator_keepsFrame _
  frame_close

theorem processAttesterSlashing_keepsFrame (asl : AttesterSlashing) :
    KeepsFrame (processAttesterSlashing (StateTransition := HezeRun) asl) := by
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
    KeepsFrame (processVoluntaryExit (StateTransition := HezeRun) sve) := by
  intro c v hv
  unfold processVoluntaryExit
  run_ensures
  call initiateValidatorExit_keepsFrame _
  frame_close

theorem processBlsToExecutionChange_keepsFrame (sbc : SignedBLSToExecutionChange) :
    KeepsFrame (processBlsToExecutionChange (StateTransition := HezeRun) sbc) := by
  intro c v hv
  unfold processBlsToExecutionChange
  run_ensures
  frame_close

theorem processOperations_keepsFrame (body : BeaconBlockBody) (parentSlot : Slot) :
    KeepsFrame (processOperations (StateTransition := HezeRun) body parentSlot) := by
  intro c v hv
  unfold processOperations
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hv (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processProposerSlashing_keepsFrame _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processAttesterSlashing_keepsFrame _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processAttestation_keepsFrame _ _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processVoluntaryExit_keepsFrame _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processBlsToExecutionChange_keepsFrame _; run_ensures; frame_close
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run hw (fun _ w hw => ?_)
  · intro w hw; run_ensures; call processPayloadAttestation_keepsFrame _; run_ensures; frame_close
  run_ensures
  frame_close

omit [Config] [CryptoBackend] in
theorem processBlockHeader_keepsFrame (block : BeaconBlock) :
    KeepsFrame (processBlockHeader (StateTransition := HezeRun) block) := by
  intro c v hv
  unfold processBlockHeader
  run_ensures
  frame_close

/-- A block keeps the in-block frame: the keys, the slot and the finalized epoch stay, and the
queue grows by admitted deposits. `processParentExecutionPayload` is the one substep that
needs the in-block context. -/
theorem processBlock_keepsFrame (block : BeaconBlock) :
    KeepsFrameInBlock (processBlock (StateTransition := HezeRun) block) := by
  intro c hc v hv
  unfold processBlock
  run_ensures
  call_in processParentExecutionPayload_keepsFrame _ c hc
  run_ensures
  call processBlockHeader_keepsFrame _
  run_ensures
  call processWithdrawals_keepsFrame
  run_ensures
  call processExecutionPayloadBid_keepsFrame _
  run_ensures
  call processRandao_keepsFrame _
  run_ensures
  call processOperations_keepsFrame _ _
  run_ensures
  call processSyncAggregate_keepsFrame _
  assumption

end

end EthCLSpecs.Proofs.Heze.IndexAssignment
