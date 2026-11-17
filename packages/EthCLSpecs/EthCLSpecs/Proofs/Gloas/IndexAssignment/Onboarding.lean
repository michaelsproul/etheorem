import EthCLSpecs.Proofs.Gloas.IndexAssignment.Block
import EthCLSpecs.Proofs.Gloas.IndexAssignment.Deposits

/-!
# `EthCLSpecs.Proofs.Gloas.IndexAssignment.Onboarding`: what the builder onboarding does to the queue

`onboardBuildersFromPendingDeposits` (`Gloas/Operations.lean`) runs once, in the second half
of the Gloas upgrade. It is the one Gloas step that takes deposits out of the middle of the
pending-deposit queue. This module states what the step leaves.

## The contract

The step keeps the slot, the finalized epoch and the registry's keys. It replaces the queue,
and `onboardBuildersFromPendingDeposits_ensures` states the new queue through one filter:

* read the old queue and the new queue through `depositValid`, the proof-of-possession check;
* the new one is the old one without the deposits `Onboardable` names.

`Onboardable cutoff d` says `d` carries builder withdrawal credentials and a slot above the
cutoff. The step makes a builder from each such deposit with a valid signature, so none stays
queued. It keeps every deposit that is not `Onboardable`.

The contract says nothing about a deposit with an invalid signature. The step keeps some and
drops others, by the registry and the deposits it kept before. Such a deposit never adds a
validator (`DepositQueue.stepKeys_of_not_valid`), so the index assignment does not read it.
That is why the contract needs no fact about the builder registry.

## The loop invariant

The loop carries `kept`, the deposits it keeps, and walks the old queue. With `rest` the part
still to walk, the invariant is one list equation:

    kept.filter depositValid ++ rest.filter (StaysValid cutoff) = queue.filter (StaysValid cutoff)

`StaysValid cutoff d` is `depositValid d` and not `Onboardable cutoff d`. Each iteration moves
the head of `rest` across: `onboardingInv_push` for a deposit the step keeps, and
`onboardingInv_skip` for one it takes out or drops.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas.IndexAssignment

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Gloas

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## The onboarding cutoff and the two filters -/

/-- The onboarding cutoff the step computes at the state `v`: the first slot of the epoch two
before the current one, and slot `0` in the first two epochs. -/
def onboardingCutoff (v : BeaconState) : Slot :=
  computeStartSlotAtEpoch (max (computeEpochAtSlot v.slot) 2 - 2)

/-- A deposit the onboarding can make a builder from: it carries builder withdrawal
credentials, and its slot is above the cutoff. -/
def Onboardable (cutoff : Slot) (d : PendingDeposit) : Bool :=
  isBuilderWithdrawalCredential d.withdrawalCredentials && decide (cutoff < d.slot)

/-- A deposit with a valid signature that the onboarding leaves in the queue. -/
def StaysValid (cutoff : Slot) (d : PendingDeposit) : Bool :=
  depositValid d && !Onboardable cutoff d

/-- The invariant after a kept deposit `d`. The hypothesis says the two filters agree on `d`:
it is not `Onboardable`, or its signature is invalid. -/
theorem onboardingInv_push {cutoff : Slot} {kept : Array PendingDeposit} {d : PendingDeposit}
    {rest F : List PendingDeposit}
    (h : kept.toList.filter depositValid ++ (d :: rest).filter (StaysValid cutoff) = F)
    (hd : depositValid d = StaysValid cutoff d) :
    (kept.push d).toList.filter depositValid ++ rest.filter (StaysValid cutoff) = F := by
  rw [← h, Array.toList_push, List.filter_append, List.append_assoc]
  congr 1
  simp only [List.filter_cons, List.filter_nil, hd]
  split <;> rfl

/-- The invariant after a deposit `d` the step does not keep. The hypothesis says the filter
drops `d` too: it is `Onboardable`, or its signature is invalid. -/
theorem onboardingInv_skip {cutoff : Slot} {kept : Array PendingDeposit} {d : PendingDeposit}
    {rest F : List PendingDeposit}
    (h : kept.toList.filter depositValid ++ (d :: rest).filter (StaysValid cutoff) = F)
    (hd : StaysValid cutoff d = false) :
    kept.toList.filter depositValid ++ rest.filter (StaysValid cutoff) = F := by
  rw [← h, List.filter_cons, hd]
  rfl

/-! ## The step -/

/-- A builder deposit keeps the frame: it tops up a builder or appends one, and both write the
builder registry alone. The proof is the one of `applyDepositForBuilder_keepsCore`
(`Proofs/Gloas/ReachableInvariants.lean`), run against the deposit frame. -/
theorem applyDepositForBuilder_keepsFrame (pk : BLSPubkey) (wc : Bytes32) (amt : Gwei)
    (sig : BLSSignature) (slot : Slot) :
    KeepsFrame (applyDepositForBuilder (StateTransition := GloasRun) pk wc amt sig slot) := by
  intro c v hv
  unfold applyDepositForBuilder
  run_ensures
  run_ensures_beta
  split
  all_goals run_ensures
  all_goals try (call addBuilderToRegistry_keepsFrame _ _ _ _ _; run_ensures)
  all_goals frame_close

/-- The builder onboarding keeps the slot, the finalized epoch and the keys, moves the
eligibility epochs by `EligStep`, and leaves the queue the module docstring describes: read
through `depositValid`, the new queue is the old one without the `Onboardable` deposits. -/
theorem onboardBuildersFromPendingDeposits_ensures (v : BeaconState) (hr : RegistrySizes v) :
    RunEnsures v (onboardBuildersFromPendingDeposits (StateTransition := GloasRun))
      (fun _ w => w.slot = v.slot ∧
        w.finalizedCheckpoint.epoch = v.finalizedCheckpoint.epoch ∧
        registryKeys w = registryKeys v ∧
        EligStep v.slot (registryElig v) (registryElig w) ∧
        w.pendingDeposits.val.toList.filter depositValid
          = v.pendingDeposits.val.toList.filter (StaysValid (onboardingCutoff v))) := by
  unfold onboardBuildersFromPendingDeposits
  run_ensures
  refine (runEnsures_forIn_array
    (fun rest (kept : Array PendingDeposit) w => StepInv (Ctx.of v false) w ∧
      kept.toList.filter depositValid ++ rest.filter (StaysValid (onboardingCutoff v))
        = v.pendingDeposits.val.toList.filter (StaysValid (onboardingCutoff v)))
    (fun (kept : Array PendingDeposit) w => StepInv (Ctx.of v false) w ∧
      kept.toList.filter depositValid
        = v.pendingDeposits.val.toList.filter (StaysValid (onboardingCutoff v)))
    (fun d rest kept w hI => ?_) (fun kept w hI => ⟨hI.1, by simpa using hI.2⟩) _ _
    ⟨StepInv.start v false hr, rfl⟩).weaken fun kept w hI => ?_
  · -- One iteration, at the deposit `d`. The five leaves are the five ways the body ends.
    obtain ⟨hw, hinv⟩ := hI
    run_ensures
    · -- No builder credentials: `d` stays, and it is not `Onboardable`.
      rename_i hcred
      have hcred' : isBuilderWithdrawalCredential d.withdrawalCredentials = false := by
        simpa using hcred
      exact ⟨hw, onboardingInv_push hinv (by simp [StaysValid, Onboardable, hcred'])⟩
    · -- A slot at or below the cutoff: `d` stays, and it is not `Onboardable`. The guard reads
      -- `currentEpochOf (pureState v)`, which unfolds to the epoch `onboardingCutoff` names.
      rename_i hslot
      have hle : d.slot ≤ onboardingCutoff v := hslot
      have hlt : ¬ onboardingCutoff v < d.slot := UInt64.not_lt.mpr hle
      exact ⟨hw, onboardingInv_push hinv (by simp [StaysValid, Onboardable, hlt])⟩
    · -- The deposit funds a builder: the step takes it out, and it is `Onboardable`.
      rename_i hcred hslot _
      have hcred' : isBuilderWithdrawalCredential d.withdrawalCredentials = true := by
        simpa using hcred
      have hlt : onboardingCutoff v < d.slot := UInt64.not_le.mp hslot
      refine (applyDepositForBuilder_keepsFrame _ _ _ _ _ _ w hw).weaken fun _ w' hw' => ?_
      run_ensures
      exact ⟨hw', onboardingInv_skip hinv (by simp [StaysValid, Onboardable, hcred', hlt])⟩
    · -- An invalid signature, kept as a top-up: neither filter keeps `d`.
      rename_i hfund _
      have hvalid : depositValid d = false := by
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hfund
        exact hfund.2
      exact ⟨hw, onboardingInv_push hinv (by simp [StaysValid, hvalid])⟩
    · -- An invalid signature, dropped: the filter drops `d` too.
      rename_i hfund _
      have hvalid : depositValid d = false := by
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hfund
        exact hfund.2
      exact ⟨hw, onboardingInv_skip hinv (by simp [StaysValid, hvalid])⟩
  · -- The last write replaces the queue by `kept`, and it writes no other field.
    obtain ⟨hw, hinv⟩ := hI
    run_ensures
    obtain ⟨hs, hf, hk, -, -, he⟩ := hw
    simp only [Ctx.of] at hs hf hk he
    exact ⟨by simp only [box_reduce]; exact hs, by simp only [box_reduce]; exact hf,
      by simp only [registryKeys, box_reduce]; exact hk,
      by simp only [registryElig, box_reduce]; exact he,
      by simp only [box_reduce]; exact hinv⟩

/-- The second half of the upgrade has the contract of the builder onboarding. The PTC window
write comes first, and it touches no value the contract reads, so the contract at the state
after that write is the contract at `v`. -/
theorem completeUpgradeToGloas_ensures (v : BeaconState) (hr : RegistrySizes v) :
    RunEnsures v (completeUpgradeToGloas (StateTransition := GloasRun))
      (fun _ w => w.slot = v.slot ∧
        w.finalizedCheckpoint.epoch = v.finalizedCheckpoint.epoch ∧
        registryKeys w = registryKeys v ∧
        EligStep v.slot (registryElig v) (registryElig w) ∧
        w.pendingDeposits.val.toList.filter depositValid
          = v.pendingDeposits.val.toList.filter (StaysValid (onboardingCutoff v))) := by
  unfold completeUpgradeToGloas
  run_ensures
  exact onboardBuildersFromPendingDeposits_ensures _ hr

end

end EthCLSpecs.Proofs.Gloas.IndexAssignment
