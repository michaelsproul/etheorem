import EthCLSpecs.Proofs.Fulu.IndexAssignment.Helpers
import EthCLSpecs.Proofs.DepositQueue

/-!
# `EthCLSpecs.Proofs.Fulu.IndexAssignment.Deposits`: the contract of the pending-deposit scan

`processPendingDeposits` (`Fulu/EpochProcessing.lean:271-283`) is the one step of the Fulu
state transition that changes the registry's keys. This module states what it does to the
keys and to the queue, in the terms of `Proofs/DepositQueue.lean`:

`processPendingDeposits_ensures` gives a `Scan` from the start to the end. The step consumes a
prefix of the queue. Each consumed deposit has a slot at or below the finalized slot, and
moves the key list by `stepKeys`. The new queue is the rest of the old one, then the
postponed deposits, and each of those names a key the registry holds.

## The three layers

* `addValidatorToRegistry_ensures`: the registry append adds the deposit's key at the end of
  the key list. On a state whose registry sizes agree, each `set_or_append_list` takes its
  append branch, as in `Proofs/Fulu/Invariants/Helpers.lean`.
* `applyPendingDeposit_ensures`: one applied deposit moves the key list by `stepKeys`. The
  registry lookup decides between a top-up and a new key, and `depositValid` is the
  proof-of-possession check a new key must pass.
* `ppdLoop_ensures`: the loop `ppdLoop` (`Fulu/EpochProcessing.lean:234-267`) keeps
  `ScanInv`. A postponed deposit comes from the lookup's `some` arm, so its key is in the
  registry.

Each layer also states what it does to the eligibility epochs. A new validator adds
`FAR_FUTURE_EPOCH` at the end, and no other entry changes (`EligExt`).

## The fuel

`ppdLoop` is a `fuelLoop` with fuel `deposits.size + 1`, and its `exhausted` value is the empty
scan. The contract must rule that value out, because an empty scan after applied deposits
would describe the wrong queue. `runEnsures_fuelLoop_fuel` reads the fuel left: each `next`
moves the cursor on by one, so the cursor passes the queue's end before the fuel runs out,
and the size guard has returned `done` by then.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu.IndexAssignment

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Fulu
open EthCLSpecs.Proofs.DepositQueue

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

section RegistryAppend

/-- Inside this section the walk's `if` rule refutes a branch guard against every hypothesis,
as in `Proofs/Fulu/Invariants/Helpers.lean`. -/
local macro_rules
  | `(tactic| run_ensures_step) =>
    `(tactic| (with_reducible refine runEnsures_ite (fun hc => ?_) (fun hc => ?_))
              <;> try (simp [*, box_reduce] at hc; done))

omit [Config] [CryptoBackend] in
/-- The registry append keeps the core values and adds `pk` at the end of the key list. The
five writes each take the append branch, so the registry sizes still agree. The key of
`getValidatorFromDeposit pk wc amt` is `pk`, and its `activation_eligibility_epoch` is
`FAR_FUTURE_EPOCH`, both by `rfl`. -/
theorem addValidatorToRegistry_ensures (pk : BLSPubkey) (wc : Bytes32) (amt : Gwei)
    (v : BeaconState) (hr : RegistrySizes v) :
    RunEnsures v (addValidatorToRegistry (StateTransition := FuluRun) pk wc amt)
      (fun _ w => coreFields w = coreFields v ∧ registryKeys w = (registryKeys v).push pk ∧
        RegistrySizes w ∧ registryElig w = (registryElig v).push Const.farFutureEpoch) := by
  obtain ⟨hb, hi, hp, hq⟩ := hr
  simp only [SizzLean.Repr.SSZList.size] at hb hi hp hq
  unfold addValidatorToRegistry
  run_ensures
  append_split <;> run_ensures
  rename_i hval _ _
  iterate 4 (all_goals (try (append_split <;> run_ensures)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [coreFields, box_reduce]
  · simp only [registryKeys, box_reduce]
    rw [hval, Array.map_push]
    rfl
  · simp only [RegistrySizes, SizzLean.Repr.SSZList.size, box_reduce]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · simp only [registryElig, box_reduce]
    rw [hval, Array.map_push]
    rfl

end RegistryAppend

/-- The proof-of-possession check `apply_pending_deposit` runs on a deposit for a new key. -/
def depositValid (d : PendingDeposit) : Bool :=
  isValidDepositSignature d.pubkey d.withdrawalCredentials d.amount d.signature

omit [Config] [CryptoBackend] in
/-- A registry lookup that finds an index finds the key in the key list. -/
theorem mem_keys_of_lookup_some {v : BeaconState} {pk : BLSPubkey} {vi : Nat}
    (h : validatorIndexByPubkey? (pureState v) pk = some vi) : pk ∈ (registryKeys v).toList := by
  have h' : v.validators.val.findIdx? (fun x => x.pubkey == pk) = some vi := h
  obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h'
  rw [Array.mem_toList_iff]
  exact Array.mem_map.mpr ⟨_, Array.getElem_mem hlt, beq_iff_eq.mp hp⟩

omit [Config] [CryptoBackend] in
/-- A registry lookup that finds no index means the key list does not hold the key. -/
theorem not_mem_keys_of_lookup_none {v : BeaconState} {pk : BLSPubkey}
    (h : validatorIndexByPubkey? (pureState v) pk = none) : pk ∉ (registryKeys v).toList := by
  have h' : v.validators.val.findIdx? (fun x => x.pubkey == pk) = none := h
  intro hmem
  rw [Array.mem_toList_iff] at hmem
  obtain ⟨x, hx, hxk⟩ := Array.mem_map.mp hmem
  have := Array.findIdx?_eq_none_iff.mp h' x hx
  rw [hxk] at this
  simp at this

/-- One applied deposit keeps the core values and moves the key list by `stepKeys`. A deposit
for a held key is a top-up, a balance write. A deposit for a new key appends the key when
`depositValid` holds, and does nothing otherwise. The eligibility epochs grow by
`FAR_FUTURE_EPOCH` for a new validator and stay otherwise (`EligExt`). -/
theorem applyPendingDeposit_ensures (d : PendingDeposit) (v : BeaconState)
    (hr : RegistrySizes v) :
    RunEnsures v (applyPendingDeposit (StateTransition := FuluRun) d)
      (fun _ w => coreFields w = coreFields v ∧
        (registryKeys w).toList
          = stepKeys (fun e : PendingDeposit => e.pubkey) depositValid (registryKeys v).toList d ∧
        RegistrySizes w ∧ EligExt (registryElig v) (registryElig w)) := by
  unfold applyPendingDeposit
  run_ensures
  split
  · rename_i vi hfind
    have hmem := mem_keys_of_lookup_some hfind
    run_ensures
    refine RunEnsures.weaken (increaseBalance_ensures _ _ _ _) (fun _ _ hbox => ?_)
    obtain ⟨hst, s', hb, hf⟩ := hbox
    subst hst hb
    run_ensures
    have hk : registryKeys s' = registryKeys _ := congrArg Prod.fst hf.2
    exact ⟨hf.1, by rw [hk, stepKeys_of_mem _ _ hmem], registrySizes_of_listSizes hf.2 hr,
      EligExt.of_eq (registryElig_of_listSizes hf.2)⟩
  · rename_i hfind
    have hnot := not_mem_keys_of_lookup_none hfind
    run_ensures
    · rename_i hvalid
      refine (addValidatorToRegistry_ensures _ _ _ v hr).weaken fun _ w ⟨hc, hk, hr', he⟩ =>
        ⟨hc, ?_, hr', he ▸ EligExt.push _⟩
      rw [hk, Array.toList_push]
      simp [stepKeys, hnot, depositValid, hvalid]
    · rename_i hinvalid
      exact ⟨trivial, by simp [stepKeys, hnot, depositValid, hinvalid], hr, EligExt.refl _⟩

/-- The invariant of the queue scan `ppdLoop`, between the start state `v` and the scan's
current accumulator `s` and state `x`. `s.ndi` is the cursor: the scan has consumed the first
`s.ndi` deposits. The keys of `x` are the start's keys moved by those deposits, each of which
has a finalized slot. A postponed deposit names a held key. The core values stay, since the
scan writes the queue only after the loop. The eligibility epochs of `x` extend those of `v`
by `FAR_FUTURE_EPOCH` entries. -/
structure ScanInv (deposits : Array PendingDeposit) (finalizedSlot : Slot) (v : BeaconState)
    (s : DepositScan) (x : BeaconState) : Prop where
  ndiLe : s.ndi ≤ deposits.size
  core : coreFields x = coreFields v
  keys : (registryKeys x).toList
    = keysAfter (fun e : PendingDeposit => e.pubkey) depositValid (registryKeys v).toList
        (deposits.toList.take s.ndi)
  postponed : ∀ e ∈ s.postpone.toList, e.pubkey ∈ (registryKeys x).toList
  finalized : ∀ e ∈ deposits.toList.take s.ndi, e.slot ≤ finalizedSlot
  sizes : RegistrySizes x
  elig : EligExt (registryElig v) (registryElig x)

/-- One more consumed deposit: the cursor moves on, and the key list moves by `stepKeys` at the
deposit under the cursor. `List.take_add_one` splits the consumed prefix at that deposit. -/
theorem ScanInv.advance {deposits : Array PendingDeposit} {finalizedSlot : Slot}
    {v w w' : BeaconState} {s : DepositScan} (hI : ScanInv deposits finalizedSlot v s w)
    (hlt : s.ndi < deposits.size) (hfin : (deposits[s.ndi]!).slot ≤ finalizedSlot)
    (hcore : coreFields w' = coreFields w)
    (hkeys : (registryKeys w').toList
      = stepKeys (fun e : PendingDeposit => e.pubkey) depositValid (registryKeys w).toList
          (deposits[s.ndi]!))
    (hr : RegistrySizes w') (helig : EligExt (registryElig w) (registryElig w'))
    (processed : Gwei) (postpone : Array PendingDeposit)
    (hpost : ∀ e ∈ postpone.toList, e.pubkey ∈ (registryKeys w').toList) :
    ScanInv deposits finalizedSlot v
      { s with ndi := s.ndi + 1, processed := processed, postpone := postpone } w' := by
  have hd : deposits.toList[s.ndi]? = some (deposits[s.ndi]!) := by
    simp [getElem!_pos, hlt]
  have htake : deposits.toList.take (s.ndi + 1)
      = deposits.toList.take s.ndi ++ [deposits[s.ndi]!] := by
    rw [List.take_add_one, hd]; rfl
  refine ⟨hlt, hcore.trans hI.core, ?_, hpost, ?_, hr, hI.elig.trans helig⟩
  · show _ = keysAfter _ _ _ (deposits.toList.take (s.ndi + 1))
    rw [htake, keysAfter_append, ← hI.keys, hkeys]
    rfl
  · show ∀ e ∈ deposits.toList.take (s.ndi + 1), _
    rw [htake]
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact hI.finalized e h
    · rw [List.mem_singleton.mp h]; exact hfin

/-- The scan keeps `ScanInv`. The four continuing branches are the withdrawn validator (apply),
the exiting validator (postpone), and the two sides of the churn check (stop, or apply). The
fuel-indexed invariant adds `deposits.size + 1 ≤ s.ndi + n`, which no state satisfies at
`n = 0`. -/
theorem ppdLoop_ensures (deposits : Array PendingDeposit) (finalizedSlot avail : Gwei)
    (nextEpoch : Epoch) (v : BeaconState) (hr : RegistrySizes v) :
    RunEnsures v (ppdLoop (StateTransition := FuluRun) deposits finalizedSlot avail nextEpoch)
      (fun s w => ScanInv deposits finalizedSlot v s w) := by
  unfold ppdLoop
  refine runEnsures_fuelLoop_fuel
    (I := fun n s w => ScanInv deposits finalizedSlot v s w ∧ deposits.size + 1 ≤ s.ndi + n)
    (Q := fun s w => ScanInv deposits finalizedSlot v s w) ?step ?ex _ _ v ⟨?init, by simp⟩
  case ex =>
    intro b w ⟨hI, hn⟩
    exfalso
    have := hI.ndiLe
    omega
  case init =>
    exact ⟨Nat.zero_le _, rfl, by simp [keysAfter], by simp, by simp, hr, EligExt.refl _⟩
  case step =>
    intro n s w ⟨hI, hn⟩
    run_ensures
    all_goals try exact hI
    all_goals have hlt : s.ndi < deposits.size := Nat.lt_of_not_ge (by assumption)
    all_goals have hfin : (deposits[s.ndi]!).slot ≤ finalizedSlot :=
      UInt64.not_lt.mp (by assumption)
    · refine (applyPendingDeposit_ensures _ w hI.sizes).weaken fun _ w' h => ?_
      obtain ⟨hc', hk, hr', he'⟩ := h
      run_ensures
      refine ⟨hI.advance hlt hfin hc' hk hr' he' _ _ fun e he => ?_, by simp only; omega⟩
      rw [hk]
      exact (prefix_stepKeys _ _ _ _).subset (hI.postponed e he)
    · rename_i hexited
      have hmem : (deposits[s.ndi]!).pubkey ∈ (registryKeys w).toList := by
        cases hlook : validatorIndexByPubkey? (pureState w) (deposits[s.ndi]!).pubkey with
        | none => rw [hlook] at hexited; simp at hexited
        | some vi => exact mem_keys_of_lookup_some hlook
      refine ⟨hI.advance hlt hfin rfl (stepKeys_of_mem _ _ hmem).symm hI.sizes (EligExt.refl _)
        _ _ fun e he => ?_, by simp only; omega⟩
      rw [Array.toList_push] at he
      rcases List.mem_append.mp he with h | h
      · exact hI.postponed e h
      · rw [List.mem_singleton.mp h]; exact hmem
    · exact ⟨hI.ndiLe, hI.core, hI.keys, hI.postponed, hI.finalized, hI.sizes, hI.elig⟩
    · refine (applyPendingDeposit_ensures _ w hI.sizes).weaken fun _ w' h => ?_
      obtain ⟨hc', hk, hr', he'⟩ := h
      run_ensures
      refine ⟨hI.advance hlt hfin hc' hk hr' he' _ _ fun e he => ?_, by simp only; omega⟩
      rw [hk]
      exact (prefix_stepKeys _ _ _ _).subset (hI.postponed e he)

/-- `processPendingDeposits` is one `Scan` of the queue, at the finalized slot of the start
state. It keeps the slot, the finalized epoch and the registry-size equalities. The new queue
is `deposits.extract ndi ++ postpone`, which is the old queue's tail after the cursor, then
the postponed deposits. Each new validator starts at `FAR_FUTURE_EPOCH` (`EligExt`). -/
theorem processPendingDeposits_ensures (v : BeaconState) (hr : RegistrySizes v) :
    RunEnsures v (processPendingDeposits (StateTransition := FuluRun))
      (fun _ w => w.slot = v.slot ∧
        w.finalizedCheckpoint.epoch = v.finalizedCheckpoint.epoch ∧ RegistrySizes w ∧
        Scan (fun e : PendingDeposit => e.pubkey) depositValid
          (fun e => e.slot ≤ computeStartSlotAtEpoch v.finalizedCheckpoint.epoch)
          (registryKeys v).toList (registryKeys w).toList
          v.pendingDeposits.val.toList w.pendingDeposits.val.toList ∧
        EligExt (registryElig v) (registryElig w)) := by
  unfold processPendingDeposits
  run_ensures
  refine (ppdLoop_ensures _ _ _ _ v hr).weaken fun scan w hI => ?_
  run_ensures
  rename_i l hl
  obtain ⟨hndi, hcore, hkeys, hpost, hfinal, hsz, helig⟩ := hI
  simp only [coreFields, CoreFields.mk.injEq] at hcore
  obtain ⟨c1, c2, c3⟩ := hcore
  refine ⟨?_, ?_, ?_, ⟨scan.ndi, scan.postpone.toList, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [box_reduce]; exact c1
  · simp only [box_reduce]; exact c2
  · refine registrySizes_of_listSizes ?_ hsz
    simp [listSizes, box_reduce]
  · simp only [registryKeys, box_reduce]; exact hkeys
  · simp only [box_reduce]
    rw [hl]
    simp
    show List.take (v.pendingDeposits.val.size - scan.ndi)
      (List.drop scan.ndi v.pendingDeposits.val.toList) = _
    exact List.take_of_length_le (by simp)
  · simp only [registryKeys, box_reduce]; exact hpost
  · exact hfinal
  · simp only [registryElig, box_reduce]; exact helig

end

end EthCLSpecs.Proofs.Fulu.IndexAssignment
