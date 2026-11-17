import EthCLSpecs.Proofs.Fulu.EpochSuccess.Registry
import EthCLSpecs.Proofs.Fulu.EpochSuccess.Rewards
import EthCLSpecs.Fulu.Operations

/-!
# `EthCLSpecs.Proofs.Fulu.VoluntaryExits`: the voluntary exits of a block cannot fail

`process_voluntary_exit` checks an exit against the state and then calls
`initiate_validator_exit`. A block applies its exits in order, and each one writes the state
the next one reads. This module gives the conditions under which the whole list succeeds.

## One exit

`ExitGates s sve` collects the checks of `process_voluntary_exit` that read the state, and
`ExitSigned s sve` is the signature check. `processVoluntaryExit_succeeds` proves that an exit
with both cannot fail when the exit queue has room. The room premise bounds the exit epoch plus
`MIN_VALIDATOR_WITHDRAWABILITY_DELAY` below `2 ^ 64`. That sum is the one checked addition on
the path, and under the premise no other sum on the path wraps.

Two gates are stated in a stronger form than the spec asserts. `shardPeriod` is a bound in
`Nat`, so `activation_epoch + SHARD_COMMITTEE_PERIOD` does not wrap. `noPending` says every
pending partial withdrawal of the validator has amount zero, so the pending balance is zero
without a sum that could wrap. A client with checked arithmetic establishes both forms.

## Many exits

An exit of validator `i` writes that validator's record and the two exit-churn fields.
`ExitView S s w` says that `w` agrees with `s` on everything an exit of a validator outside `S`
reads. The gates and the signature of such an exit carry over from `s` to `w`.

`voluntaryExits_succeed_of_exitView` is the main theorem. Exits that name pairwise distinct
validators outside `S`, and pass the gates on `s`, succeed in order from any `w` with the exit
view of `s`. `ExitRoomAt` sizes the room for the list. With `S` empty and `w = s` the theorem
covers a block whose exits run from the state they were checked on. A nonempty `S` covers the
steps of the block that run before the exits, when those steps keep the exit view.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub umin umax)
open EthCLSpecs.Fulu

section

variable [Preset] [Config] [HasherTag]

/-! ## One exit -/

/-- `initiate_validator_exit` cannot fail for a validator with no exit epoch, when the exit queue
has room. It writes the validator's exit and withdrawable epochs and the two churn fields, and
the exit epoch is `exitStep` of the effective balance past `exitStart` at most.

`initiateValidatorExit_succeeds` is the ejection case inside `process_epoch`. This lemma bounds
the step by the validator's own effective balance and states the written record exactly. -/
theorem initiateValidatorExit_exits [PresetValid] [ConfigValid] (s : BeaconState)
    (i : ValidatorIndex) (hi : i.toNat < s.validators.val.size)
    (hfar : (s.validators[i.toNat]!).exitEpoch = Const.farFutureEpoch)
    (hroom : exitStart s + exitStep (s.validators[i.toNat]!).effectiveBalance.toNat +
      Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 64) :
    RunSucceeds s (initiateValidatorExit (StateTransition := FuluRun) i)
      (fun _ s' => ∃ ee ebtc : UInt64,
        s' = { s with
          validators := s.validators.set! i.toNat
            { s.validators[i.toNat]! with
              exitEpoch := ee
              withdrawableEpoch := ee + Const.minValidatorWithdrawabilityDelay },
          exitBalanceToConsume := ebtc, earliestExitEpoch := ee } ∧
        (computeEpochAtSlot s.slot).toNat + 1 + Const.maxSeedLookahead.toNat ≤ ee.toNat ∧
        ee.toNat ≤ exitStart s + exitStep (s.validators[i.toNat]!).effectiveBalance.toNat) := by
  unfold initiateValidatorExit
  run_succeeds
  · exact ⟨_, sszList_get?_eq _ _ hi⟩
  · -- The early return runs only for a validator that has an exit epoch already.
    rename_i y hy hc
    have hyEq : y = s.validators[i.toNat]! := Option.some.inj (hy.symm.trans (sszList_get?_eq _ _ hi))
    subst hyEq
    simp [hasNotInitiatedExit, hfar] at hc
  · rename_i y hy _
    have hyEq : y = s.validators[i.toNat]! := Option.some.inj (hy.symm.trans (sszList_get?_eq _ _ hi))
    subst hyEq
    refine (computeExitEpochAndUpdateChurn_reserves s _ (by omega)).weaken (fun ee s1 h => ?_)
    obtain ⟨ebtc, hs1, h1, h2⟩ := h
    subst hs1
    have hsize : UInt64.size = 2 ^ 64 := rfl
    run_succeeds
    · exact uint64_not_add_lt_of_toNat (by omega)
    · exact ⟨ee, ebtc, rfl, h1, h2⟩

omit [HasherTag] in
/-- `passed_shard_committee_period` from a bound in `Nat`. The bound says the sum
`activation_epoch + SHARD_COMMITTEE_PERIOD` does not wrap. -/
theorem passedShardCommitteePeriod_of_toNat (v : Validator) (e : Epoch)
    (h : v.activationEpoch.toNat + Const.shardCommitteePeriod.toNat ≤ e.toNat) :
    passedShardCommitteePeriod v e = true := by
  have he : e.toNat < 2 ^ 64 := e.toNat_lt
  unfold passedShardCommitteePeriod
  rw [decide_eq_true_eq, UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact h

omit [Config] in
/-- `get_pending_balance_to_withdraw` is zero when every pending partial withdrawal of the
validator has amount zero. Each addition in the fold adds zero, so the sum does not wrap. -/
theorem getPendingBalanceToWithdraw_eq_zero (s : BeaconState) (i : ValidatorIndex)
    (h : ∀ p ∈ s.pendingPartialWithdrawals.val, p.validatorIndex = i → p.amount = 0) :
    getPendingBalanceToWithdraw (pureState s) i = 0 := by
  unfold getPendingBalanceToWithdraw
  show s.pendingPartialWithdrawals.val.foldl
    (fun acc w => if w.validatorIndex == i then acc + w.amount else acc) 0 = 0
  refine Array.foldl_induction (motive := fun _ acc => acc = 0) rfl ?_
  intro j acc hacc
  subst hacc
  split
  · rename_i heq
    have hz : s.pendingPartialWithdrawals.val[j].amount = 0 :=
      h _ (Array.getElem_mem j.isLt) (by simpa using heq)
    rw [hz]
    rfl
  · rfl

/-- The validator a voluntary exit names, read from the registry of `s`. -/
abbrev exitValidator (s : BeaconState) (sve : SignedVoluntaryExit) : Validator :=
  s.validators[sve.message.validatorIndex.toNat]!

/-- The checks of `process_voluntary_exit` that read the state, for the exit `sve` on `s`. The
signature check is `ExitSigned`. -/
structure ExitGates (s : BeaconState) (sve : SignedVoluntaryExit) : Prop where
  /-- The exit names a validator in the registry. -/
  inRange : sve.message.validatorIndex.toNat < s.validators.val.size
  /-- The validator is active at the current epoch. -/
  active : isActiveValidator (exitValidator s sve) (computeEpochAtSlot s.slot) = true
  /-- The validator has no exit epoch yet. -/
  notExited : (exitValidator s sve).exitEpoch = Const.farFutureEpoch
  /-- The epoch the exit names has come. -/
  epochReached : sve.message.epoch ≤ computeEpochAtSlot s.slot
  /-- The validator has been active for `SHARD_COMMITTEE_PERIOD` epochs. The bound is in `Nat`,
  so the sum on the left does not wrap. -/
  shardPeriod : (exitValidator s sve).activationEpoch.toNat + Const.shardCommitteePeriod.toNat ≤
    (computeEpochAtSlot s.slot).toNat
  /-- The validator has no pending partial withdrawal with a nonzero amount. -/
  noPending : ∀ p ∈ s.pendingPartialWithdrawals.val,
    p.validatorIndex = sve.message.validatorIndex → p.amount = 0

variable [CryptoBackend]

/-- The signature check of `process_voluntary_exit`: the exit's signature verifies against the
validator's public key, under the voluntary-exit domain at the Capella fork version. -/
def ExitSigned (s : BeaconState) (sve : SignedVoluntaryExit) : Prop :=
  EthCLLib.Spec.blsVerifySigned (exitValidator s sve).pubkey sve.message
    (EthCLLib.Spec.computeDomain Const.domainVoluntaryExit Const.capellaForkVersion
      s.genesisValidatorsRoot)
    sve.signature = true

/-- `process_voluntary_exit` cannot fail on an exit that passes the gates and the signature
check, when the exit queue has room for it. The post-state differs from `s` in the validator's
exit and withdrawable epochs and in the two churn fields. -/
theorem processVoluntaryExit_succeeds [PresetValid] [ConfigValid] (s : BeaconState)
    (sve : SignedVoluntaryExit) (hg : ExitGates s sve) (hsig : ExitSigned s sve)
    (hroom : exitStart s + exitStep (exitValidator s sve).effectiveBalance.toNat +
      Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 64) :
    RunSucceeds s (processVoluntaryExit (StateTransition := FuluRun) sve)
      (fun _ s' => ∃ ee ebtc : UInt64,
        s' = { s with
          validators := s.validators.set! sve.message.validatorIndex.toNat
            { exitValidator s sve with
              exitEpoch := ee
              withdrawableEpoch := ee + Const.minValidatorWithdrawabilityDelay },
          exitBalanceToConsume := ebtc, earliestExitEpoch := ee } ∧
        (computeEpochAtSlot s.slot).toNat + 1 + Const.maxSeedLookahead.toNat ≤ ee.toNat ∧
        ee.toNat ≤ exitStart s + exitStep (exitValidator s sve).effectiveBalance.toNat) := by
  have hi := hg.inRange
  -- The body reads the validator through the checked index; `exitValidator` is the same entry.
  have hv : ∀ h : sve.message.validatorIndex.toNat < (pureState s).view.validators.size,
      (pureState s).view.validators[sve.message.validatorIndex.toNat]'h = exitValidator s sve :=
    fun _ => (sszList_getElem!_eq _ hi).symm
  unfold processVoluntaryExit
  run_succeeds
  · exact initiateValidatorExit_exits s sve.message.validatorIndex hi hg.notExited hroom
  · rename_i hc
    exact hc (by rw [hv]; exact hsig)
  · rename_i hc
    exact hc (by rw [getPendingBalanceToWithdraw_eq_zero s _ hg.noPending]; rfl)
  · rename_i hc
    exact hc (by rw [hv]; exact passedShardCommitteePeriod_of_toNat _ _ hg.shardPeriod)
  · rename_i hc
    exact hc hg.epochReached
  · rename_i hc
    exact hc (by rw [hv]; simp [hasNotInitiatedExit, hg.notExited])
  · rename_i hc
    exact hc (by rw [hv]; exact hg.active)
  · rename_i hc
    exact hc hi

/-! ## The exit view -/

/-- The fields of a validator record that a voluntary exit reads: the public key for the
signature, the two epochs for the gates, and the effective balance for the churn. -/
def exitRecord (v : Validator) : BLSPubkey × Epoch × Epoch × Gwei :=
  (v.pubkey, v.activationEpoch, v.exitEpoch, v.effectiveBalance)

/-- `ExitView S s w`: the state `w` agrees with `s` on everything a voluntary exit of a validator
outside `S` reads. The slot, the genesis validators root and the registry length are equal. A
validator outside `S` has the same exit record. Every pending partial withdrawal of `w` is one of
`s`, or belongs to a validator in `S`.

`S` holds the validators that the steps from `s` to `w` may have changed. -/
structure ExitView (S : ValidatorIndex → Prop) (s w : BeaconState) : Prop where
  slot : w.slot = s.slot
  genesisValidatorsRoot : w.genesisValidatorsRoot = s.genesisValidatorsRoot
  size : w.validators.val.size = s.validators.val.size
  record : ∀ i : ValidatorIndex, ¬ S i → i.toNat < s.validators.val.size →
    exitRecord (w.validators[i.toNat]!) = exitRecord (s.validators[i.toNat]!)
  pending : ∀ p ∈ w.pendingPartialWithdrawals.val,
    S p.validatorIndex ∨ p ∈ s.pendingPartialWithdrawals.val

omit [Config] [HasherTag] [CryptoBackend] in
/-- A state has the exit view of itself, for any set. -/
theorem ExitView.refl (S : ValidatorIndex → Prop) (s : BeaconState) : ExitView S s s :=
  ⟨rfl, rfl, rfl, fun _ _ _ => rfl, fun _ hp => Or.inr hp⟩

omit [Config] [HasherTag] [CryptoBackend] in
/-- A larger set gives a weaker exit view. -/
theorem ExitView.mono {S S' : ValidatorIndex → Prop} {s w : BeaconState}
    (h : ExitView S s w) (hS : ∀ i, S i → S' i) : ExitView S' s w :=
  ⟨h.slot, h.genesisValidatorsRoot, h.size, fun i hi => h.record i (fun hsi => hi (hS i hsi)),
    fun p hp => (h.pending p hp).imp_left (hS _)⟩

omit [Config] [HasherTag] [CryptoBackend] in
/-- Exit views compose, and the sets add up. -/
theorem ExitView.trans {S S' : ValidatorIndex → Prop} {s w u : BeaconState}
    (h : ExitView S s w) (h' : ExitView S' w u) : ExitView (fun i => S i ∨ S' i) s u := by
  refine ⟨h'.slot.trans h.slot, h'.genesisValidatorsRoot.trans h.genesisValidatorsRoot,
    h'.size.trans h.size, fun i hi hlt => ?_, fun p hp => ?_⟩
  · have hS : ¬ S i := fun hsi => hi (Or.inl hsi)
    have hS' : ¬ S' i := fun hsi => hi (Or.inr hsi)
    exact (h'.record i hS' (h.size ▸ hlt)).trans (h.record i hS hlt)
  · rcases h'.pending p hp with hp' | hp'
    · exact Or.inl (Or.inr hp')
    · exact (h.pending p hp').imp_left Or.inl

section Transport

variable {S : ValidatorIndex → Prop} {s w : BeaconState} {sve : SignedVoluntaryExit}

omit [Config] [HasherTag] [CryptoBackend] in
/-- An exit of a validator outside `S` reads the same record in both states. -/
theorem ExitView.exitValidator_eq (h : ExitView S s w) (hS : ¬ S sve.message.validatorIndex)
    (hi : sve.message.validatorIndex.toNat < s.validators.val.size) :
    (exitValidator w sve).pubkey = (exitValidator s sve).pubkey ∧
      (exitValidator w sve).activationEpoch = (exitValidator s sve).activationEpoch ∧
      (exitValidator w sve).exitEpoch = (exitValidator s sve).exitEpoch ∧
      (exitValidator w sve).effectiveBalance = (exitValidator s sve).effectiveBalance := by
  have hrec := h.record _ hS hi
  simp only [exitRecord, Prod.mk.injEq] at hrec
  exact hrec

omit [HasherTag] [CryptoBackend] in
/-- The gates of an exit of a validator outside `S` carry over to a state with the same exit
view. -/
theorem ExitGates.of_exitView (hg : ExitGates s sve) (h : ExitView S s w)
    (hS : ¬ S sve.message.validatorIndex) : ExitGates w sve := by
  obtain ⟨_, hact, hexit, _⟩ := h.exitValidator_eq hS hg.inRange
  refine ⟨h.size ▸ hg.inRange, ?_, hexit.trans hg.notExited, h.slot ▸ hg.epochReached, ?_, ?_⟩
  · have := hg.active
    unfold isActiveValidator at this ⊢
    rw [hact, hexit, h.slot]
    exact this
  · rw [hact, h.slot]
    exact hg.shardPeriod
  · intro p hp hidx
    rcases h.pending p hp with hps | hps
    · exact absurd (hidx ▸ hps) hS
    · exact hg.noPending p hps hidx

/-- The signature of an exit of a validator outside `S` carries over to a state with the same
exit view. -/
theorem ExitSigned.of_exitView (hsig : ExitSigned s sve) (h : ExitView S s w)
    (hS : ¬ S sve.message.validatorIndex)
    (hi : sve.message.validatorIndex.toNat < s.validators.val.size) : ExitSigned w sve := by
  obtain ⟨hpk, _, _, _⟩ := h.exitValidator_eq hS hi
  unfold ExitSigned at hsig ⊢
  rw [hpk, h.genesisValidatorsRoot]
  exact hsig

end Transport

/-! ## The exits of a block -/

/-- `ExitRoomAt start s exits`: the exit queue has room for `exits`. Starting at epoch `start`,
each exit moves the earliest exit epoch by `exitStep` of its validator's effective balance at
most. The last exit epoch plus `MIN_VALIDATOR_WITHDRAWABILITY_DELAY` stays below `2 ^ 64`.

The effective balances are read from `s`. `start` is the `exitStart` of the state the exits run
from, which may be a later state than `s`. -/
def ExitRoomAt (start : Nat) (s : BeaconState) (exits : List SignedVoluntaryExit) : Prop :=
  start + (exits.map fun sve => exitStep (exitValidator s sve).effectiveBalance.toNat).sum +
    Const.minValidatorWithdrawabilityDelay.toNat < 2 ^ 64

omit [HasherTag] [CryptoBackend] in
/-- Room for `n` exits of any balance is room for a list of `n` exits at most. An effective
balance is below `2 ^ 64`, so `exitStep (2 ^ 64 - 1)` bounds the step of every exit. -/
theorem ExitRoomAt.of_uniform {start n : Nat} (s : BeaconState)
    (exits : List SignedVoluntaryExit) (hlen : exits.length ≤ n)
    (h : start + n * exitStep (2 ^ 64 - 1) + Const.minValidatorWithdrawabilityDelay.toNat <
      2 ^ 64) : ExitRoomAt start s exits := by
  have hsum : ∀ l : List SignedVoluntaryExit,
      (l.map fun sve => exitStep (exitValidator s sve).effectiveBalance.toNat).sum ≤
        l.length * exitStep (2 ^ 64 - 1) := by
    intro l
    induction l with
    | nil => simp
    | cons x rest ih =>
      have hx : exitStep (exitValidator s x).effectiveBalance.toNat ≤ exitStep (2 ^ 64 - 1) :=
        exitStep_mono (by have := (exitValidator s x).effectiveBalance.toNat_lt; omega)
      rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  have hmul : exits.length * exitStep (2 ^ 64 - 1) ≤ n * exitStep (2 ^ 64 - 1) :=
    Nat.mul_le_mul_right _ hlen
  have := hsum exits
  unfold ExitRoomAt
  omega

omit [Config] [HasherTag] [CryptoBackend] in
/-- The state after an exit of validator `i` has the exit view of the state before it, for the
set that holds `i` alone: the exit writes that validator's record and the two churn fields. -/
theorem exitView_of_exit (s : BeaconState) (i : ValidatorIndex) (y : Validator)
    (ebtc : Gwei) (ee : Epoch) :
    ExitView (· = i) s
      { s with validators := s.validators.set! i.toNat y, exitBalanceToConsume := ebtc,
               earliestExitEpoch := ee } := by
  refine ⟨rfl, rfl, by simp, fun j hj hlt => ?_, fun _ hp => Or.inr hp⟩
  have hne : i.toNat ≠ j.toNat := fun h => hj (UInt64.toNat_inj.mp h.symm)
  show exitRecord ((s.validators.set! i.toNat y)[j.toNat]!) = _
  rw [sszList_set!_getElem!_of_ne _ _ hlt hne]

/-- The voluntary exits of a block succeed, one after the other, from the state they pass the
gates on. The exits name pairwise distinct validators, so an exit leaves the gates of the later
exits alone, and `ExitRoomAt` covers the epochs the exits take together. -/
theorem processVoluntaryExits_foldlM_succeeds [PresetValid] [ConfigValid] :
    ∀ (exits : List SignedVoluntaryExit) (w : BeaconState),
      exits.Pairwise (fun a b => a.message.validatorIndex ≠ b.message.validatorIndex) →
      (∀ sve ∈ exits, ExitGates w sve ∧ ExitSigned w sve) →
      ExitRoomAt (exitStart w) w exits →
      RunSucceeds w
        (exits.foldlM (fun (_ : PUnit) sve => processVoluntaryExit (StateTransition := FuluRun) sve)
          ⟨⟩)
        (fun _ _ => True)
  | [], w, _, _, _ => by
    rw [List.foldlM_nil]
    exact runSucceeds_pure trivial
  | sve :: rest, w, hdistinct, hall, hroom => by
    obtain ⟨hg, hsig⟩ := hall sve List.mem_cons_self
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hdistinct
    unfold ExitRoomAt at hroom
    rw [List.map_cons, List.sum_cons] at hroom
    rw [List.foldlM_cons]
    refine runSucceeds_bind ((processVoluntaryExit_succeeds w sve hg hsig (by omega)).weaken ?_)
    intro _ w' hw'
    obtain ⟨ee, ebtc, rfl, _, hee⟩ := hw'
    have hview := exitView_of_exit w sve.message.validatorIndex
      { exitValidator w sve with
        exitEpoch := ee
        withdrawableEpoch := ee + Const.minValidatorWithdrawabilityDelay } ebtc ee
    -- A later exit names another validator, so it reads the same record after this exit.
    have hother : ∀ y ∈ rest, ¬ (y.message.validatorIndex = sve.message.validatorIndex) :=
      fun y hy h => hhead y hy h.symm
    refine processVoluntaryExits_foldlM_succeeds rest _ hrest (fun y hy => ?_) ?_
    · obtain ⟨hgy, hsigy⟩ := hall y (List.mem_cons_of_mem _ hy)
      exact ⟨hgy.of_exitView hview (hother y hy),
        hsigy.of_exitView hview (hother y hy) hgy.inRange⟩
    · -- The exit moved the start by its own step at most, and kept the other balances.
      have hstart : exitStart
          { w with
            validators := w.validators.set! sve.message.validatorIndex.toNat
              { exitValidator w sve with
                exitEpoch := ee
                withdrawableEpoch := ee + Const.minValidatorWithdrawabilityDelay },
            exitBalanceToConsume := ebtc, earliestExitEpoch := ee } ≤
          exitStart w + exitStep (exitValidator w sve).effectiveBalance.toNat := by
        unfold exitStart at hee ⊢
        dsimp only
        omega
      have hsum : (rest.map fun y => exitStep (exitValidator
          { w with
            validators := w.validators.set! sve.message.validatorIndex.toNat
              { exitValidator w sve with
                exitEpoch := ee
                withdrawableEpoch := ee + Const.minValidatorWithdrawabilityDelay },
            exitBalanceToConsume := ebtc, earliestExitEpoch := ee } y).effectiveBalance.toNat).sum =
          (rest.map fun y => exitStep (exitValidator w y).effectiveBalance.toNat).sum := by
        congr 1
        refine List.map_congr_left (fun y hy => ?_)
        obtain ⟨hgy, _⟩ := hall y (List.mem_cons_of_mem _ hy)
        rw [(hview.exitValidator_eq (hother y hy) hgy.inRange).2.2.2]
      unfold ExitRoomAt
      rw [hsum]
      omega

/-- The fold `process_operations` runs over the voluntary exits of a block body: each exit
through `process_voluntary_exit`, in order. -/
abbrev processVoluntaryExits (exits : Array SignedVoluntaryExit) : FuluRun Unit :=
  ForM.forM exits (processVoluntaryExit (StateTransition := FuluRun))

/-- The `for` loop `process_operations` runs over `body.voluntary_exits` is
`processVoluntaryExits` of the list's elements. The loop elaborates to a `forIn` whose body
always yields, which is a fold. -/
theorem forIn_voluntaryExits_eq {cap : Nat}
    (exits : SizzLean.Repr.SSZList SignedVoluntaryExit cap) :
    forIn exits PUnit.unit (fun op (_ : PUnit) => do
        processVoluntaryExit (StateTransition := FuluRun) op
        pure (ForInStep.yield PUnit.unit)) =
      processVoluntaryExits exits.val := by
  -- The `ForIn` instance of an SSZ list walks the underlying array.
  show forIn exits.val PUnit.unit (fun op (_ : PUnit) =>
      processVoluntaryExit (StateTransition := FuluRun) op >>= fun _ =>
        pure (ForInStep.yield PUnit.unit)) =
    ForM.forM exits.val (processVoluntaryExit (StateTransition := FuluRun))
  -- Mapping a constant over an action is a bind with a `pure` of that constant.
  have hmap : ∀ {α β : Type} (x : FuluRun α) (a : β),
      (fun _ => a) <$> x = (x >>= fun _ => pure a) := by
    intro α β x a
    simp [Functor.map]
  have hbody : (fun op (_ : PUnit) =>
        processVoluntaryExit (StateTransition := FuluRun) op >>= fun _ =>
          pure (ForInStep.yield PUnit.unit)) =
      (fun a (_ : PUnit) =>
        (fun _ => ForInStep.yield PUnit.unit) <$>
          processVoluntaryExit (StateTransition := FuluRun) a) := by
    funext op _
    rw [hmap]
  rw [hbody, Array.forIn_yield_eq_foldlM
    (f := fun a (_ : PUnit) => processVoluntaryExit (StateTransition := FuluRun) a)
    (g := fun (_ : SignedVoluntaryExit) (_ : PUnit) (_ : PUnit) => PUnit.unit)]
  simp only [ForM.forM, Array.forM, hmap, bind_pure_unit]

/-- The voluntary exits of a block succeed from a state `w` that has the exit view of the state
`s` they pass the gates on. The exits name pairwise distinct validators outside `S`. The
effective balances that size the room are read from `s`, and the room starts at the `exitStart`
of `w`.

With `S` empty and `w = s` this is the plain statement: exits that pass the gates on `s`
succeed from `s`. A nonempty `S` covers steps that run between `s` and the exits. -/
theorem voluntaryExits_succeed_of_exitView [PresetValid] [ConfigValid]
    {S : ValidatorIndex → Prop} {s w : BeaconState} (exits : Array SignedVoluntaryExit)
    (hview : ExitView S s w)
    (hdistinct : exits.toList.Pairwise
      fun a b => a.message.validatorIndex ≠ b.message.validatorIndex)
    (hgates : ∀ sve ∈ exits, ExitGates s sve) (hsigned : ∀ sve ∈ exits, ExitSigned s sve)
    (hexcl : ∀ sve ∈ exits, ¬ S sve.message.validatorIndex)
    (hroom : ExitRoomAt (exitStart w) s exits.toList) :
    ∃ w', runPure (processVoluntaryExits exits) w = .ok ((), w') := by
  have hmem : ∀ sve ∈ exits.toList, sve ∈ exits := fun _ h => Array.mem_toList_iff.mp h
  have hroomw : ExitRoomAt (exitStart w) w exits.toList := by
    unfold ExitRoomAt at hroom ⊢
    have hsum : (exits.toList.map fun y => exitStep (exitValidator w y).effectiveBalance.toNat).sum =
        (exits.toList.map fun y => exitStep (exitValidator s y).effectiveBalance.toNat).sum := by
      congr 1
      refine List.map_congr_left (fun y hy => ?_)
      rw [(hview.exitValidator_eq (hexcl y (hmem y hy)) (hgates y (hmem y hy)).inRange).2.2.2]
    rw [hsum]
    exact hroom
  have hrun := processVoluntaryExits_foldlM_succeeds exits.toList w hdistinct
    (fun sve hsve => ⟨(hgates sve (hmem sve hsve)).of_exitView hview (hexcl sve (hmem sve hsve)),
      (hsigned sve (hmem sve hsve)).of_exitView hview (hexcl sve (hmem sve hsve))
        (hgates sve (hmem sve hsve)).inRange⟩) hroomw
  obtain ⟨a, w', hw', _⟩ := hrun.runPure_ok
  refine ⟨w', ?_⟩
  rw [show processVoluntaryExits exits =
      exits.foldlM (fun (_ : PUnit) sve => processVoluntaryExit (StateTransition := FuluRun) sve) ⟨⟩
      from rfl, ← Array.foldlM_toList]
  exact hw'

end

end EthCLSpecs.Proofs.Fulu
