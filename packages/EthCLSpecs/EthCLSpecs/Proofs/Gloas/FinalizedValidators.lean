import EthCLSpecs.Proofs.Fulu.FinalizedValidators
import EthCLSpecs.Proofs.Gloas.IndexAssignment

/-!
# `EthCLSpecs.Proofs.Gloas.FinalizedValidators`: chains agree on the finalized validators, across the Gloas upgrade

The Gloas counterpart of `Proofs/Fulu/FinalizedValidators.lean`, which states the property and
names the argument. A validator is finalized in a state when its `activation_eligibility_epoch`
is at or below the state's finalized epoch, or when it comes before such a validator in the
registry. A finalized validator of one chain has the same index and the same key on every
chain that descends from the finalized checkpoint.

## Across the upgrade

`ReachableState.follows` proves that the Gloas state transition keeps `Follows`, with the
`upgrade` step included. So the common state `t` may be a Fulu state, and each chain may pass
the Gloas upgrade on its own.

* `upgradeToGloas` copies the slot and maps the registry one validator at a time
  (`registryView_upgradeToGloas`).
* `completeUpgradeToGloas` fills the PTC window and onboards builders from the queue. The
  builder steps write the builder registry, and the last write replaces the queue. No step
  writes a validator (`completeUpgradeToGloas_registry`).

`finalizedValidators_pubkey_eq_fromFulu` is the theorem for a Fulu common state, and
`finalizedValidators_pubkey_eq` the one for a Gloas common state.

## The contrast with the index assignment

`IndexAssignmentFromFulu` (`Proofs/Gloas/IndexAssignment.lean`) is false: two chains from one
Fulu state, with compatible finality, can hold two keys at one index.
`FinalizedIndexAssignmentFromFulu` is that statement with two more hypotheses, that the
validator's `activation_eligibility_epoch` is finalized in both states.
`finalizedIndexAssignmentFromFulu` proves it.

In the pair of chains that refutes the first statement, the upgrade turns a queued deposit
into a builder on one chain, after the other chain made a validator from it. Each validator
at the disputed index was added after the common state. Its eligibility epoch then starts
above the slot of the common state, and neither chain has finalized that slot.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Gloas
open EthCLSpecs.Gloas.Const (slotsPerEpoch slotsPerEpochPos farFutureEpoch gloasForkVersion
  gloasForkEpoch)
open EthCLSpecs.Proofs.DepositQueue
open EthCLSpecs.Proofs.FinalizedRegistry
open scoped EthCLSpecs.Gloas.Downgrade
open IndexAssignment (registryKeys registryElig EligStep Ctx StepInv KeepsFrame finalizedSlot
  processSlots_progress processBlock_keepsFrame addBuilderToRegistry_keepsFrame)

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The `View` of a Gloas state: its slot, its finalized epoch, the public keys of its registry
and the eligibility epochs of its registry. -/
def registryView (v : BeaconState) : View BLSPubkey where
  slot := v.slot.toNat
  finalizedEpoch := v.finalizedCheckpoint.epoch
  keys := registryKeys v
  elig := registryElig v

omit [HasherTag] [Config] [CryptoBackend] in
/-- A state follows itself: both arrays of its view map `validators`, so they have one size. -/
theorem follows_refl (t : BeaconState) :
    Follows slotsPerEpoch (registryView t) (registryView t) :=
  Follows.refl _ (by simp [registryView, registryKeys, registryElig])

omit [HasherTag] [Config] [CryptoBackend] in
/-- One step of the chain keeps `Follows`, from what the frame says about the step. The Gloas
copy of the Fulu `follows_step`, which explains the two new values `EligStep` allows. -/
theorem follows_step (hspe : 2 ≤ slotsPerEpoch) {T : View BLSPubkey} {x z : BeaconState}
    (hx : Follows slotsPerEpoch T (registryView x)) (hslot : x.slot.toNat ≤ z.slot.toNat)
    (hkeys : (registryKeys x).toList <+: (registryKeys z).toList)
    (helig : EligStep x.slot (registryElig x) (registryElig z)) :
    Follows slotsPerEpoch T (registryView z) := by
  have hfar : farFutureEpoch.toNat = 2 ^ 64 - 1 := rfl
  have hlt : x.slot.toNat < farFutureEpoch.toNat * slotsPerEpoch := by
    have := x.slot.toNat_lt
    rw [hfar]
    omega
  have hno : x.slot.toNat / slotsPerEpoch + 1 < 2 ^ 64 := by
    have h1 := Nat.div_lt_of_lt_mul (Nat.mul_comm _ _ ▸ hlt)
    omega
  refine hx.step ?_ hslot hkeys fun j hj => ?_
  · simp [registryView, registryKeys, registryElig]
  · rcases helig j hj with h | h | h
    · exact Or.inl h
    · refine Or.inr ?_
      show x.slot.toNat < ((registryElig z)[j]).toNat * slotsPerEpoch
      rw [h]
      exact hlt
    · refine Or.inr ?_
      show x.slot.toNat < ((registryElig z)[j]).toNat * slotsPerEpoch
      have he : (computeEpochAtSlot x.slot + 1).toNat = x.slot.toNat / slotsPerEpoch + 1 := by
        rw [UInt64.toNat_add, computeEpochAtSlot_toNat, UInt64.toNat_one]
        exact Nat.mod_eq_of_lt hno
      rw [h, he, Nat.mul_comm]
      exact Nat.lt_mul_div_succ _ slotsPerEpochPos

/-! ## The upgrade -/

omit [Config] [CryptoBackend] in
/-- `upgradeToGloas` keeps the view. It copies the slot and the finalized checkpoint, and it
maps `validators` with a converter that copies each field, so the keys and the eligibility
epochs of the Gloas state are those of the Fulu state. -/
theorem registryView_upgradeToGloas (fv : Version) (u : EthCLSpecs.Fulu.BeaconState) :
    registryView (upgradeToGloas fv u) = EthCLSpecs.Proofs.Fulu.registryView u := by
  have hk : registryKeys (upgradeToGloas fv u)
      = EthCLSpecs.Proofs.Fulu.IndexAssignment.registryKeys u := by
    simp only [registryKeys, EthCLSpecs.Proofs.Fulu.IndexAssignment.registryKeys, upgradeToGloas,
      Array.map_map]
    rfl
  have he : registryElig (upgradeToGloas fv u)
      = EthCLSpecs.Proofs.Fulu.IndexAssignment.registryElig u := by
    simp only [registryElig, EthCLSpecs.Proofs.Fulu.IndexAssignment.registryElig, upgradeToGloas,
      Array.map_map]
    rfl
  simp only [registryView, EthCLSpecs.Proofs.Fulu.registryView, hk, he]
  rfl

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

/-- The builder onboarding of the upgrade keeps the slot and the keys, and it moves the
eligibility epochs by `EligStep`. The loop applies builder deposits, each of which keeps the
frame. The last write replaces the queue, which the frame does not allow, so the contract
states the three values apart. -/
theorem onboardBuildersFromPendingDeposits_registry (v : BeaconState) (hr : RegistrySizes v) :
    RunEnsures v (onboardBuildersFromPendingDeposits (StateTransition := GloasRun))
      (fun _ w => w.slot = v.slot ∧ registryKeys w = registryKeys v ∧
        EligStep v.slot (registryElig v) (registryElig w)) := by
  unfold onboardBuildersFromPendingDeposits
  run_ensures
  refine (Preserves.forIn_array _ _ (fun _ _ => ?_)).run (StepInv.start v false hr)
    (fun _ w hw => ?_)
  · intro w hw
    run_ensures
    all_goals try frame_close
    call applyDepositForBuilder_keepsFrame _ _ _ _ _
    run_ensures
    frame_close
  · run_ensures
    obtain ⟨hs, -, hk, -, -, he⟩ := hw
    simp only [Ctx.of] at hs hk he
    exact ⟨by simp only [box_reduce]; exact hs, by simp only [registryKeys, box_reduce]; exact hk,
      by simp only [registryElig, box_reduce]; exact he⟩

/-- The second half of the upgrade keeps the slot and the keys, and it moves the eligibility
epochs by `EligStep`. The PTC window write touches neither. -/
theorem completeUpgradeToGloas_registry (v : BeaconState) (hr : RegistrySizes v) :
    RunEnsures v (completeUpgradeToGloas (StateTransition := GloasRun))
      (fun _ w => w.slot = v.slot ∧ registryKeys w = registryKeys v ∧
        EligStep v.slot (registryElig v) (registryElig w)) := by
  unfold completeUpgradeToGloas
  run_ensures
  exact onboardBuildersFromPendingDeposits_registry _ hr

/-! ## The induction -/

variable {anchors : Anchors} {validated : Bool} {nextForkEpoch : Epoch}

/-- The state transition keeps `Follows`, across the upgrade: when every Fulu anchor and every
Gloas anchor follows `T`, so does every reachable Gloas state.

The `upgrade` step starts at a reachable Fulu state, which follows `T` by the Fulu theorem.
`upgradeToGloas` keeps the view, and `completeUpgradeToGloas` is one more step of the chain.
The `slots` and `block` steps are the Fulu ones. -/
theorem ReachableState.follows (hspe : 2 ≤ slotsPerEpoch)
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → SimpleStateInvariants u) {T : View BLSPubkey}
    (h0F : ∀ u, anchors.fulu u →
      Follows slotsPerEpoch T (EthCLSpecs.Proofs.Fulu.registryView u))
    (h0G : ∀ u, anchors.gloas u → Follows slotsPerEpoch T (registryView u)) {w : BeaconState}
    (h : ReachableState anchors validated nextForkEpoch w) :
    Follows slotsPerEpoch T (registryView w) := by
  induction h with
  | anchor ha _ => exact h0G _ ha
  | @upgrade u w hu _ _ hrun =>
    have hFu := EthCLSpecs.Proofs.Fulu.ReachableState.simpleStateInvariants hF hu
    have fu : Follows slotsPerEpoch T (EthCLSpecs.Proofs.Fulu.registryView u) :=
      EthCLSpecs.Proofs.Fulu.ReachableState.follows hspe hF h0F hu
    rw [← registryView_upgradeToGloas gloasForkVersion u] at fu
    obtain ⟨hs, hk, he⟩ := (completeUpgradeToGloas_registry _
      (upgradeToGloas_invariants _ hFu).registrySizes).runPure_ok hrun
    exact follows_step hspe fu (by rw [hs]; exact Nat.le_refl _)
      (by rw [hk]; exact List.prefix_refl _) he
  | slots target hv _ hrun ih =>
    have hinv := hv.simpleStateInvariants hF hG
    refine (processSlots_progress (fun x => Follows slotsPerEpoch T (registryView x)) ?_
      target _ hinv ih).runPure_ok hrun
    intro x z _ _ hprog hPx
    have hs := hprog.slot
    exact follows_step hspe hPx (by omega) (hprog.deposits.2.prefix _ _) hprog.elig
  | @block v w sb hv _ _ hrun _ ih =>
    have hinv := hv.simpleStateInvariants hF hG
    have hst := (processBlock_keepsFrame sb.message (Ctx.of v true) rfl v
      (StepInv.start v true hinv.registrySizes)).runPure_ok hrun
    obtain ⟨hs, -, hk, -, -, he⟩ := hst
    simp only [Ctx.of] at hs hk he
    exact follows_step hspe ih (by rw [hs]; exact Nat.le_refl _)
      (by rw [hk]; exact List.prefix_refl _) he

/-! ## The theorems -/

/-- The finalized epoch of `w` starts at or before the slot `σ`. With `σ` the slot of a state
on the chain of `w`, that state sits at or after the finalized checkpoint of `w`. -/
def FinalizedAtOrBefore (σ : Slot) (w : BeaconState) : Prop :=
  (computeStartSlotAtEpoch w.finalizedCheckpoint.epoch).toNat ≤ σ.toNat

omit [HasherTag] [Config] [CryptoBackend] in
/-- `FinalizedBelow`, the hypothesis of the index-assignment theorem, is the strict form. -/
theorem FinalizedBelow.atOrBefore {σ : Slot} {w : BeaconState} (h : FinalizedBelow σ w) :
    FinalizedAtOrBefore σ w := Nat.le_of_lt h

omit [HasherTag] [CryptoBackend] in
/-- The hypothesis over the view, with no `uint64` wrap (`finalizedSlot_toNat`). -/
theorem FinalizedAtOrBefore.view {σ : Slot} {w : BeaconState} (h : FinalizedAtOrBefore σ w)
    (hw : SimpleStateInvariants w) :
    (registryView w).finalizedEpoch.toNat * slotsPerEpoch ≤ σ.toNat := by
  have hf : (computeStartSlotAtEpoch w.finalizedCheckpoint.epoch).toNat
      = w.finalizedCheckpoint.epoch.toNat * slotsPerEpoch := finalizedSlot_toNat hw
  unfold FinalizedAtOrBefore at h
  rw [hf] at h
  exact h

omit [HasherTag] [Config] [CryptoBackend] in
/-- The conclusion over the registry, from the conclusion over the views. The view's arrays
map `validators`, so its sizes and entries are the registry's. -/
theorem pubkey_eq_of_views {t : View BLSPubkey} {w' w'' : BeaconState}
    (f' : Follows slotsPerEpoch t (registryView w'))
    (f'' : Follows slotsPerEpoch t (registryView w''))
    (hfin : (registryView w').finalizedEpoch.toNat * slotsPerEpoch ≤ t.slot) {i j : Nat}
    (hji : j ≤ i) (hi : i < w'.validators.val.size)
    (he : w'.validators.val[i].activationEligibilityEpoch ≤ w'.finalizedCheckpoint.epoch) :
    ∃ (hj' : j < w'.validators.val.size) (hj'' : j < w''.validators.val.size),
      w''.validators.val[j].pubkey = w'.validators.val[j].pubkey := by
  have hi' : i < (registryView w').elig.size := by simpa [registryView, registryElig] using hi
  have he' : (registryView w').elig[i] ≤ (registryView w').finalizedEpoch := by
    simpa [registryView, registryElig] using he
  obtain ⟨hj', hj'', e⟩ := keys_eq_of_finalized f' f'' hfin hji hi' he'
  refine ⟨by simpa [registryView, registryKeys] using hj',
    by simpa [registryView, registryKeys] using hj'', ?_⟩
  simpa [registryView, registryKeys] using e

/-- Two Gloas chains from a Gloas state agree on the finalized validators of one of them.

* The preset has two or more slots per epoch, as `minimal` and `mainnet` do.
* `t` is a reachable Gloas state, and the anchors satisfy their fork's
  `SimpleStateInvariants`.
* `w'` and `w''` are reachable from `t`: `ReachableState` with the one anchor `t`.
* The finalized epoch of `w'` starts at or before the slot of `t`.
* Validator `i` of `w'` has a finalized `activation_eligibility_epoch`.

Then every index `j` up to `i` is in both registries, with one public key. -/
theorem finalizedValidators_pubkey_eq (hspe : 2 ≤ slotsPerEpoch)
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → SimpleStateInvariants u) {t w' w'' : BeaconState}
    (ht : ReachableState anchors validated nextForkEpoch t)
    (h' : ReachableState (Anchors.only t) validated nextForkEpoch w')
    (h'' : ReachableState (Anchors.only t) validated nextForkEpoch w'')
    (hfin : FinalizedAtOrBefore t.slot w') {i j : Nat} (hji : j ≤ i)
    (hi : i < w'.validators.val.size)
    (he : w'.validators.val[i].activationEligibilityEpoch ≤ w'.finalizedCheckpoint.epoch) :
    ∃ (hj' : j < w'.validators.val.size) (hj'' : j < w''.validators.val.size),
      w''.validators.val[j].pubkey = w'.validators.val[j].pubkey := by
  -- The one anchor is the Gloas state `t`. The anchor set holds no Fulu state.
  have hF' : ∀ u, (Anchors.only t).fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u :=
    fun _ hu => hu.elim
  have hG' : ∀ u, (Anchors.only t).gloas u → SimpleStateInvariants u :=
    fun _ hu => hu ▸ ht.simpleStateInvariants hF hG
  have h0F : ∀ u, (Anchors.only t).fulu u →
      Follows slotsPerEpoch (registryView t) (EthCLSpecs.Proofs.Fulu.registryView u) :=
    fun _ hu => hu.elim
  have h0G : ∀ u, (Anchors.only t).gloas u →
      Follows slotsPerEpoch (registryView t) (registryView u) :=
    fun _ hu => hu ▸ follows_refl t
  exact pubkey_eq_of_views (ReachableState.follows hspe hF' hG' h0F h0G h')
    (ReachableState.follows hspe hF' hG' h0F h0G h'')
    (hfin.view (h'.simpleStateInvariants hF' hG')) hji hi he

end

/-! ## A Fulu common state

The statements below name a Fulu state `t` and Gloas states reachable from it, as
`IndexAssignmentFromFulu` does. Each chain passes the Gloas upgrade on its own. -/

section FromFulu

variable [Preset] [HasherTag] [Config] [CryptoBackend]
variable {validated : Bool} {nextForkEpoch : Epoch}

/-- Two Gloas chains from a Fulu state agree on the finalized validators of one of them.

* The preset has two or more slots per epoch.
* `t` is a reachable Fulu state, and the Fulu anchors satisfy `SimpleStateInvariants`.
* `w'` and `w''` are Gloas states reachable from `t`, through the upgrade:
  `ReachableState` with the one Fulu anchor `t`.
* The finalized epoch of `w'` starts at or before the slot of `t`.
* Validator `i` of `w'` has a finalized `activation_eligibility_epoch`.

Then every index `j` up to `i` is in both registries, with one public key. The proof rests on
Lean's three standard axioms. -/
theorem finalizedValidators_pubkey_eq_fromFulu (hspe : 2 ≤ slotsPerEpoch)
    {anchors : EthCLSpecs.Proofs.Fulu.Anchors}
    (hA : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    {t : EthCLSpecs.Fulu.BeaconState} {w' w'' : BeaconState}
    (ht : EthCLSpecs.Proofs.Fulu.ReachableState anchors validated gloasForkEpoch t)
    (h' : ReachableState (Anchors.onlyFulu t) validated nextForkEpoch w')
    (h'' : ReachableState (Anchors.onlyFulu t) validated nextForkEpoch w'')
    (hfin : FinalizedAtOrBefore t.slot w') {i j : Nat} (hji : j ≤ i)
    (hi : i < w'.validators.val.size)
    (he : w'.validators.val[i].activationEligibilityEpoch ≤ w'.finalizedCheckpoint.epoch) :
    ∃ (hj' : j < w'.validators.val.size) (hj'' : j < w''.validators.val.size),
      w''.validators.val[j].pubkey = w'.validators.val[j].pubkey := by
  -- The one anchor is the Fulu state `t`. The anchor set holds no Gloas state.
  have hF' : ∀ u, (Anchors.onlyFulu t).fulu u →
      EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u :=
    fun _ hu => hu ▸ EthCLSpecs.Proofs.Fulu.ReachableState.simpleStateInvariants hA ht
  have hG' : ∀ u, (Anchors.onlyFulu t).gloas u → SimpleStateInvariants u :=
    fun _ hu => hu.elim
  have h0F : ∀ u, (Anchors.onlyFulu t).fulu u →
      Follows slotsPerEpoch (EthCLSpecs.Proofs.Fulu.registryView t)
        (EthCLSpecs.Proofs.Fulu.registryView u) :=
    fun _ hu => hu ▸ EthCLSpecs.Proofs.Fulu.follows_refl t
  have h0G : ∀ u, (Anchors.onlyFulu t).gloas u →
      Follows slotsPerEpoch (EthCLSpecs.Proofs.Fulu.registryView t) (registryView u) :=
    fun _ hu => hu.elim
  exact pubkey_eq_of_views (ReachableState.follows hspe hF' hG' h0F h0G h')
    (ReachableState.follows hspe hF' hG' h0F h0G h'')
    (hfin.view (h'.simpleStateInvariants hF' hG')) hji hi he

/-- `IndexAssignmentFromFulu` for the validators that are finalized in both states: the
hypotheses of that statement, and two more. Validator `i` has an
`activation_eligibility_epoch` at or below the finalized epoch, in `w'` and in `w''`.

`IndexAssignmentFromFulu` is false (`Tests/GloasPyspecReplayPins.lean`), and this statement
is a theorem (`finalizedIndexAssignmentFromFulu`). -/
def FinalizedIndexAssignmentFromFulu : Prop :=
  ∀ (anchors : EthCLSpecs.Proofs.Fulu.Anchors) (t : EthCLSpecs.Fulu.BeaconState)
    (w' w'' : BeaconState),
    (∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u) →
    EthCLSpecs.Proofs.Fulu.ReachableState anchors true gloasForkEpoch t →
    ReachableState (Anchors.onlyFulu t) true farFutureEpoch w' →
    ReachableState (Anchors.onlyFulu t) true farFutureEpoch w'' →
    CompatibleFinality t.slot w' w'' →
    ∀ (i : Nat) (h' : i < w'.validators.val.size) (h'' : i < w''.validators.val.size),
      w'.validators.val[i].activationEligibilityEpoch ≤ w'.finalizedCheckpoint.epoch →
      w''.validators.val[i].activationEligibilityEpoch ≤ w''.finalizedCheckpoint.epoch →
      w'.validators.val[i].pubkey = w''.validators.val[i].pubkey

/-- The index assignment of the finalized validators is stable across the Gloas upgrade, at a
preset with two or more slots per epoch. `CompatibleFinality` gives `FinalizedAtOrBefore` for
one of the two states, and `finalizedValidators_pubkey_eq_fromFulu` applies from that
state. -/
theorem finalizedIndexAssignmentFromFulu (hspe : 2 ≤ slotsPerEpoch) :
    FinalizedIndexAssignmentFromFulu := by
  intro anchors t w' w'' hA ht h' h'' hc i hi' hi'' he' he''
  rcases hc with hc | hc
  · obtain ⟨_, _, e⟩ := finalizedValidators_pubkey_eq_fromFulu hspe hA ht h' h''
      hc.atOrBefore (Nat.le_refl i) hi' he'
    exact e.symm
  · obtain ⟨_, _, e⟩ := finalizedValidators_pubkey_eq_fromFulu hspe hA ht h'' h'
      hc.atOrBefore (Nat.le_refl i) hi'' he''
    exact e

end FromFulu

end EthCLSpecs.Proofs.Gloas
