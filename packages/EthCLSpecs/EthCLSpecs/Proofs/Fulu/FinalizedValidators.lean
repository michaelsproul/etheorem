import EthCLSpecs.Proofs.FinalizedRegistry
import EthCLSpecs.Proofs.Fulu.IndexAssignment

/-!
# `EthCLSpecs.Proofs.Fulu.FinalizedValidators`: Fulu chains agree on the finalized validators

A validator is finalized in a state when its `activation_eligibility_epoch` is at or below the
state's finalized epoch, or when it comes before such a validator in the registry. A client
may keep one map from validator index to public key that holds the finalized validators alone.
`finalizedValidators_pubkey_eq` proves the property that map rests on, for chains inside Fulu:
a finalized validator of one chain has the same index and the same key on every chain that
descends from the finalized checkpoint.

## The statement

It reads in `ReachableState` (`Proofs/Fulu/Reachable.lean`), as the index-assignment theorem
does (`Proofs/Fulu/IndexAssignment.lean`).

* `ReachableState anchors validated nextForkEpoch t`: `t` is the common state of two chains.
* `ReachableState (Anchors.only t) validated nextForkEpoch w`: `w` is reachable from `t`.
* `FinalizedAtOrBefore t.slot w'`: the finalized epoch of `w'` starts at or before the slot of
  `t`. With `t` the state of the finalized checkpoint of `w'`, the two slots are equal. Then
  "reachable from `t`" reads "descends from the finalized checkpoint of `w'`".
* Validator `i` of `w'` has `activation_eligibility_epoch ≤ w'.finalized_checkpoint.epoch`.

Then every index `j` up to `i` is in the registry of `w'` and of `w''`, with one public key.
`w''` needs no hypothesis on its own finality.

## The proof

`Proofs/FinalizedRegistry.lean` holds the argument, over the `View` of a state.
`ReachableState.follows` proves that the state transition keeps `Follows`: the registry only
grows, and a validator added after `t` gets an eligibility epoch that starts above the slot of
`t`. The frame of `Proofs/Fulu/IndexAssignment/Frame.lean` carries the eligibility epochs
through each spec step (`EligStep`), and `follows_step` reads one step of it.

## Why this property and the index assignment differ

The index assignment of all validators needs both chains inside one fork: a fork upgrade can
change what a queued deposit becomes (`Proofs/Gloas/IndexAssignment.lean`). This property
does not read the queue, so the Gloas and Heze modules prove it across the upgrades
(`Proofs/Heze/FinalizedValidators.lean` has the statement for all three forks).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Fulu
open EthCLSpecs.Fulu.Const (slotsPerEpoch slotsPerEpochPos farFutureEpoch)
open EthCLSpecs.Proofs.DepositQueue
open EthCLSpecs.Proofs.FinalizedRegistry
open IndexAssignment (registryKeys registryElig EligStep Ctx StepInv finalizedSlot
  processSlots_progress processBlock_keepsFrame)

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The `View` of a Fulu state: its slot, its finalized epoch, the public keys of its registry
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
/-- One step of the chain keeps `Follows`, from what the frame says about the step. The keys
of `x` are a prefix of the keys of `z`, the slot does not fall, and the eligibility epochs
move by `EligStep` at the slot of `x`.

`EligStep` allows two new values, and each starts above the slot of `x`, at a preset with two
or more slots per epoch (`hspe`, which `PresetValid.twoLeSlotsPerEpoch` gives). No slot
reaches the first slot of `FAR_FUTURE_EPOCH`, in `Nat`. The epoch of a slot is below
`2 ^ 63`, so the `uint64` sum `current_epoch + 1` does not wrap. -/
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

variable {anchors : Anchors} {validated : Bool} {nextForkEpoch : Epoch}

/-- The state transition keeps `Follows`: when every anchor follows `T`, so does every
reachable state.

A `slots` step applies `processSlots_progress`. One slot of progress gives the key prefix from
the queue scan, the slot count, and `EligStep`. A `block` step keeps the keys and the slot,
and its frame gives `EligStep`. -/
theorem ReachableState.follows (hspe : 2 ≤ slotsPerEpoch)
    (hA : ∀ u, anchors.fulu u → SimpleStateInvariants u) {T : View BLSPubkey}
    (h0 : ∀ u, anchors.fulu u → Follows slotsPerEpoch T (registryView u)) {w : BeaconState}
    (h : ReachableState anchors validated nextForkEpoch w) :
    Follows slotsPerEpoch T (registryView w) := by
  induction h with
  | anchor ha _ => exact h0 _ ha
  | slots target hv _ hrun ih =>
    have hinv := hv.simpleStateInvariants hA
    refine (processSlots_progress (fun x => Follows slotsPerEpoch T (registryView x)) ?_
      target _ hinv ih).runPure_ok hrun
    intro x z _ _ hprog hPx
    have hs := hprog.slot
    exact follows_step hspe hPx (by omega) (hprog.deposits.2.prefix _ _) hprog.elig
  | @block v w sb hv _ _ hrun _ ih =>
    have hinv := hv.simpleStateInvariants hA
    have hst := (processBlock_keepsFrame sb.message (Ctx.of v true) rfl v
      (StepInv.start v true hinv.registrySizes)).runPure_ok hrun
    obtain ⟨hs, -, hk, -, -, he⟩ := hst
    simp only [Ctx.of] at hs hk he
    exact follows_step hspe ih (by rw [hs]; exact Nat.le_refl _)
      (by rw [hk]; exact List.prefix_refl _) he

/-- The finalized epoch of `w` starts at or before the slot `σ`. With `σ` the slot of a state
on the chain of `w`, that state sits at or after the finalized checkpoint of `w`. -/
def FinalizedAtOrBefore (σ : Slot) (w : BeaconState) : Prop :=
  (computeStartSlotAtEpoch w.finalizedCheckpoint.epoch).toNat ≤ σ.toNat

omit [HasherTag] [Config] [CryptoBackend] in
/-- `FinalizedBelow`, the hypothesis of the index-assignment theorem, is the strict form. -/
theorem FinalizedBelow.atOrBefore {σ : Slot} {w : BeaconState} (h : FinalizedBelow σ w) :
    FinalizedAtOrBefore σ w := Nat.le_of_lt h

omit [HasherTag] [CryptoBackend] in
/-- The hypothesis over the view. `computeStartSlotAtEpoch` multiplies in `uint64`, and
`finalizedSlot_toNat` shows the product does not wrap on a state with
`SimpleStateInvariants`. -/
theorem FinalizedAtOrBefore.view {σ : Slot} {w : BeaconState} (h : FinalizedAtOrBefore σ w)
    (hw : SimpleStateInvariants w) :
    (registryView w).finalizedEpoch.toNat * slotsPerEpoch ≤ σ.toNat := by
  have hf : (computeStartSlotAtEpoch w.finalizedCheckpoint.epoch).toNat
      = w.finalizedCheckpoint.epoch.toNat * slotsPerEpoch := finalizedSlot_toNat hw
  unfold FinalizedAtOrBefore at h
  rw [hf] at h
  exact h

/-- Two Fulu chains agree on the finalized validators of one of them.

* The preset has two or more slots per epoch, as `minimal` and `mainnet` do.
* `t` is a reachable Fulu state, and the anchors satisfy `SimpleStateInvariants`.
* `w'` and `w''` are reachable from `t`: `ReachableState` with the one anchor `t`.
* The finalized epoch of `w'` starts at or before the slot of `t`.
* Validator `i` of `w'` has a finalized `activation_eligibility_epoch`.

Then every index `j` up to `i` is in both registries, with one public key. The proof rests on
Lean's three standard axioms. -/
theorem finalizedValidators_pubkey_eq (hspe : 2 ≤ slotsPerEpoch)
    (hA : ∀ u, anchors.fulu u → SimpleStateInvariants u) {t w' w'' : BeaconState}
    (ht : ReachableState anchors validated nextForkEpoch t)
    (h' : ReachableState (Anchors.only t) validated nextForkEpoch w')
    (h'' : ReachableState (Anchors.only t) validated nextForkEpoch w'')
    (hfin : FinalizedAtOrBefore t.slot w') {i j : Nat} (hji : j ≤ i)
    (hi : i < w'.validators.val.size)
    (he : w'.validators.val[i].activationEligibilityEpoch ≤ w'.finalizedCheckpoint.epoch) :
    ∃ (hj' : j < w'.validators.val.size) (hj'' : j < w''.validators.val.size),
      w''.validators.val[j].pubkey = w'.validators.val[j].pubkey := by
  have hAt : ∀ u, (Anchors.only t).fulu u → SimpleStateInvariants u :=
    fun _ hu => hu ▸ ht.simpleStateInvariants hA
  have h0 : ∀ u, (Anchors.only t).fulu u →
      Follows slotsPerEpoch (registryView t) (registryView u) :=
    fun _ hu => hu ▸ follows_refl t
  have f' := ReachableState.follows hspe hAt h0 h'
  have f'' := ReachableState.follows hspe hAt h0 h''
  -- The view's arrays map `validators`, so its sizes and entries are the registry's.
  have hi' : i < (registryView w').elig.size := by simpa [registryView, registryElig] using hi
  have he' : (registryView w').elig[i] ≤ (registryView w').finalizedEpoch := by
    simpa [registryView, registryElig] using he
  obtain ⟨hj', hj'', e⟩ :=
    keys_eq_of_finalized f' f'' (hfin.view (h'.simpleStateInvariants hAt)) hji hi' he'
  refine ⟨by simpa [registryView, registryKeys] using hj',
    by simpa [registryView, registryKeys] using hj'', ?_⟩
  simpa [registryView, registryKeys] using e

/-- The symmetric form: the index-assignment property, for the validators that are finalized
in both states. One of the two finalized epochs starts at or before the slot of `t`, and
validator `i` has a finalized `activation_eligibility_epoch` in `w'` and in `w''`. Then `i`
has one public key in both. -/
theorem finalizedValidators_pubkey_eq_of_both (hspe : 2 ≤ slotsPerEpoch)
    (hA : ∀ u, anchors.fulu u → SimpleStateInvariants u) {t w' w'' : BeaconState}
    (ht : ReachableState anchors validated nextForkEpoch t)
    (h' : ReachableState (Anchors.only t) validated nextForkEpoch w')
    (h'' : ReachableState (Anchors.only t) validated nextForkEpoch w'')
    (hc : FinalizedAtOrBefore t.slot w' ∨ FinalizedAtOrBefore t.slot w'')
    (i : Nat) (hi' : i < w'.validators.val.size) (hi'' : i < w''.validators.val.size)
    (he' : w'.validators.val[i].activationEligibilityEpoch ≤ w'.finalizedCheckpoint.epoch)
    (he'' : w''.validators.val[i].activationEligibilityEpoch ≤ w''.finalizedCheckpoint.epoch) :
    w'.validators.val[i].pubkey = w''.validators.val[i].pubkey := by
  rcases hc with hc | hc
  · obtain ⟨_, _, e⟩ := finalizedValidators_pubkey_eq hspe hA ht h' h'' hc (Nat.le_refl i) hi' he'
    exact e.symm
  · obtain ⟨_, _, e⟩ := finalizedValidators_pubkey_eq hspe hA ht h'' h' hc (Nat.le_refl i) hi'' he''
    exact e

end

end EthCLSpecs.Proofs.Fulu
