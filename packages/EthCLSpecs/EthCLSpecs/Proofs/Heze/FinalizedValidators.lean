import EthCLSpecs.Proofs.Gloas.FinalizedValidators
import EthCLSpecs.Proofs.Heze.IndexAssignment

/-!
# `EthCLSpecs.Proofs.Heze.FinalizedValidators`: chains of any fork agree on the finalized validators

A validator is finalized in a state when its `activation_eligibility_epoch` is at or below the
state's finalized epoch, or when it comes before such a validator in the registry. This module
has the statement for all three forks: a finalized validator of one chain has the same index
and the same key on every chain that descends from the finalized checkpoint, whatever fork
each state is in. `Proofs/Fulu/FinalizedValidators.lean` states the property inside one fork
and names the argument.

## One statement for three forks

A chain crosses the Gloas and the Heze upgrade, so its states have three types. `ForkState` is
a state of one of them, and `Reachable anchors validated w` is the fork's own `ReachableState`
at the fork's window:

* a Fulu state before the Gloas fork epoch,
* a Gloas state before the Heze fork epoch, which a chain reaches through the Gloas upgrade,
* a Heze state, which a chain reaches through both upgrades.

`finalizedValidators_pubkey_eq_anyFork` takes a reachable `t` of any fork and two states `w'`
and `w''` reachable from `t`, each of any fork. The pair may be a Fulu state and a Gloas
state: a client near a fork boundary holds such pairs. The statement reads the `View` of each
state (`Proofs/FinalizedRegistry.lean`), which is the same four values in every fork.

## What Heze adds to the proof

`upgradeToHeze` copies the slot and maps the registry one validator at a time, so it keeps the
view (`registryView_upgradeToHeze`). The Heze rule for a queued deposit with BLS credentials
(EIP-8365) changes what the queue scan appends. It does not change the two facts the argument
reads: the registry only grows, and a new validator starts at `FAR_FUTURE_EPOCH`.

## The contrast with the index assignment

`IndexAssignmentFromFulu` (`Proofs/Heze/IndexAssignment.lean`) is false.
`FinalizedIndexAssignmentFromFulu` is that statement with two more hypotheses, that the
validator's `activation_eligibility_epoch` is finalized in both states, and
`finalizedIndexAssignmentFromFulu` proves it.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Heze
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochPos farFutureEpoch hezeForkEpoch
  hezeForkVersion)
open EthCLSpecs.Proofs.DepositQueue
open EthCLSpecs.Proofs.FinalizedRegistry
open scoped EthCLSpecs.Heze.Downgrade EthCLSpecs.Gloas.Downgrade
open IndexAssignment (registryKeys registryElig EligStep Ctx StepInv finalizedSlot
  processSlots_progress processBlock_keepsFrame)

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The `View` of a Heze state: its slot, its finalized epoch, the public keys of its registry
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
/-- One step of the chain keeps `Follows`, from what the frame says about the step. The Heze
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

omit [HasherTag] [Config] [CryptoBackend] in
/-- `upgradeToHeze` keeps the view. The upgrade rejects when the eth1 deposit queue has not
drained, so the hypothesis is that it returned a state. That state copies the slot and the
finalized checkpoint, and it maps `validators` with a converter that copies each field. -/
theorem registryView_upgradeToHeze {fv : Version} {u : EthCLSpecs.Gloas.BeaconState}
    {w : BeaconState} (h : upgradeToHeze fv u = .ok w) :
    registryView w = EthCLSpecs.Proofs.Gloas.registryView u := by
  unfold upgradeToHeze at h
  split at h
  · -- The assert passed: the bind returns the record, so `w` is that record.
    injection h with h
    subst h
    simp only [registryView, EthCLSpecs.Proofs.Gloas.registryView, registryKeys, registryElig,
      EthCLSpecs.Proofs.Gloas.IndexAssignment.registryKeys,
      EthCLSpecs.Proofs.Gloas.IndexAssignment.registryElig, Array.map_map]
    rfl
  · cases h

/-! ## The induction -/

variable {anchors : Anchors} {validated : Bool} {nextForkEpoch : Epoch}

/-- The state transition keeps `Follows`, across both upgrades: when every anchor of each fork
follows `T`, so does every reachable Heze state.

The `upgrade` step starts at a reachable Gloas state, which follows `T` by the Gloas theorem,
and `upgradeToHeze` keeps the view. The `slots` and `block` steps are the Fulu ones. -/
theorem ReachableState.follows (hspe : 2 ≤ slotsPerEpoch)
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ u, anchors.heze u → SimpleStateInvariants u) {T : View BLSPubkey}
    (h0F : ∀ u, anchors.fulu u →
      Follows slotsPerEpoch T (EthCLSpecs.Proofs.Fulu.registryView u))
    (h0G : ∀ u, anchors.gloas u →
      Follows slotsPerEpoch T (EthCLSpecs.Proofs.Gloas.registryView u))
    (h0H : ∀ u, anchors.heze u → Follows slotsPerEpoch T (registryView u)) {w : BeaconState}
    (h : ReachableState anchors validated nextForkEpoch w) :
    Follows slotsPerEpoch T (registryView w) := by
  induction h with
  | anchor ha _ => exact h0H _ ha
  | @upgrade u w hu _ _ hup =>
    have fu : Follows slotsPerEpoch T (EthCLSpecs.Proofs.Gloas.registryView u) :=
      EthCLSpecs.Proofs.Gloas.ReachableState.follows hspe hF hG h0F h0G hu
    rw [← registryView_upgradeToHeze hup] at fu
    exact fu
  | slots target hv _ hrun ih =>
    have hinv := hv.simpleStateInvariants hF hG hH
    refine (processSlots_progress (fun x => Follows slotsPerEpoch T (registryView x)) ?_
      target _ hinv ih).runPure_ok hrun
    intro x z _ _ hprog hPx
    have hs := hprog.slot
    exact follows_step hspe hPx (by omega) (hprog.deposits.2.prefix _ _) hprog.elig
  | @block v w sb hv _ _ hrun _ ih =>
    have hinv := hv.simpleStateInvariants hF hG hH
    have hst := (processBlock_keepsFrame sb.message (Ctx.of v true) rfl v
      (StepInv.start v true hinv.registrySizes)).runPure_ok hrun
    obtain ⟨hs, -, hk, -, -, he⟩ := hst
    simp only [Ctx.of] at hs hk he
    exact follows_step hspe ih (by rw [hs]; exact Nat.le_refl _)
      (by rw [hk]; exact List.prefix_refl _) he

/-! ## States of any fork -/

/-- A beacon state of one of the three forks. -/
inductive ForkState where
  | fulu (v : EthCLSpecs.Fulu.BeaconState)
  | gloas (v : EthCLSpecs.Gloas.BeaconState)
  | heze (v : BeaconState)

/-- The `View` of a state of any fork. `slot` is the state's slot in `Nat`, `finalizedEpoch` is
`finalized_checkpoint.epoch`, `keys[i]` is `validators[i].pubkey`, and `elig[i]` is
`validators[i].activation_eligibility_epoch`. -/
def ForkState.view : ForkState → View BLSPubkey
  | .fulu v => EthCLSpecs.Proofs.Fulu.registryView v
  | .gloas v => EthCLSpecs.Proofs.Gloas.registryView v
  | .heze v => registryView v

/-- `SimpleStateInvariants` of the state's own fork. -/
def ForkState.Invariants : ForkState → Prop
  | .fulu v => EthCLSpecs.Proofs.Fulu.SimpleStateInvariants v
  | .gloas v => EthCLSpecs.Proofs.Gloas.SimpleStateInvariants v
  | .heze v => SimpleStateInvariants v

/-- The anchor set that holds the one state `t`, of whichever fork. Every state reachable from
it descends from `t`, so `Reachable (Anchors.onlyState t)` reads "reachable from `t`". -/
def Anchors.onlyState : ForkState → Anchors
  | .fulu u => { fulu := (· = u), gloas := fun _ => False, heze := fun _ => False }
  | .gloas u => { fulu := fun _ => False, gloas := (· = u), heze := fun _ => False }
  | .heze u => { fulu := fun _ => False, gloas := fun _ => False, heze := (· = u) }

/-- The states of any fork that the state transition reaches from `anchors`. Each case is the
fork's own `ReachableState` at the fork's window: a Fulu state before the Gloas fork epoch, a
Gloas state before the Heze fork epoch, and a Heze state with no later fork. The windows are
the ones the `upgrade` steps of the Gloas and Heze `ReachableState` read. -/
def Reachable (anchors : Anchors) (validated : Bool) : ForkState → Prop
  | .fulu v => EthCLSpecs.Proofs.Fulu.ReachableState anchors.toFulu validated
      EthCLSpecs.Gloas.Const.gloasForkEpoch v
  | .gloas v => EthCLSpecs.Proofs.Gloas.ReachableState anchors.toGloas validated hezeForkEpoch v
  | .heze v => ReachableState anchors validated farFutureEpoch v

/-- A reachable state of any fork satisfies its fork's `SimpleStateInvariants`. -/
theorem Reachable.invariants
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ u, anchors.heze u → SimpleStateInvariants u) {w : ForkState}
    (h : Reachable anchors validated w) : w.Invariants := by
  cases w with
  | fulu v => exact EthCLSpecs.Proofs.Fulu.ReachableState.simpleStateInvariants hF h
  | gloas v => exact EthCLSpecs.Proofs.Gloas.ReachableState.simpleStateInvariants hF hG h
  | heze v => exact ReachableState.simpleStateInvariants hF hG hH h

/-- A state of any fork reachable from `t` follows `t`. The anchor set holds `t` alone, so the
premise of each fork's `follows` theorem is `follows_refl` for the fork of `t`, and it is
empty for the other two. -/
theorem Reachable.follows (hspe : 2 ≤ slotsPerEpoch) {t w : ForkState} (ht : t.Invariants)
    (h : Reachable (Anchors.onlyState t) validated w) :
    Follows slotsPerEpoch t.view w.view := by
  cases t with
  | fulu t =>
    have hF : ∀ u, u = t → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u := fun _ hu => hu ▸ ht
    have h0F : ∀ u, u = t → Follows slotsPerEpoch (EthCLSpecs.Proofs.Fulu.registryView t)
        (EthCLSpecs.Proofs.Fulu.registryView u) :=
      fun _ hu => hu ▸ EthCLSpecs.Proofs.Fulu.follows_refl t
    cases w with
    | fulu w => exact EthCLSpecs.Proofs.Fulu.ReachableState.follows hspe hF h0F h
    | gloas w =>
      exact EthCLSpecs.Proofs.Gloas.ReachableState.follows hspe hF (fun _ hu => False.elim hu) h0F
        (fun _ hu => False.elim hu) h
    | heze w =>
      exact ReachableState.follows hspe hF (fun _ hu => False.elim hu) (fun _ hu => False.elim hu) h0F
        (fun _ hu => False.elim hu) (fun _ hu => False.elim hu) h
  | gloas t =>
    have hG : ∀ u, u = t → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u :=
      fun _ hu => hu ▸ ht
    have h0G : ∀ u, u = t → Follows slotsPerEpoch (EthCLSpecs.Proofs.Gloas.registryView t)
        (EthCLSpecs.Proofs.Gloas.registryView u) :=
      fun _ hu => hu ▸ EthCLSpecs.Proofs.Gloas.follows_refl t
    cases w with
    | fulu w =>
      -- No Fulu state descends from a Gloas state: the anchor set holds no Fulu state.
      exact (EthCLSpecs.Proofs.Fulu.ReachableState.false_of_no_anchor (fun _ hu => hu) h).elim
    | gloas w =>
      exact EthCLSpecs.Proofs.Gloas.ReachableState.follows hspe (fun _ hu => False.elim hu) hG
        (fun _ hu => False.elim hu) h0G h
    | heze w =>
      exact ReachableState.follows hspe (fun _ hu => False.elim hu) hG (fun _ hu => False.elim hu)
        (fun _ hu => False.elim hu) h0G (fun _ hu => False.elim hu) h
  | heze t =>
    have hH : ∀ u, u = t → SimpleStateInvariants u := fun _ hu => hu ▸ ht
    have h0H : ∀ u, u = t → Follows slotsPerEpoch (registryView t) (registryView u) :=
      fun _ hu => hu ▸ follows_refl t
    cases w with
    | fulu w =>
      exact (EthCLSpecs.Proofs.Fulu.ReachableState.false_of_no_anchor (fun _ hu => hu) h).elim
    | gloas w =>
      exact (EthCLSpecs.Proofs.Gloas.ReachableState.false_of_no_anchor (fun _ hu => hu)
        (fun _ hu => hu) h).elim
    | heze w =>
      exact ReachableState.follows hspe (fun _ hu => False.elim hu) (fun _ hu => False.elim hu) hH
        (fun _ hu => False.elim hu) (fun _ hu => False.elim hu) h0H h

/-- Two chains, in any forks, agree on the finalized validators of one of them.

* The preset has two or more slots per epoch, as `minimal` and `mainnet` do.
* `t` is a reachable state of any fork, and the anchors satisfy their fork's
  `SimpleStateInvariants`.
* `w'` and `w''` are states of any fork reachable from `t`. A chain from `t` to either may
  cross the Gloas upgrade, the Heze upgrade, or both.
* The finalized epoch of `w'` starts at or before the slot of `t`. The product is in `Nat`.
  With `t` the state of the finalized checkpoint of `w'`, the two sides are equal, and
  "reachable from `t`" reads "descends from the finalized checkpoint of `w'`".
* Validator `i` of `w'` has `activation_eligibility_epoch ≤ finalized_checkpoint.epoch`.

Then every index `j` up to `i` is in both registries, with one public key. `w''` needs no
hypothesis on its own finality. The proof rests on Lean's three standard axioms and on no
hash or signature assumption. -/
theorem finalizedValidators_pubkey_eq_anyFork (hspe : 2 ≤ slotsPerEpoch)
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ u, anchors.heze u → SimpleStateInvariants u) {t w' w'' : ForkState}
    (ht : Reachable anchors validated t)
    (h' : Reachable (Anchors.onlyState t) validated w')
    (h'' : Reachable (Anchors.onlyState t) validated w'')
    (hfin : w'.view.finalizedEpoch.toNat * slotsPerEpoch ≤ t.view.slot) {i j : Nat}
    (hji : j ≤ i) (hi : i < w'.view.elig.size)
    (he : w'.view.elig[i] ≤ w'.view.finalizedEpoch) :
    ∃ (hj' : j < w'.view.keys.size) (hj'' : j < w''.view.keys.size),
      w''.view.keys[j] = w'.view.keys[j] :=
  have hinv := ht.invariants hF hG hH
  keys_eq_of_finalized (h'.follows hspe hinv) (h''.follows hspe hinv) hfin hji hi he

/-- The symmetric form: the index-assignment property, for the validators that are finalized
in both states. One of the two finalized epochs starts at or before the slot of `t`, and
validator `i` has a finalized `activation_eligibility_epoch` in `w'` and in `w''`. Then `i`
has one public key in both. -/
theorem finalizedValidators_pubkey_eq_of_both_anyFork (hspe : 2 ≤ slotsPerEpoch)
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ u, anchors.heze u → SimpleStateInvariants u) {t w' w'' : ForkState}
    (ht : Reachable anchors validated t)
    (h' : Reachable (Anchors.onlyState t) validated w')
    (h'' : Reachable (Anchors.onlyState t) validated w'')
    (hfin : w'.view.finalizedEpoch.toNat * slotsPerEpoch ≤ t.view.slot ∨
      w''.view.finalizedEpoch.toNat * slotsPerEpoch ≤ t.view.slot)
    {i : Nat} (hi' : i < w'.view.elig.size) (hi'' : i < w''.view.elig.size)
    (he' : w'.view.elig[i] ≤ w'.view.finalizedEpoch)
    (he'' : w''.view.elig[i] ≤ w''.view.finalizedEpoch) :
    ∃ (h₁ : i < w'.view.keys.size) (h₂ : i < w''.view.keys.size),
      w'.view.keys[i] = w''.view.keys[i] :=
  have hinv := ht.invariants hF hG hH
  keys_eq_of_both_finalized (h'.follows hspe hinv) (h''.follows hspe hinv) hfin hi' hi'' he' he''

/-! ## Heze end states -/

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

end

/-! ## A Fulu common state

The statements below name a Fulu state `t` and Heze states reachable from it, as
`IndexAssignmentFromFulu` does. Each chain passes the Gloas and Heze upgrades on its own. -/

section FromFulu

variable [Preset] [HasherTag] [Config] [CryptoBackend]
variable {validated : Bool}

/-- Two Heze chains from a Fulu state agree on the finalized validators of one of them.

* The preset has two or more slots per epoch.
* `t` is a reachable Fulu state, and the Fulu anchors satisfy `SimpleStateInvariants`.
* `w'` and `w''` are Heze states reachable from `t`, through both upgrades:
  `ReachableState` with the one Fulu anchor `t`.
* The finalized epoch of `w'` starts at or before the slot of `t`.
* Validator `i` of `w'` has a finalized `activation_eligibility_epoch`.

Then every index `j` up to `i` is in both registries, with one public key. -/
theorem finalizedValidators_pubkey_eq_fromFulu (hspe : 2 ≤ slotsPerEpoch)
    {anchors : EthCLSpecs.Proofs.Fulu.Anchors}
    (hA : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    {t : EthCLSpecs.Fulu.BeaconState} {w' w'' : BeaconState}
    (ht : EthCLSpecs.Proofs.Fulu.ReachableState anchors validated
      EthCLSpecs.Gloas.Const.gloasForkEpoch t)
    (h' : ReachableState (Anchors.onlyFulu t) validated farFutureEpoch w')
    (h'' : ReachableState (Anchors.onlyFulu t) validated farFutureEpoch w'')
    (hfin : FinalizedAtOrBefore t.slot w') {i j : Nat} (hji : j ≤ i)
    (hi : i < w'.validators.val.size)
    (he : w'.validators.val[i].activationEligibilityEpoch ≤ w'.finalizedCheckpoint.epoch) :
    ∃ (hj' : j < w'.validators.val.size) (hj'' : j < w''.validators.val.size),
      w''.validators.val[j].pubkey = w'.validators.val[j].pubkey := by
  have hinv : (ForkState.fulu t).Invariants :=
    EthCLSpecs.Proofs.Fulu.ReachableState.simpleStateInvariants hA ht
  -- `Anchors.onlyFulu t` is `Anchors.onlyState (.fulu t)`, by unfolding.
  have r' : Reachable (Anchors.onlyState (.fulu t)) validated (.heze w') := h'
  have r'' : Reachable (Anchors.onlyState (.fulu t)) validated (.heze w'') := h''
  have hw' : SimpleStateInvariants w' :=
    Reachable.invariants (fun _ hu => hu ▸ hinv) (fun _ hu => False.elim hu) (fun _ hu => False.elim hu) r'
  exact pubkey_eq_of_views (r'.follows hspe hinv) (r''.follows hspe hinv) (hfin.view hw') hji
    hi he

/-- `IndexAssignmentFromFulu` for the validators that are finalized in both states: the
hypotheses of that statement, and two more. Validator `i` has an
`activation_eligibility_epoch` at or below the finalized epoch, in `w'` and in `w''`.

`IndexAssignmentFromFulu` is false (`Tests/HezeValidatorIndexPins.lean`), and this statement
is a theorem (`finalizedIndexAssignmentFromFulu`). -/
def FinalizedIndexAssignmentFromFulu : Prop :=
  ∀ (anchors : EthCLSpecs.Proofs.Fulu.Anchors) (t : EthCLSpecs.Fulu.BeaconState)
    (w' w'' : BeaconState),
    (∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u) →
    EthCLSpecs.Proofs.Fulu.ReachableState anchors true EthCLSpecs.Gloas.Const.gloasForkEpoch t →
    ReachableState (Anchors.onlyFulu t) true farFutureEpoch w' →
    ReachableState (Anchors.onlyFulu t) true farFutureEpoch w'' →
    CompatibleFinality t.slot w' w'' →
    ∀ (i : Nat) (h' : i < w'.validators.val.size) (h'' : i < w''.validators.val.size),
      w'.validators.val[i].activationEligibilityEpoch ≤ w'.finalizedCheckpoint.epoch →
      w''.validators.val[i].activationEligibilityEpoch ≤ w''.finalizedCheckpoint.epoch →
      w'.validators.val[i].pubkey = w''.validators.val[i].pubkey

/-- The index assignment of the finalized validators is stable across the Gloas and Heze
upgrades, at a preset with two or more slots per epoch. `CompatibleFinality` gives
`FinalizedAtOrBefore` for one of the two states, and
`finalizedValidators_pubkey_eq_fromFulu` applies from that state. -/
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

end EthCLSpecs.Proofs.Heze
