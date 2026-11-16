import EthCLSpecs.Proofs.Gloas.IndexAssignment
import EthCLSpecs.Tests.DepositScenario

/-!
# `EthCLSpecs.Tests.ChainReplay`: an accepted replay of a chain is a reachability proof

`ReachableState` has one constructor per step. Each takes a run equation and a window bound,
and at `validated = true` a block step also takes a signature fact and a state-root fact. A
pin about a chain of fifty blocks would need some two hundred evaluated facts, and each
evaluation would run the chain again from its start.

This module folds the premises into one function. `replayChain fuluSteps gloasSteps u` runs a
chain from the Fulu state `u`: the Fulu steps, the Gloas upgrade, then the Gloas steps. It
makes every check the constructors ask for and returns `none` when one fails.
`replayChain_reachable` proves that an accepted chain ends at a state reachable from `u`. One
evaluation of `replayChain` then stands for the whole derivation, in one pass over the blocks.

The lemmas here evaluate nothing: each is an induction over the step list. The pins that use
them evaluate `replayChain` by `native_decide`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.ChainReplay

open EthCLLib.Spec
open EthCLLib.Proofs (pureState runPure)
open SizzLean (SSZRepr)
open SizzLean.Cache
open EthCLSpecs EthCLSpecs.Proofs
open EthCLSpecs.Proofs.Fulu (FuluRun)
open EthCLSpecs.Proofs.Gloas (GloasRun)
open scoped EthCLSpecs.Gloas.Downgrade

/-! ## Running a step to an option -/

section Run

variable [HasherTag]

/-- The post-state of a run of `act` on `v`, or `none` when the run rejects. -/
def run? {T : Type} [SSZRepr T]
    (act : StateT (SSZ.Box HasherTag.H T) (Except StateTransitionError) Unit) (v : T) : Option T :=
  match runPure act v with
  | .ok (_, w) => some w
  | .error _ => none

/-- A run that `run?` reports is the run equation `ReachableState` takes. -/
theorem runPure_eq_of_run? {T : Type} [SSZRepr T]
    {act : StateT (SSZ.Box HasherTag.H T) (Except StateTransitionError) Unit} {v w : T}
    (h : run? act v = some w) : runPure act v = .ok ((), w) := by
  unfold run? at h
  cases hr : runPure act v with
  | ok p =>
    rw [hr] at h
    injection h with h
    subst h
    rfl
  | error e => rw [hr] at h; cases h

end Run

/-! ## Fulu -/

section Fulu

variable [Gloas.Preset] [HasherTag] [Gloas.Config] [CryptoBackend]

/-- One step of a Fulu chain. -/
inductive FuluStep where
  | slots (target : Fulu.Slot)
  | block (signedBlock : Fulu.SignedBeaconBlock)

/-- Replay Fulu steps from `v` inside the window that ends at slot `limit`, with every check
`ReachableState` makes at `validated = true`. `none` when a step rejects or a check fails. -/
def replayFulu (limit : Nat) : List FuluStep → Fulu.BeaconState → Option Fulu.BeaconState
  | [], v => some v
  | .slots target :: rest, v =>
    if target.toNat ≤ limit then
      match run? (Fulu.processSlots (StateTransition := FuluRun) target) v with
      | some w => replayFulu limit rest w
      | none => none
    else none
  | .block sb :: rest, v =>
    if v.slot.toNat < limit ∧ Fulu.verifyBlockSignature (pureState v) sb = true then
      match run? (Fulu.processBlock (StateTransition := FuluRun) sb.message) v with
      | some w => if sb.message.stateRoot = htr w then replayFulu limit rest w else none
      | none => none
    else none

/-- An accepted Fulu replay ends at a reachable state. Each `if` and `match` of `replayFulu`
that the run passed is one premise of the matching `ReachableState` constructor. -/
theorem replayFulu_reachable {anchors : Fulu.Anchors} {nextForkEpoch : Fulu.Epoch} :
    ∀ (steps : List FuluStep) (v w : Fulu.BeaconState),
      replayFulu (Fulu.forkSlot nextForkEpoch) steps v = some w →
      Fulu.ReachableState anchors true nextForkEpoch v →
      Fulu.ReachableState anchors true nextForkEpoch w := by
  intro steps
  induction steps with
  | nil =>
    intro v w h hv
    simp only [replayFulu, Option.some.injEq] at h
    exact h ▸ hv
  | cons step rest ih =>
    intro v w h hv
    cases step with
    | slots target =>
      simp only [replayFulu] at h
      split at h
      · next hlim =>
        split at h
        · next w1 hrun => exact ih w1 w h (.slots target hv hlim (runPure_eq_of_run? hrun))
        · cases h
      · cases h
    | block sb =>
      simp only [replayFulu] at h
      split at h
      · next hchk =>
        split at h
        · next w1 hrun =>
          split at h
          · next hroot =>
            exact ih w1 w h (.block sb hv hchk.1 (fun _ => hchk.2) (runPure_eq_of_run? hrun)
              (fun _ => hroot))
          · cases h
        · cases h
      · cases h

end Fulu

/-! ## Gloas -/

section Gloas

variable [Gloas.Preset] [HasherTag] [Gloas.Config] [CryptoBackend]

/-- One step of a Gloas chain. -/
inductive GloasStep where
  | slots (target : Gloas.Slot)
  | block (signedBlock : Gloas.SignedBeaconBlock)

/-- Replay Gloas steps from `v` inside the window that ends at slot `limit`, with every check
`ReachableState` makes at `validated = true`. -/
def replayGloas (limit : Nat) : List GloasStep → Gloas.BeaconState → Option Gloas.BeaconState
  | [], v => some v
  | .slots target :: rest, v =>
    if target.toNat ≤ limit then
      match run? (Gloas.processSlots (StateTransition := GloasRun) target) v with
      | some w => replayGloas limit rest w
      | none => none
    else none
  | .block sb :: rest, v =>
    if v.slot.toNat < limit ∧ Gloas.verifyBlockSignature (pureState v) sb = true then
      match run? (Gloas.processBlock (StateTransition := GloasRun) sb.message) v with
      | some w => if sb.message.stateRoot = htr w then replayGloas limit rest w else none
      | none => none
    else none

/-- An accepted Gloas replay ends at a reachable state, as `replayFulu_reachable`. -/
theorem replayGloas_reachable {anchors : Gloas.Anchors} {nextForkEpoch : Gloas.Epoch} :
    ∀ (steps : List GloasStep) (v w : Gloas.BeaconState),
      replayGloas (Gloas.forkSlot nextForkEpoch) steps v = some w →
      Gloas.ReachableState anchors true nextForkEpoch v →
      Gloas.ReachableState anchors true nextForkEpoch w := by
  intro steps
  induction steps with
  | nil =>
    intro v w h hv
    simp only [replayGloas, Option.some.injEq] at h
    exact h ▸ hv
  | cons step rest ih =>
    intro v w h hv
    cases step with
    | slots target =>
      simp only [replayGloas] at h
      split at h
      · next hlim =>
        split at h
        · next w1 hrun => exact ih w1 w h (.slots target hv hlim (runPure_eq_of_run? hrun))
        · cases h
      · cases h
    | block sb =>
      simp only [replayGloas] at h
      split at h
      · next hchk =>
        split at h
        · next w1 hrun =>
          split at h
          · next hroot =>
            exact ih w1 w h (.block sb hv hchk.1 (fun _ => hchk.2) (runPure_eq_of_run? hrun)
              (fun _ => hroot))
          · cases h
        · cases h
      · cases h

/-- The Gloas upgrade of a Fulu state at the fork boundary, with the two trigger checks of the
`upgrade` constructor. -/
def upgrade? (limit : Nat) (u : Fulu.BeaconState) : Option Gloas.BeaconState :=
  if u.slot.toNat = Gloas.forkSlot Gloas.Const.gloasForkEpoch ∧ u.slot.toNat ≤ limit then
    run? (Gloas.completeUpgradeToGloas (StateTransition := GloasRun))
      (Gloas.upgradeToGloas Gloas.Const.gloasForkVersion u)
  else none

/-- A whole chain from a Fulu state: Fulu steps up to the Gloas boundary, the upgrade, then
Gloas steps. A chain that stays in Gloas passes `farFutureEpoch` as its window. -/
def replayChain (fuluSteps : List FuluStep) (gloasSteps : List GloasStep)
    (u : Fulu.BeaconState) : Option Gloas.BeaconState :=
  let limit := Gloas.forkSlot Gloas.Const.farFutureEpoch
  -- The start must lie inside the Fulu window, the premise of the `anchor` constructor.
  if u.slot.toNat ≤ Fulu.forkSlot Gloas.Const.gloasForkEpoch then
    match replayFulu (Fulu.forkSlot Gloas.Const.gloasForkEpoch) fuluSteps u with
    | some u1 =>
      match upgrade? limit u1 with
      | some w0 => replayGloas limit gloasSteps w0
      | none => none
    | none => none
  else none

/-- A chain that `replayChain` accepts ends at a state reachable from its start, with every
block signature and state root checked. -/
theorem replayChain_reachable {fuluSteps : List FuluStep} {gloasSteps : List GloasStep}
    {u : Fulu.BeaconState} {w : Gloas.BeaconState}
    (h : replayChain fuluSteps gloasSteps u = some w) :
    Gloas.ReachableState (Gloas.Anchors.onlyFulu u) true Gloas.Const.farFutureEpoch w := by
  unfold replayChain at h
  simp only at h
  split at h
  · next hwin =>
    split at h
    · next u1 hf =>
      split at h
      · next w0 hup =>
        have hu1 : Fulu.ReachableState (Gloas.Anchors.onlyFulu u).toFulu true
            Gloas.Const.gloasForkEpoch u1 :=
          replayFulu_reachable _ u u1 hf (.anchor rfl hwin)
        unfold upgrade? at hup
        split at hup
        · next htrig =>
          exact replayGloas_reachable _ w0 w h
            (.upgrade hu1 htrig.1 htrig.2 (runPure_eq_of_run? hup))
        · cases hup
      · cases h
    · cases h
  · cases h

end Gloas

end EthCLSpecs.Tests.ChainReplay
