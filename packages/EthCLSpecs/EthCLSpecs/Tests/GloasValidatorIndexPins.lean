import EthCLSpecs.Proofs.Gloas.IndexAssignment
import EthCLSpecs.Tests.DepositScenario

/-!
# `EthCLSpecs.Tests.GloasValidatorIndexPins`: the Gloas upgrade splits the index assignment

A validator index is a position in `state.validators`. A client that keeps one map from index
to public key for every chain it follows relies on one property. Two chains with compatible
finality hold the same public key at every index both have assigned. This module proves the
property false across the Gloas upgrade, with a concrete pair of chains.

## The property inside one fork

`process_pending_deposits` is the only step that appends to the registry. It takes deposits
from the front of the queue, in queue order, and stops at the first deposit whose slot is not
finalized. A postponed deposit names a validator that exists already. So two chains with one
finalized prefix create validators in one order, each at the pace its own churn allows.
`indexAssignment_of_compatibleFinality` proves it for Fulu chains
(`Proofs/Fulu/IndexAssignment.lean`) and for Gloas chains (`Proofs/Gloas/IndexAssignment.lean`).

## Why the upgrade breaks it

`onboardBuildersFromPendingDeposits` (`Gloas/Operations.lean:160-180`) runs once, at the
fork. It takes out of the queue each deposit that carries the builder credential prefix
`0xB0` and names no validator, and it makes a builder from that deposit. Before the fork,
Fulu's `ppdLoop` (`Fulu/EpochProcessing.lean:234-267`) makes a validator from the same
deposit. The outcome depends on one fact: did the queue scan reach the deposit before the
fork epoch?

The scan's progress belongs to one chain. It depends on when that chain finalized the
deposit's slot, and on the churn the earlier deposits consumed. Two chains can share the
deposit and the finalized checkpoint and still differ in both.

## The scenario

The preset is `minimal`, and the config schedules Gloas at epoch 65. `DepositScenario` builds
the common ancestor, a Fulu state at slot 519 with sixteen validators and a finalized
checkpoint at epoch 62. Its deposit queue holds three deposits, all from finalized slots:

1. `topUp 64`: 64 ETH for validator 1. The amount equals the churn of one epoch.
2. `builderDeposit`: 32 ETH for the new key 101, with `0xB0` credentials and a valid signature.
3. `validatorDeposit`: 32 ETH for the new key 102, with `0x01` credentials.

Chain A has no block at slot 519. Chain B has a block there that carries a voluntary exit of
validator 1.

| Step | Chain A | Chain B |
| --- | --- | --- |
| Epoch 64 transition, Fulu | `topUp` applies and uses the churn; the scan stops | validator 1 is exiting, so `topUp` is postponed; keys 101 and 102 join, at 16 and 17 |
| Upgrade at slot 520 | `builderDeposit` leaves the queue and becomes a builder | no builder deposit is left |
| Epoch 65 transition, Gloas | `validatorDeposit` joins, at index 16 | no change to the registry |

At slot 528 both chains hold the ancestor's finalized checkpoint. Index 16 holds key 102 on
chain A and key 101 on chain B.

The exit is one lever among several. Finality timing is another. Fulu's scan stops at a
deposit whose slot is above the finalized slot, so a chain that finalizes the deposits' slots
one epoch after its sibling splits the same way, with no exit and no top-up. The upstream
pyspec reproduces that variant from a genesis state, at v1.7.0-beta.4 and at its current
development head (`SPECS_ARCHITECTURE.md` §11.6). `GloasPyspecReplayPins` replays the
pyspec's blocks for that variant and proves the same split.

## What the theorem states

`validatorIndex_diverges_across_upgrade` gives two Gloas states. Both are reachable from one
Fulu state at `validated = true`, so every block signature and state root is checked. Both sit
at one slot, and both hold the finalized checkpoint of the common Fulu state. They disagree on
the public key at an index both have assigned. The anchor set holds one state
(`Anchors.onlyFulu`), which makes `ReachableState` the relation "reachable from that state".

`indexAssignmentFromFulu_false` is the same fact as a negation. `IndexAssignmentFromFulu`
(`Proofs/Gloas/IndexAssignment.lean`) is the statement of the in-fork theorem
`indexAssignment_of_compatibleFinality` with a Fulu state as the common state: the same
`ReachableState` premises and the same `CompatibleFinality`. It is false. The ancestor
satisfies `SimpleStateInvariants` and the config satisfies `ConfigValid`, so the pair meets
each hypothesis of the in-fork theorem, and the one difference is that the upgrade lies after
the common ancestor.

## Trust, and why this is a pin

The crypto backend is `CryptoBackend.ffi`, and every signature in the scenario is a blst
signature made from a known secret key. The hasher is the FFI SHA-256. Each concrete fact
closes by `native_decide`, which evaluates the compiled state transition, so each theorem
trusts the compiler and the two native libraries. `fastHasherTag` names the FFI `Sha256`,
whose `Hasher` instance has a law proved from `sha256BatchCombine_eq_spec` and
`sha256Combine_eq_spec`, so `#print axioms` lists both. No step here rewrites with them.

The proof-coverage audit keeps compiled evaluation out of `EthCLSpecs/Proofs/`, so the theorem
sits with the pins. Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.GloasValidatorIndexPins

open EthCLLib.Spec
open EthCLLib.Proofs (pureState runPure)
open EthCLSpecs EthCLSpecs.Proofs
open EthCLSpecs.Proofs.Gloas (GloasRun)
open EthCLSpecs.Gloas.Const (farFutureEpoch gloasForkEpoch gloasForkVersion)
open EthCLSpecs.Tests.DepositScenario
open scoped EthCLSpecs.Gloas.Downgrade

/-! ## The configuration -/

/-- The Gloas `minimal` preset: eight slots per epoch. -/
@[reducible] def preset : Gloas.Preset := Gloas.minimal

/-- The `minimal` config with Gloas scheduled at epoch 65. The shipped config leaves
`GLOAS_FORK_EPOCH` at `FAR_FUTURE_EPOCH`, so the scenario sets its own. -/
@[reducible] def config : Gloas.Config := { Gloas.minimalConfig with gloasForkEpoch := 65 }

-- The four instances every declaration below resolves. `local` keeps them inside this module.
-- The Fulu `Preset` and `Config` come from the first two through the `Downgrade` bridge.
attribute [local instance] preset config fastHasherTag CryptoBackend.ffi

/-! ## The queue and the two chains -/

/-- 32 ETH for the new key 101, with builder credentials. Fulu makes a validator from it. The
Gloas upgrade makes a builder from it. -/
def builderDeposit : Fulu.PendingDeposit := newKeyDeposit 101 0xB0 481

/-- 32 ETH for the new key 102, an ordinary validator deposit. -/
def validatorDeposit : Fulu.PendingDeposit := newKeyDeposit 102 0x01 482

/-- The ancestor's deposit queue. `topUp 64` equals the 64 ETH churn of one epoch, so it stops
the scan on the chain that applies it. -/
def queue : Array Fulu.PendingDeposit := #[topUp 64, builderDeposit, validatorDeposit]

/-- The common ancestor: the scenario's Fulu state at slot 519, with `queue`. -/
def ancestor : Fulu.BeaconState := anchor queue

/-- Chain A at the boundary: no block at slot 519. The registry has its sixteen validators,
and `builderDeposit` is at the front of the queue. -/
def fuluA : Fulu.BeaconState := quietBoundary queue

/-- Chain A after the upgrade. `builderDeposit` has left the queue and is a builder. -/
def upgradedA : Gloas.BeaconState :=
  postOf (Gloas.completeUpgradeToGloas (StateTransition := GloasRun))
    (Gloas.upgradeToGloas gloasForkVersion fuluA)

/-- Chain A one epoch later, at slot 528. `validatorDeposit` has joined at index 16. -/
def chainA : Gloas.BeaconState :=
  postOf (Gloas.processSlots (StateTransition := GloasRun) 528) upgradedA

/-- Chain B at the boundary: the exit block at slot 519. Keys 101 and 102 are validators 16
and 17, made under the Fulu rules. -/
def fuluB : Fulu.BeaconState := exitBoundary queue

/-- Chain B after the upgrade. The queue holds no builder deposit, so no builder appears. -/
def upgradedB : Gloas.BeaconState :=
  postOf (Gloas.completeUpgradeToGloas (StateTransition := GloasRun))
    (Gloas.upgradeToGloas gloasForkVersion fuluB)

/-- Chain B one epoch later, at slot 528, the slot of `chainA`. -/
def chainB : Gloas.BeaconState :=
  postOf (Gloas.processSlots (StateTransition := GloasRun) 528) upgradedB

/-! ## Both chains are reachable from the ancestor

Each step is one constructor of `ReachableState`. The run equations come from
`runPure_eq_of_succeeds`, and `native_decide` evaluates each `succeeds`, each window bound,
the block signature, and the state root. -/

/-- Chain A reaches the Gloas boundary inside the Fulu window. -/
theorem reachable_fuluA :
    Fulu.ReachableState (Gloas.Anchors.onlyFulu ancestor).toFulu true gloasForkEpoch fuluA :=
  .slots 520 (.anchor rfl (by native_decide)) (by native_decide)
    (runPure_eq_of_succeeds (by native_decide))

/-- Chain A is reachable from the ancestor: the upgrade, then one epoch of empty slots. -/
theorem reachable_chainA :
    Gloas.ReachableState (Gloas.Anchors.onlyFulu ancestor) true farFutureEpoch chainA :=
  .slots 528
    (.upgrade reachable_fuluA (by native_decide) (by native_decide)
      (runPure_eq_of_succeeds (by native_decide)))
    (by native_decide) (runPure_eq_of_succeeds (by native_decide))

/-- Chain B reaches the Gloas boundary inside the Fulu window. Its block at slot 519 has a
signature that verifies under the proposer's key, and a state root that is the root of the
block's post-state. -/
theorem reachable_fuluB :
    Fulu.ReachableState (Gloas.Anchors.onlyFulu ancestor).toFulu true gloasForkEpoch fuluB :=
  .slots 520
    (.block (signedExitBlock queue) (.anchor rfl (by native_decide)) (by native_decide)
      (fun _ => by native_decide) (runPure_eq_of_succeeds (by native_decide))
      (fun _ => by native_decide))
    (by native_decide) (runPure_eq_of_succeeds (by native_decide))

/-- Chain B is reachable from the ancestor: the upgrade, then one epoch of empty slots. -/
theorem reachable_chainB :
    Gloas.ReachableState (Gloas.Anchors.onlyFulu ancestor) true farFutureEpoch chainB :=
  .slots 528
    (.upgrade reachable_fuluB (by native_decide) (by native_decide)
      (runPure_eq_of_succeeds (by native_decide)))
    (by native_decide) (runPure_eq_of_succeeds (by native_decide))

/-! ## What each chain did with the builder deposit -/

/-- The path of the two new keys through each chain.

* Chain A enters the fork with its sixteen validators, and the upgrade makes key 101 the one
  builder. One epoch later key 102 is validator 16.
* Chain B enters the fork with key 101 at index 16 and key 102 at index 17. The upgrade makes
  no builder, and the registry does not change after it. -/
theorem scenario_anatomy :
    fuluA.validators.val.size = 16 ∧
    upgradedA.builders.val.map (·.pubkey) = #[pubkey 101] ∧
    (chainA.validators.val.map (·.pubkey)).extract 16 = #[pubkey 102] ∧
    (fuluB.validators.val.map (·.pubkey)).extract 16 = #[pubkey 101, pubkey 102] ∧
    upgradedB.builders.val.size = 0 ∧
    (chainB.validators.val.map (·.pubkey)).extract 16 = #[pubkey 101, pubkey 102] := by
  native_decide

/-! ## The theorem -/

/-- Two chains with one finalized checkpoint can assign one validator index to two public
keys, when the Gloas upgrade lies between their common ancestor and their heads.

The statement, at the `minimal` preset with Gloas at epoch 65:

* `u` is a Fulu state, and it is the only anchor, so both `ReachableState` facts read
  "reachable from `u`". The flag is `true`: every block signature and state root is checked.
* `w'` and `w''` are Gloas states at one slot.
* Their finalized checkpoints are equal, and equal to the checkpoint of `u`. Neither chain
  finalized a block after `u`, so the two finalities are compatible in the strongest sense.
* At index `i`, which both registries hold, the public keys differ.

The witnesses are `chainA` and `chainB`, and the index is 16. `scenario_anatomy` records why:
`onboardBuildersFromPendingDeposits` made a builder from a deposit on one chain, and Fulu's
`processPendingDeposits` had made a validator from it on the other.

The proof evaluates the compiled state transition by `native_decide`, on the FFI SHA-256 and
the blst backend, so it trusts the compiler and the two native libraries. The two SHA-256
equivalence axioms appear in its axiom list through the `Hasher` instance of the FFI
`Sha256`; the module docstring says why. -/
theorem validatorIndex_diverges_across_upgrade :
    ∃ (u : Fulu.BeaconState) (w' w'' : Gloas.BeaconState),
      Gloas.ReachableState (Gloas.Anchors.onlyFulu u) true farFutureEpoch w' ∧
      Gloas.ReachableState (Gloas.Anchors.onlyFulu u) true farFutureEpoch w'' ∧
      w'.slot = w''.slot ∧
      w'.finalizedCheckpoint = w''.finalizedCheckpoint ∧
      w'.finalizedCheckpoint.epoch = u.finalizedCheckpoint.epoch ∧
      w'.finalizedCheckpoint.root = u.finalizedCheckpoint.root ∧
      ∃ (i : Nat) (h' : i < w'.validators.val.size) (h'' : i < w''.validators.val.size),
        w'.validators.val[i].pubkey ≠ w''.validators.val[i].pubkey :=
  ⟨ancestor, chainA, chainB, reachable_chainA, reachable_chainB, by native_decide,
    by native_decide, by native_decide, by native_decide,
    16, by native_decide, by native_decide, by native_decide⟩

/-! ## The property, negated -/

/-- The scenario's config satisfies the rules the proofs put on a config. -/
theorem config_valid : @Gloas.ConfigValid preset config := by
  apply @Gloas.ConfigValid.mk preset config <;> decide

/-- The common ancestor satisfies `SimpleStateInvariants`, the hypothesis the in-fork theorem
puts on its anchors: the header is at slot 518 of 519, the five registry lists have sixteen
entries, the three checkpoints are at epoch 62 of 64, and the `fork` field names Fulu. -/
theorem ancestor_invariants : Fulu.SimpleStateInvariants ancestor :=
  ⟨by native_decide,
    ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩,
    ⟨by native_decide, by native_decide, by native_decide⟩,
    ⟨by native_decide, by native_decide⟩⟩

/-- The index assignment is not stable across the Gloas upgrade: `IndexAssignmentFromFulu` is false.

`IndexAssignmentFromFulu` is the statement of the in-fork theorem
`indexAssignment_of_compatibleFinality` with a Fulu state as the common state. The witness is
the ancestor, which is reachable as an anchor and satisfies `SimpleStateInvariants`, with
`chainA` and `chainB` at index 16. Both chains have finalized no slot at or after the slot of
the ancestor: their finalized epoch is 62, which starts at slot 496, and the ancestor is at
slot 519. The proof trusts the compiler and the two native libraries, as
`validatorIndex_diverges_across_upgrade` does. -/
theorem indexAssignmentFromFulu_false : ¬ Gloas.IndexAssignmentFromFulu :=
  Gloas.not_indexAssignmentFromFulu (anchors := Fulu.Anchors.only ancestor)
    (fun _ h => h ▸ ancestor_invariants) (.anchor rfl (by native_decide))
    reachable_chainA reachable_chainB
    (Or.inl (by unfold Gloas.FinalizedBelow; native_decide))
    (i := 16) (by native_decide) (by native_decide) (by native_decide)

end EthCLSpecs.Tests.GloasValidatorIndexPins
