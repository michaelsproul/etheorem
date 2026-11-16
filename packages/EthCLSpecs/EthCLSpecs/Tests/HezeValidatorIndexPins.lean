import EthCLSpecs.Proofs.Heze.IndexAssignment
import EthCLSpecs.Tests.DepositScenario

/-!
# `EthCLSpecs.Tests.HezeValidatorIndexPins`: the Heze upgrade splits the index assignment

The Heze counterpart of `GloasValidatorIndexPins`, which states the property and the argument
for one fork. Two chains with one finalized checkpoint can assign one validator index to two
public keys, when the Heze upgrade lies between their common ancestor and their heads.

## Why the upgrade breaks it

Heze's `applyPendingDeposit` (`Heze/EpochProcessing.lean:86-95`) carries EIP-8365. It drops a
deposit that would make a new validator with BLS credentials, prefix `0x00`, and the rule
covers a deposit submitted before Heze. The Fulu and Gloas rules make a validator from the
same deposit. The outcome depends on one fact: did the queue scan reach the deposit before
the Heze fork epoch? As at the Gloas upgrade, the scan's progress belongs to one chain.

The rule changes what a queued deposit becomes, and the change takes effect at a fixed epoch.
Any fork with such a change splits the assignment in the same way.

`indexAssignmentFromFulu_false` states the result as a negation: `IndexAssignmentFromFulu`
(`Proofs/Heze/IndexAssignment.lean`), the statement of the in-fork theorem with a Fulu state
as the common state, is false. Inside Heze the property holds, by
`indexAssignment_of_compatibleFinality` in the same module.

## The scenario

The preset is `minimal`. The config schedules Gloas at epoch 65 and Heze at epoch 66.
`DepositScenario` builds the common ancestor, a Fulu state at slot 519. Its queue:

1. `topUp 128`: 128 ETH for validator 1, twice the churn of one epoch.
2. `blsDeposit`: 32 ETH for the new key 101, with `0x00` credentials and a valid signature.
3. `validatorDeposit`: 32 ETH for the new key 102, with `0x01` credentials.

Chain A has no block at slot 519. Chain B has a block there that carries a voluntary exit of
validator 1. Both chains pass the Gloas upgrade at slot 520 with no effect on the queue, since
no deposit has builder credentials.

| Step | Chain A | Chain B |
| --- | --- | --- |
| Epoch 64 transition, Fulu | `topUp` exceeds the churn; the scan stops and saves 64 ETH | `topUp` is postponed; keys 101 and 102 join, at 16 and 17 |
| Epoch 65 transition, Gloas | `topUp` applies and uses the saved churn; the scan stops | no change to the registry |
| Upgrade at slot 528 | `blsDeposit` is at the front of the queue | the queue holds `topUp` alone |
| Epoch 66 transition, Heze | `blsDeposit` is dropped; `validatorDeposit` joins, at index 16 | no change to the registry |

At slot 536 both chains hold the ancestor's finalized checkpoint. Index 16 holds key 102 on
chain A and key 101 on chain B.

The ancestor is a Fulu state because the one block of the scenario is then a Fulu block, the
block `DepositScenario` builds. A Gloas ancestor one epoch before the Heze boundary gives the
same split.

## Trust, and why this is a pin

As in `GloasValidatorIndexPins`: `CryptoBackend.ffi` with blst signatures from known keys,
the FFI SHA-256, and `native_decide` for each concrete fact. Each theorem trusts the compiler
and the two native libraries, and lists the two SHA-256 equivalence axioms through the
`Hasher` instance of the FFI `Sha256`. Fires on `lake build EthCLSpecsTests`
(`just ethcl-test`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.HezeValidatorIndexPins

open EthCLLib.Spec
open EthCLLib.Proofs (pureState runPure)
open EthCLSpecs EthCLSpecs.Proofs
open EthCLSpecs.Proofs.Gloas (GloasRun)
open EthCLSpecs.Proofs.Heze (HezeRun)
open EthCLSpecs.Heze.Const (farFutureEpoch hezeForkEpoch hezeForkVersion)
open EthCLSpecs.Tests.DepositScenario
open scoped EthCLSpecs.Heze.Downgrade EthCLSpecs.Gloas.Downgrade

/-! ## The configuration -/

/-- The Heze `minimal` preset: eight slots per epoch. -/
@[reducible] def preset : Heze.Preset := Heze.minimal

/-- The `minimal` config with Gloas scheduled at epoch 65 and Heze at epoch 66. The shipped
config leaves both at `FAR_FUTURE_EPOCH`. -/
@[reducible] def config : Heze.Config :=
  { Heze.minimalConfig with gloasForkEpoch := 65, hezeForkEpoch := 66 }

-- The four instances every declaration below resolves. `local` keeps them inside this module.
-- The Gloas and Fulu `Preset` and `Config` come from the first two through the two
-- `Downgrade` bridges.
attribute [local instance] preset config fastHasherTag CryptoBackend.ffi

/-! ## The queue and the two chains -/

/-- 32 ETH for the new key 101, with BLS credentials. Fulu and Gloas make a validator from
it. Heze drops it. -/
def blsDeposit : Fulu.PendingDeposit := newKeyDeposit 101 0x00 481

/-- 32 ETH for the new key 102, an ordinary validator deposit. -/
def validatorDeposit : Fulu.PendingDeposit := newKeyDeposit 102 0x01 482

/-- The ancestor's deposit queue. `topUp 128` is twice the 64 ETH churn of one epoch, so the
chain that applies it needs two epoch transitions to pass it. -/
def queue : Array Fulu.PendingDeposit := #[topUp 128, blsDeposit, validatorDeposit]

/-- The common ancestor: the scenario's Fulu state at slot 519, with `queue`. -/
def ancestor : Fulu.BeaconState := anchor queue

/-- A Fulu state at the Gloas boundary, upgraded and advanced one epoch to the Heze boundary
at slot 528, under the Gloas rules. -/
def gloasEpoch (u : Fulu.BeaconState) : Gloas.BeaconState :=
  postOf (Gloas.processSlots (StateTransition := GloasRun) 528)
    (postOf (Gloas.completeUpgradeToGloas (StateTransition := GloasRun))
      (Gloas.upgradeToGloas Gloas.Const.gloasForkVersion u))

/-- The Heze upgrade of `u`. A rejected upgrade returns the default state;
`upgradeToHeze_eq_ok` tells the two apart. -/
def hezeUpgrade (u : Gloas.BeaconState) : Heze.BeaconState :=
  match Heze.upgradeToHeze hezeForkVersion u with
  | .ok w => w
  | .error _ => default

/-- An upgrade that does not reject ends in `hezeUpgrade`. -/
theorem upgradeToHeze_eq_ok {u : Gloas.BeaconState}
    (h : (Heze.upgradeToHeze hezeForkVersion u).toBool = true) :
    Heze.upgradeToHeze hezeForkVersion u = .ok (hezeUpgrade u) := by
  unfold hezeUpgrade
  cases hr : Heze.upgradeToHeze hezeForkVersion u with
  | ok w => rfl
  | error e => rw [hr] at h; cases h

/-- Chain A at the Gloas boundary: no block at slot 519, and no deposit applied. -/
def fuluA : Fulu.BeaconState := quietBoundary queue

/-- Chain A at the Heze boundary. The Gloas epoch transition applied `topUp`, and
`blsDeposit` is at the front of the queue. -/
def gloasA : Gloas.BeaconState := gloasEpoch fuluA

/-- Chain A one epoch into Heze, at slot 536. Heze dropped `blsDeposit`, and
`validatorDeposit` has joined at index 16. -/
def chainA : Heze.BeaconState :=
  postOf (Heze.processSlots (StateTransition := HezeRun) 536) (hezeUpgrade gloasA)

/-- Chain B at the Gloas boundary: the exit block at slot 519. Keys 101 and 102 are
validators 16 and 17, made under the Fulu rules. -/
def fuluB : Fulu.BeaconState := exitBoundary queue

/-- Chain B at the Heze boundary. -/
def gloasB : Gloas.BeaconState := gloasEpoch fuluB

/-- Chain B one epoch into Heze, at slot 536, the slot of `chainA`. -/
def chainB : Heze.BeaconState :=
  postOf (Heze.processSlots (StateTransition := HezeRun) 536) (hezeUpgrade gloasB)

/-! ## Both chains are reachable from the ancestor -/

/-- Chain A reaches the Gloas boundary inside the Fulu window. -/
theorem reachable_fuluA :
    Fulu.ReachableState (Heze.Anchors.onlyFulu ancestor).toFulu true Gloas.Const.gloasForkEpoch fuluA :=
  .slots 520 (.anchor rfl (by native_decide)) (by native_decide)
    (runPure_eq_of_succeeds (by native_decide))

/-- Chain B reaches the Gloas boundary inside the Fulu window, through its signed block. -/
theorem reachable_fuluB :
    Fulu.ReachableState (Heze.Anchors.onlyFulu ancestor).toFulu true Gloas.Const.gloasForkEpoch fuluB :=
  .slots 520
    (.block (signedExitBlock queue) (.anchor rfl (by native_decide)) (by native_decide)
      (fun _ => by native_decide) (runPure_eq_of_succeeds (by native_decide))
      (fun _ => by native_decide))
    (by native_decide) (runPure_eq_of_succeeds (by native_decide))

/-- Chain A reaches the Heze boundary inside the Gloas window. -/
theorem reachable_gloasA :
    Gloas.ReachableState (Heze.Anchors.onlyFulu ancestor).toGloas true hezeForkEpoch gloasA :=
  .slots 528
    (.upgrade reachable_fuluA (by native_decide) (by native_decide)
      (runPure_eq_of_succeeds (by native_decide)))
    (by native_decide) (runPure_eq_of_succeeds (by native_decide))

/-- Chain B reaches the Heze boundary inside the Gloas window. -/
theorem reachable_gloasB :
    Gloas.ReachableState (Heze.Anchors.onlyFulu ancestor).toGloas true hezeForkEpoch gloasB :=
  .slots 528
    (.upgrade reachable_fuluB (by native_decide) (by native_decide)
      (runPure_eq_of_succeeds (by native_decide)))
    (by native_decide) (runPure_eq_of_succeeds (by native_decide))

/-- Chain A is reachable from the ancestor: the Heze upgrade, then one epoch of empty slots. -/
theorem reachable_chainA :
    Heze.ReachableState (Heze.Anchors.onlyFulu ancestor) true farFutureEpoch chainA :=
  .slots 536
    (.upgrade reachable_gloasA (by native_decide) (by native_decide)
      (upgradeToHeze_eq_ok (by native_decide)))
    (by native_decide) (runPure_eq_of_succeeds (by native_decide))

/-- Chain B is reachable from the ancestor: the Heze upgrade, then one epoch of empty slots. -/
theorem reachable_chainB :
    Heze.ReachableState (Heze.Anchors.onlyFulu ancestor) true farFutureEpoch chainB :=
  .slots 536
    (.upgrade reachable_gloasB (by native_decide) (by native_decide)
      (upgradeToHeze_eq_ok (by native_decide)))
    (by native_decide) (runPure_eq_of_succeeds (by native_decide))

/-! ## What each chain did with the BLS deposit -/

/-- The path of the two new keys through each chain.

* Chain A reaches the Heze boundary with its sixteen validators and with `blsDeposit` and
  `validatorDeposit` in the queue. One epoch later the queue is empty, and key 102 alone has
  joined, at index 16.
* Chain B enters Gloas with key 101 at index 16 and key 102 at index 17, and neither upgrade
  changes that. -/
theorem scenario_anatomy :
    gloasA.validators.val.size = 16 ∧
    gloasA.pendingDeposits.val.map (·.pubkey) = #[pubkey 101, pubkey 102] ∧
    chainA.pendingDeposits.val.size = 0 ∧
    (chainA.validators.val.map (·.pubkey)).extract 16 = #[pubkey 102] ∧
    (fuluB.validators.val.map (·.pubkey)).extract 16 = #[pubkey 101, pubkey 102] ∧
    (chainB.validators.val.map (·.pubkey)).extract 16 = #[pubkey 101, pubkey 102] := by
  native_decide

/-! ## The theorem -/

/-- Two chains with one finalized checkpoint can assign one validator index to two public
keys, when the Heze upgrade lies between their common ancestor and their heads.

The statement, at the `minimal` preset with Gloas at epoch 65 and Heze at epoch 66:

* `u` is a Fulu state, and it is the only anchor, so both `ReachableState` facts read
  "reachable from `u`". The flag is `true`: every block signature and state root is checked.
* `w'` and `w''` are Heze states at one slot.
* Their finalized checkpoints are equal, and equal to the checkpoint of `u`. Neither chain
  finalized a block after `u`.
* At index `i`, which both registries hold, the public keys differ.

The witnesses are `chainA` and `chainB`, and the index is 16. `scenario_anatomy` records why:
Heze's `applyPendingDeposit` dropped a deposit with BLS credentials on one chain, and Fulu's
`processPendingDeposits` had made a validator from it on the other.

The proof evaluates the compiled state transition by `native_decide`, on the FFI SHA-256 and
the blst backend, so it trusts the compiler and the two native libraries. The two SHA-256
equivalence axioms appear in its axiom list through the `Hasher` instance of the FFI
`Sha256`; no step rewrites with them. -/
theorem validatorIndex_diverges_across_upgrade :
    ∃ (u : Fulu.BeaconState) (w' w'' : Heze.BeaconState),
      Heze.ReachableState (Heze.Anchors.onlyFulu u) true farFutureEpoch w' ∧
      Heze.ReachableState (Heze.Anchors.onlyFulu u) true farFutureEpoch w'' ∧
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

/-- The common ancestor satisfies `SimpleStateInvariants`, the hypothesis the in-fork theorem
puts on its anchors. -/
theorem ancestor_invariants : Fulu.SimpleStateInvariants ancestor :=
  ⟨by native_decide,
    ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩,
    ⟨by native_decide, by native_decide, by native_decide⟩,
    ⟨by native_decide, by native_decide⟩⟩

/-- The index assignment is not stable across the upgrades into Heze: `IndexAssignmentFromFulu` is false.

`IndexAssignmentFromFulu` is the statement of the in-fork theorem
`indexAssignment_of_compatibleFinality` with a Fulu state as the common state. The witness is
the ancestor, which is reachable as an anchor and satisfies `SimpleStateInvariants`, with
`chainA` and `chainB` at index 16. Both chains have finalized no slot at or after the slot of
the ancestor: their finalized epoch is 62, which starts at slot 496, and the ancestor is at
slot 519. The proof trusts the compiler and the two native libraries, as
`validatorIndex_diverges_across_upgrade` does. -/
theorem indexAssignmentFromFulu_false : ¬ Heze.IndexAssignmentFromFulu :=
  Heze.not_indexAssignmentFromFulu (anchors := Fulu.Anchors.only ancestor)
    (fun _ h => h ▸ ancestor_invariants) (.anchor rfl (by native_decide))
    reachable_chainA reachable_chainB
    (Or.inl (by unfold Heze.FinalizedBelow; native_decide))
    (i := 16) (by native_decide) (by native_decide) (by native_decide)

end EthCLSpecs.Tests.HezeValidatorIndexPins
