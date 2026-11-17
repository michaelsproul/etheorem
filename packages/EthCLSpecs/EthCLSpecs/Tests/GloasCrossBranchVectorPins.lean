import EthCLSpecs.Proofs.Gloas.Run
import EthCLSpecs.Gloas.Upgrade
import EthCLSpecs.Tests.ChainData
import EthCLSpecs.Tests.DepositScenario

/-!
# `EthCLSpecs.Tests.GloasCrossBranchVectorPins`: the branch's cross-branch test, on the Lean model

The consensus-specs branch `dapplion:gloas-onboard-cutoff` adds the test
`test_fork_validator_indices_match_across_branches`. Its pre-state is a Fulu state whose queue
holds a builder deposit from `GENESIS_SLOT`, which is at or below the onboarding cutoff, and a
validator deposit. The test upgrades the state, applies the pending deposits, and checks that
the builder deposit became validator 64 and the validator deposit validator 65: the registry
a branch reaches when it applies the builder deposit before the fork.

The test yields `pre` and the state after the deposits were applied, as `post`. So the vector
it generates is no `fork` vector: `post` is the upgrade of `pre` followed by one
`process_pending_deposits`. The harness under `PySpecTests/` compares `post` with the upgrade
alone and reports a mismatch. This module replays what the test does.

`data/cross_branch_fork.txt` holds `pre` and `post`, as SSZ in hex. They are the vector the
branch generates at the `minimal` preset (commit `e4bd955`), with the snappy framing
removed.

`cross_branch_vector` states the result. The upgrade accepts `pre`, makes no builder and
leaves both deposits in the queue. One `processPendingDeposits` then accepts the upgraded
state, and the state it leaves has the root of `post`, with 66 validators.

One `native_decide` evaluates the two steps, on `CryptoBackend.ffi` and the FFI SHA-256, so
the theorem trusts the compiler and the two native libraries.
Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.GloasCrossBranchVectorPins

open EthCLLib.Spec
open SizzLean
open EthCLSpecs EthCLSpecs.Proofs
open EthCLSpecs.Proofs.Gloas (GloasRun)
open EthCLSpecs.Tests.ChainData
open EthCLSpecs.Tests.DepositScenario (postOf succeeds)
open scoped EthCLSpecs.Gloas.Downgrade

/-- The Gloas `minimal` preset. -/
@[reducible] def preset : Gloas.Preset := Gloas.minimal

/-- The shipped `minimal` config. The upgrade reads its `GLOAS_FORK_VERSION`. -/
@[reducible] def config : Gloas.Config := Gloas.minimalConfig

-- The four instances every declaration below resolves, kept inside this module.

attribute [local instance] preset config fastHasherTag CryptoBackend.ffi

/-- The objects of the data file: `pre` and `post`. -/
def dump : List (String × ByteArray) := parseDump (include_str "data/cross_branch_fork.txt")

/-- The Fulu pre-state of the vector. A decode failure gives the default state, which the
root comparison of `cross_branch_vector` then rejects. -/
def pre : Fulu.BeaconState :=
  match objects dump "pre" with
  | [bytes] => (SSZ.deserialize (T := Fulu.BeaconState) bytes).toOption.getD default
  | _ => default

/-- The Gloas post-state of the vector. -/
def post : Gloas.BeaconState :=
  match objects dump "post" with
  | [bytes] => (SSZ.deserialize (T := Gloas.BeaconState) bytes).toOption.getD default
  | _ => default

/-- The upgrade of `pre`: `upgradeToGloas`, then `completeUpgradeToGloas`. -/
def upgraded : Gloas.BeaconState :=
  postOf (Gloas.completeUpgradeToGloas (StateTransition := GloasRun))
    (Gloas.upgradeToGloas Gloas.Const.gloasForkVersion pre)

/-- The upgraded state after one `processPendingDeposits`, the step the test repeats until
the queue is empty. -/
def drained : Gloas.BeaconState :=
  postOf (Gloas.processPendingDeposits (StateTransition := GloasRun)) upgraded

/-- The Lean model reproduces the branch's cross-branch test.

* The upgrade accepts `pre`. It makes no builder, and both deposits stay in the queue: the
  builder deposit sits at the cutoff slot.
* The upgraded state has another root than `post`, so the vector is no `fork` vector.
* `processPendingDeposits` accepts the upgraded state and empties the queue. The state it
  leaves has the root of `post`, and 66 validators: the two deposits became validators 64
  and 65. -/
theorem cross_branch_vector :
    pre.validators.val.size = 64 ∧
    succeeds (Gloas.completeUpgradeToGloas (StateTransition := GloasRun))
      (Gloas.upgradeToGloas Gloas.Const.gloasForkVersion pre) = true ∧
    upgraded.builders.val.size = 0 ∧ upgraded.pendingDeposits.val.size = 2 ∧
    htr upgraded ≠ htr post ∧
    succeeds (Gloas.processPendingDeposits (StateTransition := GloasRun)) upgraded = true ∧
    drained.pendingDeposits.val.size = 0 ∧ drained.validators.val.size = 66 ∧
    htr drained = htr post := by
  native_decide

end EthCLSpecs.Tests.GloasCrossBranchVectorPins
