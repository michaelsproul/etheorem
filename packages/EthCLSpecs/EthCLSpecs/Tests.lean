import EthCLSpecs.Tests.BoxBinderPins
import EthCLSpecs.Tests.ChainData
import EthCLSpecs.Tests.ChainReplay
import EthCLSpecs.Tests.DepositScenario
import EthCLSpecs.Tests.FuluForkChoicePins
import EthCLSpecs.Tests.GloasCommitteesPins
import EthCLSpecs.Tests.GloasCrossBranchVectorPins
import EthCLSpecs.Tests.GloasForkChoicePins
import EthCLSpecs.Tests.GloasPyspecReplayPins
import EthCLSpecs.Tests.GloasValidatorIndexPins
import EthCLSpecs.Tests.HezeCommitteesPins
import EthCLSpecs.Tests.HezeForkChoicePins
import EthCLSpecs.Tests.HezeValidatorIndexPins
import EthCLSpecs.Tests.WalkingSkeleton

/-!
# `EthCLSpecs.Tests`: Lean-internal spec self-tests

`#guard` / `native_decide` checks over hand-built inputs, confirming spec
behavior independently of the `pytest-xdist` pyspec harness. The sources
live under `EthCLSpecs/Tests/` (namespace `EthCLSpecs.Tests.*`), built as their
own `lean_lib` and excluded from the shipped library (`SPECS_ARCHITECTURE.md`
§3.6).

The `*Pins` modules are the vectorless build gates: reject branches and helper
values no conformance vector reaches, one module per fork body they pin. They
were written beside the declarations they pin and moved here, since a
`native_decide` compiled into a fork body is evaluation every consumer of that
body carries, for a check only the build gate reads.

The two `*ValidatorIndexPins` modules are evaluated theorems about `ReachableState`. Each
runs two chains from the Fulu state `DepositScenario` builds, across a fork upgrade
(`SPECS_ARCHITECTURE.md` §11.6).

* `GloasValidatorIndexPins` applies `indexAssignment_fromFulu` to its pair: the two chains
  hold one public key at every validator index. The onboarding cutoff of the Gloas upgrade
  gives that, and the module pins the two sides of the cutoff.
* `HezeValidatorIndexPins` proves that its pair assigns one validator index to two public
  keys, across the Heze upgrade.

`GloasPyspecReplayPins` applies `indexAssignment_fromFulu` from a genesis state, on signed
blocks the upstream pyspec built, which `ChainReplay` replays with every signature and state
root checked. The blocks come from the pyspec with the onboarding function `Gloas/Operations.lean`
ports, so the replay checks that port. The module also applies the finalized-validator theorem
to the pair: it covers the indices up to 63, and validator 64 is finalized in neither chain.
`ChainData` decodes the data files the replay pins read.

`GloasCrossBranchVectorPins` replays the test the branch `dapplion:gloas-onboard-cutoff` adds
for the cutoff, `test_fork_validator_indices_match_across_branches`, on the vector that test
generates: the upgrade, then one `processPendingDeposits`, ends on the root of its `post`.
-/
