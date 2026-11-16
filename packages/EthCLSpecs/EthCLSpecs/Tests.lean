import EthCLSpecs.Tests.BoxBinderPins
import EthCLSpecs.Tests.ChainReplay
import EthCLSpecs.Tests.DepositScenario
import EthCLSpecs.Tests.FuluForkChoicePins
import EthCLSpecs.Tests.GloasCommitteesPins
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
runs two chains from the Fulu state `DepositScenario` builds, across a fork upgrade, and
proves that the chains assign one validator index to two public keys
(`SPECS_ARCHITECTURE.md` §11.6). `GloasPyspecReplayPins` proves the same from a genesis
state, on signed blocks the upstream pyspec built, which `ChainReplay` replays with every
signature and state root checked. It also applies the finalized-validator theorem to that
pair of chains: they agree up to index 63, and the index where they differ is finalized in
neither.
-/
