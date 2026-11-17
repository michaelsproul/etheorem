# EthCLSpecs: spec-vs-vector discrepancies

The directional discrepancy policy (`SPEC_AUTHORING_MODEL.md` §10,
`SPECS_ARCHITECTURE.md` §12.1): the upstream `consensus-spec-tests` vectors are
the operational reference, so a Lean-versus-vector divergence almost always means
the Lean is wrong and the fix goes in Lean. The spec markdown is the ultimate
authority, and "spec wins" bites only in the rare case a vector contradicts the
spec text (an upstream pyspec bug): then Lean follows the text, the vector fails,
and the divergence is **recorded here** rather than papered over by bending Lean
to a wrong vector.

Each entry carries the vector id, the spec-text citation, and the upstream issue
link, so the audit trail is one grep away. Resolved Lean-versus-vector divergences
stay logged here for the audit trail even when the fix landed in Lean.

Deliberate implementation divergences that no vector observes live in
`IMPLEMENTATION_NOTES.md`, catalogued per fork; the FOCIL set is under "Heze diff".

Pin: `v1.7.0-beta.4` (all forks).

Spec-markdown line citations (`<file>.md:NN`) resolve under `specs/` in
`ethereum/consensus-specs` at the pinned version; every re-pin re-checks them
alongside the divergences they anchor.

## Fulu

_No open vector discrepancies._ Every collected in-scope minimal and mainnet vector passes
by root or rejects faithfully (`epoch_processing`, `operations` incl. standalone
`execution_payload`, `sanity/blocks`, `sanity/slots`, `finality`, `random`,
`rewards`, `fork_choice` incl. the PeerDAS data-availability `on_block` cases and
`get_proposer_head`), with zero `xfail`. The only Fulu vectors not run are the
deselected out-of-scope ones (`IMPLEMENTATION_NOTES.md`, "Scope and conformance"): the Fulu `fork` /
`transition` formats (the Electra→Fulu upgrade / boundary, needing an Electra parent
fork) and the `light_client` / `networking` / `merkle_proof` / `sync` runners.

| Vector id | Spec citation | Upstream issue | Resolution |
|---|---|---|---|
| `epoch_processing/registry_updates/pyspec_tests/invalid_large_withdrawable_epoch` | `electra/beacon-chain.md`, `initiate_validator_exit` | none (Lean-side gap) | Fixed in Lean |

The one resolved entry was a Lean-side gap: Lean's `UInt64`
wrapped where the pyspec raises a `ValueError` serializing the overflowed
`withdrawable_epoch`. Closed by asserting the `exit_epoch +
MIN_VALIDATOR_WITHDRAWABILITY_DELAY` bound in `initiateValidatorExit`, so the case
now rejects faithfully.

The v1.7.0-beta.4 re-pin found four Lean-side gaps against the spec text that no vector
observed. Three are in the deposit path: the tree had kept its Electra forms after Fulu
removed the old deposit mechanism (consensus-specs #4704, in the text since alpha.12). The
fourth is a missing blob-count assert in `process_execution_payload`. All four are fixed in
Lean. The Fulu
vectors passed before and after, so the rows cite the spec text alone.

| Spec citation | Lean-side gap | Resolution |
|---|---|---|
| `fulu/beacon-chain.md:178`, `process_operations` | ran the Electra deposit-count gate and the `process_deposit` loop; the text asserts `len(body.deposits) == 0` | Fixed in Lean |
| `fulu/beacon-chain.md:206`, `process_deposit_request` | wrote `deposit_requests_start_index` on the first request; the text no longer does | Fixed in Lean |
| `fulu/beacon-chain.md:415`, `process_pending_deposits` | stopped at the eth1 bridge; the text has no such stop | Fixed in Lean |
| `fulu/beacon-chain.md:115`, `process_execution_payload` | no bound on the blob count; the text asserts `len(body.blob_kzg_commitments) <= get_blob_parameters(get_current_epoch(state)).max_blobs_per_block` | Fixed in Lean (`BLOB_SCHEDULE`, `get_blob_parameters`) |

### Silent wraps and one missing assert

The reachable-state audit and the `processEpoch` success proofs (`SPECS_ARCHITECTURE.md`
§11.4, §11.5) read every arithmetic and assert site in epoch processing and in the two
execution-request handlers. They found more Lean-side gaps of the class the resolved
`initiate_validator_exit` entry closed. At each site below the pyspec raises, and the model
continues with a wrapped or default value. No vector reaches any of them, because each needs a
value near `2^64` or a sync-committee pubkey that fails `KeyValidate`. They stay open. A fix
changes the error behaviour of a body that the conformance runs pass on, so each fix is its own
change.

| Spec citation | Lean-side gap | Resolution |
|---|---|---|
| `altair/beacon-chain.md:481`, `get_flag_index_deltas` | `base_reward * weight * unslashed_participating_increments` is a `uint64` product and raises past `2^64`. `getFlagIndexDeltas` computes it in `Nat`. `get_base_reward` (`:391`) is the same case, and `getBaseReward` returns a `Nat` | Open |
| `phase0/beacon-chain.md:1565-1570`, `get_total_balance` | the `Gwei(...)` cast of the sum raises past `2^64`; the `UInt64` fold wraps | Deferred, `IMPLEMENTATION_NOTES.md` (the fork-choice weight path) |
| `electra/beacon-chain.md:935-936`, `compute_exit_epoch_and_update_churn` | the two `+=` raise past `2^64`; `reserveChurn` adds in `UInt64` and wraps. The consolidation twin (`:965-966`) calls the same `reserveChurn` | Open |
| `phase0/beacon-chain.md:1350`, `compute_start_slot_at_epoch` | `Slot(epoch) * SLOTS_PER_EPOCH` raises past `2^64`; `computeStartSlotAtEpoch` wraps | Open |
| `phase0/beacon-chain.md:1360`, `compute_activation_exit_epoch` | `epoch + 1 + MAX_SEED_LOOKAHEAD` raises past `2^64`; `computeActivationExitEpoch` wraps | Open |
| `electra/beacon-chain.md:1926` and `:2068`, `process_withdrawal_request` and `process_consolidation_request` | `exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY` raises past `2^64`. Both bodies add in `UInt64` and wrap, where `initiateValidatorExit` asserts the bound | Open |
| `altair/bls.md:45-47`, `eth_aggregate_pubkeys` | the text asserts a nonempty list of keys that pass `KeyValidate`. The FFI returns an empty buffer on a bad key, and `blsAggregatePubkeys` reads it as 48 zero bytes | Open |

The success theorems speak of the model. Their premises keep the exit churn and the activation
epoch in range, so the pyspec does not raise at those sites either. They bound neither the
reward numerator, the balance fold, the start slot of the proposer lookahead, nor the pubkeys. At
those four sites a theorem's success holds for the model alone.

The same audit checked one more candidate and found no gap. `compute_balance_weighted_selection`
(`gloas/beacon-chain.md:1216-1229`) runs `i += 1` on a `Uint64` after the append, so the last pass
at `i = 2**64 - 1` raises whether or not it filled the selection. `cbwsAux` throws at the same
point through `checkedSucc`.

### Config rules the spec needs and upstream does not test

Upstream states its config rules as tests, one `test_config_invariants.py` per fork. Some configs
pass those tests and still make the pyspec fail on every chain that reaches the site. The proofs
assume stronger rules (`PresetValid` and `ConfigValid`, `Proofs/Fulu/ConfigValid.lean`), and that
module's docstring gives the reason for each. Four are candidate upstream rules. No upstream issue
is filed yet.

| Config | Upstream test | Pyspec failure |
|---|---|---|
| `SLOTS_PER_HISTORICAL_ROOT = SLOTS_PER_EPOCH`, with `SLOTS_PER_EPOCH ≥ 2` | passes `test_time` (`SPE <= SPHR`, `SPHR % SPE == 0`) | at the last slot of an epoch, `get_block_root(previous_epoch)` asserts `state.slot <= slot + SLOTS_PER_HISTORICAL_ROOT` (`phase0/beacon-chain.md:1452`) whenever the previous-epoch target justifies |
| `SLOTS_PER_EPOCH = 1` | passes `test_time` | the epoch's start slot is the state's slot, and `get_block_root(current_epoch)` asserts `slot < state.slot` whenever the current-epoch target justifies |
| a zero `EPOCHS_PER_SYNC_COMMITTEE_PERIOD` or `EPOCHS_PER_ETH1_VOTING_PERIOD` | no test bounds either | epoch processing takes `next_epoch` modulo each, and Python raises `ZeroDivisionError` |
| `MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA < EFFECTIVE_BALANCE_INCREMENT`, or a zero `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` | no test bounds either | on a small registry the exit churn rounds down to zero, and `compute_exit_epoch_and_update_churn` divides by it (`electra/beacon-chain.md:934`) |

## Gloas

_One recorded deviation from the pinned release, below._ Gloas is fully ported (the EIP-7732
ePBS spine, that is the state-transition pipeline, plus operations, fork choice, and the
Fulu→Gloas transition). Apart from the `fork` and `transition` vectors of the deviation, every
in-scope minimal and mainnet vector passes by root or rejects faithfully, with no `xfail`.
Gloas inherits the Fulu `registry_updates` substep (the
DSL re-elaborates the captured `forkdef` in the Gloas namespace), so the overflow fix
above propagated to Gloas with no Gloas-side change. Deliberate divergences are
catalogued in `IMPLEMENTATION_NOTES.md`, "Gloas diff" and "Fork choice".

### The Fulu to Gloas upgrade: a deviation from the pinned release

The upgrade here is the upgrade of the consensus-specs branch
`dapplion:gloas-onboard-cutoff`, at commit `e4bd955`. The branch proposes a change to the
spec, and this tree carries it to prove what it gives. This case differs from the rows above:
here the Lean bodies follow a proposed text, and the pinned vectors follow the released one.

Between v1.7.0-beta.4 and the branch, the state transition of Fulu and Gloas changes in one
file, `specs/gloas/fork.md`, in three places. The other files the branch changes hold fork
choice, networking and validator guidance, and the Heze config.

* **The onboarding rule of consensus-specs #5736**, which upstream merged after v1.7.0-beta.4
  (`onboardBuildersFromPendingDeposits`, `Gloas/Operations.lean`). A deposit without builder
  credentials stays queued, even when a builder holds its key. A builder-credential deposit
  with a valid signature makes a builder, even when a validator holds its key or a queued
  deposit names it.
* **The onboarding cutoff**, the change the branch proposes, in the same function. A deposit
  with a slot at or below the first slot of epoch `GLOAS_FORK_EPOCH - 2` stays queued. A chain
  may have applied such a deposit before the fork, as a validator deposit.
* **The payload-availability bit of the fork slot**, consensus-specs #5808, also merged after
  v1.7.0-beta.4 (`upgradeToGloas`, `Gloas/Upgrade.lean`). `upgrade_to_gloas` unsets the bit,
  which `process_slot` would have done at the previous slot under the Gloas rules.

With the cutoff, two chains with compatible finality hold one public key at every validator
index both have, across the upgrade: `indexAssignmentFromFulu`
(`Proofs/Gloas/IndexAssignmentFromFulu.lean`). Without it they can hold two
(`SPECS_ARCHITECTURE.md` §11.6).

**The pinned vectors.** Every post-state of an upgrade has another root than the pinned
release gives, by the unset bit. So each pinned Gloas `fork` vector departs (37 at `minimal`,
35 at `mainnet`), and each pinned Gloas `transition` vector with a post-state (33 and 27).
`transition_rejects_pre_gloas_payload_attestation` compares no post-state and passes. Nine of
the `fork` vectors per preset depart by the onboarding rule too: they hold a builder deposit
at `GENESIS_SLOT`, at or below the cutoff, and the branch moves the deposits of those tests to
`GENESIS_SLOT + 1`. The harness states the rule in `departs_from_pinned_release`
(`PySpecTests/test_pyspec.py`) and reports these vectors as `xfail`. The other pinned vectors
of Gloas, Fulu and Heze pass.

| Vectors (`minimal` and `mainnet`) | Spec citation | Resolution |
|---|---|---|
| `gloas/fork/fork/pyspec_tests/*` | `gloas/fork.md:70`, `onboard_builders_from_pending_deposits`, and `gloas/fork.md:135`, `upgrade_to_gloas` | Deviation kept: Lean follows the branch |
| `gloas/transition/core/pyspec_tests/*`, but `transition_rejects_pre_gloas_payload_attestation` | `gloas/fork.md:135`, `upgrade_to_gloas` | Deviation kept: Lean follows the branch |

**The checks that replace them.** Three checks hold the Lean upgrade to the branch itself.

* The branch generates its own vectors (`make test reftests=true`). At `minimal`, the Lean
  model passes the 233 `fork`, `transition` and neighbouring cases it models, run through the
  harness with `--tag` on the generated tree. They include the branch's test of the two sides
  of the cutoff.
* One generated case is no `fork` vector: `fork_validator_indices_match_across_branches`
  yields a `post` taken after `process_pending_deposits`. `Tests/GloasCrossBranchVectorPins.lean`
  replays what the test does and ends on the root of `post`.
* `scripts/repro_validator_index_split.py` builds two chains on the pyspec of the branch, and
  `Tests/GloasPyspecReplayPins.lean` replays their 55 blocks with each signature and state
  root checked. Eight of them are Gloas blocks after the upgrade, and the queue of that
  scenario takes each branch of the onboarding function.

The Gloas `process_pending_deposits` (`gloas/beacon-chain.md:1659`) is a Gloas override, and
it carried the same stale eth1-bridge stop as the Fulu body above. The beta.4 re-pin removed
it with the Fulu fix; no vector observed it.

Gloas inherits every body in the Fulu table of silent wraps (`Gloas/EpochProcessing.lean`
`inherit`s each one), so each of those gaps is open in Gloas too. The config rules carry over
through `Proofs/Gloas/ConfigValid.lean`, which extends the Fulu classes.

## Heze

_No open discrepancies._ The Gloas→Heze `fork` vectors are in scope, and at v1.7.0-beta.4
every in-scope minimal and mainnet vector passes by root or rejects faithfully, with no
`xfail`. FOCIL's deliberate divergences from the spec text stay in `IMPLEMENTATION_NOTES.md`,
"Heze diff".

| Vector id | Spec citation | Upstream issue | Resolution |
|---|---|---|---|
| `minimal/heze/fork/fork/pyspec_tests/fork_base_state` | `heze/fork.md:41`, `upgrade_to_heze` | none | Resolved upstream at v1.7.0-beta.4 |
| `mainnet/heze/fork/fork/pyspec_tests/fork_base_state` | `heze/fork.md:41`, `upgrade_to_heze` | none | Resolved upstream at v1.7.0-beta.4 |

At alpha.12 both rows were open. Their pre-state was not a Gloas state, and their post-state
was not the output of `upgrade_to_heze`, so Lean followed the spec text and the harness
reported the two cases as `xfail`. The beta.4 vectors are a Gloas pre-state and its
`upgrade_to_heze` output, Lean matches them, and the harness's `SPEC_TEXT_DIVERGENCES` set
is empty. The alpha.12 evidence, kept for the audit trail:

The pre-state's fork current version was already Heze (`0x08000001` minimal,
`0x08000000` mainnet). On minimal the bid's first variable offset was 226, where a
Gloas bid's prefix is 224, so the bid was the 13-field Heze container. On both presets
the pre-state was two bytes larger than the sibling Gloas pre-states. The post-state's
`fork.current_version` was the bytes `e8 14 80 00`, which is not `HEZE_FORK_VERSION`.
A correct upgrade of a Gloas state grows by those two inclusion-list bytes; those
posts grew by 516 bytes (minimal) and 2052 bytes (mainnet).
