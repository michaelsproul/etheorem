"""Two Gloas chains from one Fulu state, and the public key each holds at validator index 64.

A run against the upstream pyspec (ethereum/consensus-specs), at the minimal preset. It needs
a consensus-specs checkout with the pyspec built (`make build` there), and it runs from any
directory:

    PYTHONPATH=<checkout> uv run --project <checkout> \
        python scripts/repro_validator_index_split.py --expect agree

BLS is on, so every block, attestation and deposit signature is checked.

`--expect` names the outcome the run asserts.

* `--expect split`: the two chains hold two public keys at index 64. This is the outcome at
  v1.7.0-beta.4 and at upstream commit e3e2d01 (2026-11-12).
* `--expect agree`: the two chains hold one public key at every index both have. This is the
  outcome with the onboarding cutoff of the branch `dapplion:gloas-onboard-cutoff`: at that
  branch, and at v1.7.0-beta.4 with `onboard_builders_from_pending_deposits` replaced by the
  function of that branch.

With `--dump FILE` it also writes the genesis state and every signed block of both chains, as
SSZ in hex, one `name hex` line each. `EthCLSpecs/Tests/data/index_split.txt` is that file at
the branch `dapplion:gloas-onboard-cutoff`, commit `e4bd955`, and
`EthCLSpecs/Tests/GloasPyspecReplayPins.lean` replays it on the Lean model.

The two chains share every block up to slot 40. Gloas activates at epoch 6, so the onboarding
cutoff is slot 32, the first slot of epoch 4. Two shared blocks carry deposit requests.

* The block at slot 31, at or below the cutoff: key 64 with builder credentials (0xB0), and
  key 65 with 0x01 credentials.
* The block at slot 39, above the cutoff, four requests with builder credentials: key 66
  signed, key 67 unsigned, key 0 unsigned (key 0 is validator 0), and key 66 again.

The chains differ in when they finalize epoch 4.

* Chain A keeps attesting through epoch 5. It finalizes epoch 4 at the last Fulu epoch
  transition, so Fulu's process_pending_deposits makes validators 64 and 65 from the two
  deposits of slot 31 before the fork.
* Chain B has no block in slots 41..47. Its finalized epoch is still 3 at the fork, so all six
  deposits are pending there. After one Gloas epoch with attestations chain B finalizes
  epoch 4 as well.

Without the cutoff, onboard_builders_from_pending_deposits makes a builder from the deposit
for key 64 on chain B, and the deposit for key 65 becomes validator 64 there. validators[64]
is then key 64 on chain A and key 65 on chain B, with one finalized checkpoint.

With the cutoff, the deposit for key 64 stays queued on chain B, because its slot is at or
below the cutoff. Chain B then makes validators 64 and 65 from the two deposits, as chain A
did. The four deposits of slot 39 take the four ways through the onboarding on both chains:
key 66 becomes a builder, the unsigned deposit for key 67 is dropped, the unsigned deposit for
validator 0 stays queued as a top-up, and the second deposit for key 66 tops up the builder.

packages/EthCLSpecs/docs/SPECS_ARCHITECTURE.md section 11.6 records the finding, and
EthCLSpecs/Proofs/Gloas/IndexAssignmentFromFulu.lean proves the agreement for every pair of
chains.
"""

import sys

from eth_consensus_specs.fulu import minimal as fulu
from eth_consensus_specs.gloas import minimal as gloas
from eth_consensus_specs.test.context import (
    default_activation_threshold,
    get_copy_of_spec,
    spec_with_config_overrides,
)
from eth_consensus_specs.test.helpers.attestations import next_slots_with_attestations
from eth_consensus_specs.test.helpers.block import build_empty_block_for_next_slot
from eth_consensus_specs.test.helpers.deposits import prepare_deposit_request
from eth_consensus_specs.test.helpers.fork_transition import do_fork
from eth_consensus_specs.test.helpers.genesis import create_genesis_state
from eth_consensus_specs.test.helpers.keys import pubkeys
from eth_consensus_specs.test.helpers.state import state_transition_and_sign_block

from eth_consensus_specs.utils import bls
from eth_consensus_specs.utils.ssz.ssz_impl import serialize

bls.bls_active = True  # real signatures: deposits, blocks and attestations are all checked
assert bls.bls_active

FORK_EPOCH = 6
overrides = {"GLOAS_FORK_EPOCH": FORK_EPOCH}
pre, _ = spec_with_config_overrides(get_copy_of_spec(fulu), overrides)
post, _ = spec_with_config_overrides(get_copy_of_spec(gloas), overrides)
SPE = pre.SLOTS_PER_EPOCH
LAST_FULU_SLOT = FORK_EPOCH * SPE - 1          # 47
DEPOSIT_SLOT = 4 * SPE - 1                     # 31, the last slot of epoch 3
LATE_DEPOSIT_SLOT = 5 * SPE - 1                # 39, the last slot of epoch 4, above the cutoff
SPLIT_SLOT = 5 * SPE                           # 40, the last block both chains share
BUILDER_KEY, VALIDATOR_KEY = 64, 65            # two keys outside the 64-validator registry
LATE_BUILDER_KEY, UNSIGNED_KEY = 66, 67        # two more, for the deposits above the cutoff
TOP_UP_KEY = 0                                 # the key of validator 0
EXPECT = sys.argv[sys.argv.index("--expect") + 1] if "--expect" in sys.argv else "agree"
assert EXPECT in ("split", "agree")

builder_credentials = post.BUILDER_WITHDRAWAL_PREFIX + b"\x00" * 11 + b"\x42" * 20
validator_credentials = pre.ETH1_ADDRESS_WITHDRAWAL_PREFIX + b"\x00" * 11 + b"\x43" * 20


def checkpoint(state):
    c = state.finalized_checkpoint
    return (int(c.epoch), bytes(c.root).hex()[:16])


def describe(name, state):
    print(
        f"{name}: slot {int(state.slot)}, validators {len(state.validators)}, "
        f"finalized {checkpoint(state)}, pending deposits {len(state.pending_deposits)}"
        + (f", builders {len(state.builders)}" if hasattr(state, "builders") else "")
    )


# ---- The shared prefix: full participation, and one block with the two deposits. ----
state = create_genesis_state(pre, [pre.MAX_EFFECTIVE_BALANCE] * 64, default_activation_threshold(pre))
dump = [("genesis", serialize(state))]
for slot in range(1, SPLIT_SLOT + 1):
    if slot == DEPOSIT_SLOT:
        block = build_empty_block_for_next_slot(pre, state)
        amount = pre.Gwei(32 * 10**9)
        block.body.execution_requests.deposits.append(
            prepare_deposit_request(pre, BUILDER_KEY, amount, index=0,
                                    withdrawal_credentials=builder_credentials, signed=True))
        block.body.execution_requests.deposits.append(
            prepare_deposit_request(pre, VALIDATOR_KEY, amount, index=1,
                                    withdrawal_credentials=validator_credentials, signed=True))
        dump.append(("shared", serialize(state_transition_and_sign_block(pre, state, block))))
    elif slot == LATE_DEPOSIT_SLOT:
        block = build_empty_block_for_next_slot(pre, state)
        amount = pre.Gwei(32 * 10**9)
        late = [(LATE_BUILDER_KEY, True), (UNSIGNED_KEY, False), (TOP_UP_KEY, False),
                (LATE_BUILDER_KEY, True)]
        for i, (key, signed) in enumerate(late):
            block.body.execution_requests.deposits.append(
                prepare_deposit_request(pre, key, amount, index=2 + i,
                                        withdrawal_credentials=builder_credentials, signed=signed))
        dump.append(("shared", serialize(state_transition_and_sign_block(pre, state, block))))
    else:
        _, blocks, state = next_slots_with_attestations(pre, state, 1, True, False)
        dump += [("shared", serialize(b)) for b in blocks]
shared = state.copy()
shared_block_root_32 = bytes(pre.get_block_root_at_slot(shared, 4 * SPE)).hex()[:16]
describe("shared state", shared)
print(f"block root at slot 32 (start of epoch 4): {shared_block_root_32}")

# ---- Chain A: blocks with attestations through the rest of epoch 5, then the upgrade. ----
a = shared.copy()
_, blocks, a = next_slots_with_attestations(pre, a, LAST_FULU_SLOT - SPLIT_SLOT, True, False)
dump += [("chainA", serialize(b)) for b in blocks]
a, _ = do_fork(a, pre, post, FORK_EPOCH, with_block=False)
describe("chain A after the upgrade", a)

# ---- Chain B: no block in slots 41..47, the upgrade, then Gloas blocks with attestations. ----
b = shared.copy()
pre.process_slots(b, LAST_FULU_SLOT)
describe("chain B at the last Fulu slot", b)
b, _ = do_fork(b, pre, post, FORK_EPOCH, with_block=False)
describe("chain B after the upgrade", b)
epochs = 0
while len(b.validators) == 64 and epochs < 8:
    _, blocks, b = next_slots_with_attestations(post, b, SPE, True, True)
    dump += [("chainB", serialize(x)) for x in blocks]
    epochs += 1
    describe(f"chain B after {epochs} Gloas epoch(s)", b)

print(f"BLS active: {bls.bls_active}")

# ---- The comparison. ----
def keys(state):
    return [pubkeys.index(bytes(v.pubkey)) for v in state.validators]


def builders(state):
    return [(pubkeys.index(bytes(x.pubkey)), int(x.balance)) for x in state.builders]


shared_indices = min(len(a.validators), len(b.validators))
split = [i for i in range(shared_indices) if keys(a)[i] != keys(b)[i]]
print()
print(f"chain A finalized {checkpoint(a)}; chain B finalized {checkpoint(b)}")
print(f"chain B holds chain A's finalized block as an ancestor: "
      f"{bytes(post.get_block_root_at_slot(b, 4 * SPE)).hex()[:16] == checkpoint(a)[1]}"
      if int(b.slot) - 4 * SPE <= post.SLOTS_PER_HISTORICAL_ROOT else "")
for name, chain in (("A", a), ("B", b)):
    print(f"chain {name}: validators[64:] hold keys {keys(chain)[64:]}, "
          f"credentials prefixes {[bytes(v.withdrawal_credentials)[:1].hex() for v in chain.validators[64:]]}, "
          f"builders (key, balance) {builders(chain)}, "
          f"pending deposits for keys {[pubkeys.index(bytes(d.pubkey)) for d in chain.pending_deposits]}")
print(f"indices where the chains disagree: {split}")
if EXPECT == "split":
    assert split == [64], "expected two public keys at index 64"
else:
    assert split == [], "expected one public key at every shared index"
    assert keys(a)[64:] == [BUILDER_KEY, VALIDATOR_KEY] == keys(b)[64:]
    # The deposits above the cutoff: one builder with both deposits for its key, on each chain.
    assert builders(a) == [(LATE_BUILDER_KEY, 64 * 10**9)] == builders(b)
print(f"outcome: {EXPECT}")

if "--dump" in sys.argv:
    path = sys.argv[sys.argv.index("--dump") + 1]
    with open(path, "w") as f:
        for name, data in dump:
            f.write(f"{name} {data.hex()}\n")
    print(f"wrote {len(dump)} objects to {path}")
