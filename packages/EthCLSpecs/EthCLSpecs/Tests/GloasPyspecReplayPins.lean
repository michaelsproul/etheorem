import EthCLSpecs.Proofs.Gloas.FinalizedValidators
import EthCLSpecs.Proofs.Gloas.IndexAssignmentFromFulu
import EthCLSpecs.Tests.ChainData

/-!
# `EthCLSpecs.Tests.GloasPyspecReplayPins`: the index assignment on chains the upstream pyspec built

`GloasValidatorIndexPins` runs two chains across the Gloas upgrade from a hand-built Fulu
state. This module runs two from a genesis state, on chains of real blocks. The genesis state
and every signed block come from the upstream pyspec. `scripts/repro_validator_index_split.py`
builds them with the upstream test helpers and writes them, as SSZ in hex, to
`data/index_split.txt`. The model decodes them and replays them through
`ChainReplay.replayChain`, at `validated = true`. A block the replay accepts is a block whose
signature the model verified and whose post-state root the model and the pyspec agree on.

## The pyspec that built the blocks

The blocks come from the pyspec of the consensus-specs branch
`dapplion:gloas-onboard-cutoff`, at commit `e4bd955`, whose Fulu to Gloas upgrade
`Gloas/Upgrade.lean` and `Gloas/Operations.lean` port. The Gloas blocks of chain B carry
state roots computed after the upgrade. So the replay checks the Lean upgrade against the
Python text of the branch, on a queue that takes each branch of the onboarding function.

## The two chains

The preset is `minimal`, and Gloas activates at epoch 6, slot 48. The onboarding cutoff is
slot 32, the first slot of epoch 4.

* **Shared.** The genesis state with 64 validators, then 40 blocks with full attestations. Two
  blocks carry deposit requests of 32 ETH.
  * The block at slot 31, at or below the cutoff: key 64 with builder credentials `0xB0`, and
    key 65 with `0x01` credentials.
  * The block at slot 39, above the cutoff, four requests with builder credentials: key 66
    signed, key 67 unsigned, key 0 unsigned (validator 0 holds key 0), and key 66 again.
* **Chain A.** Seven more Fulu blocks with attestations, slots 41 to 47. The upgrade at slot
  48. Empty slots to 56.
* **Chain B.** No block in slots 41 to 47. The upgrade at slot 48. Eight Gloas blocks with
  attestations, slots 49 to 56.

Chain A justifies epoch 5 in time, so it finalizes epoch 4 at the last Fulu epoch transition.
The slot of the first two deposits is then finalized, and Fulu's `processPendingDeposits`
makes validators 64 and 65 from them. Chain B finalizes epoch 4 one epoch later, under Gloas,
so all six deposits are in its queue at the upgrade.

At v1.7.0-beta.4 the upgrade of chain B makes a builder from the deposit for key 64, and the
deposit for key 65 becomes validator 64: two chains with one finalized checkpoint hold two
keys at one index. The script shows that outcome with `--expect split`.

With the cutoff the deposit for key 64 stays in the queue of chain B, because its slot is at
or below slot 32. Chain B then makes validators 64 and 65 from the two deposits, as chain A
did. The four deposits of slot 39 are above the cutoff, and no chain applied them before the
fork. Each takes one way through the onboarding, on both chains: key 66 becomes a builder,
the unsigned deposit for key 67 is dropped, the unsigned deposit for validator 0 stays queued
as a top-up, and the second deposit for key 66 tops up the builder.

## What the theorems state

`replay_facts` reads the evaluated facts off the three replays. Both end states sit at slot 56
and hold the finalized checkpoint of epoch 4, which starts at slot 32, below the slot of the
shared state. Each registry has 66 validators, with one key at index 64 and one at index 65.
Each chain has one builder with 64 ETH and one queued deposit.

`validatorIndex_agrees_from_genesis` states the agreement at every index, and it takes that
part from the theorem `indexAssignment_fromFulu`
(`Proofs/Gloas/IndexAssignmentFromFulu.lean`), with no evaluation of a key. The replays give
the hypotheses: a reachable shared state, two end states reachable from it, and
`CompatibleFinality`. So the theorem applies to chains of real blocks, and its hypotheses hold
together.

## The finalized validators

`finalizedValidators_on_replay` applies the finalized-validator theorem
(`Proofs/Gloas/FinalizedValidators.lean`) to the same pair. That theorem gives the agreement
at every index up to 63, and it stops there: validator 64 has no finalized
`activation_eligibility_epoch` in either end state. The index-assignment theorem needs no
such hypothesis.

## Trust

One `native_decide` evaluates the three replays, on `CryptoBackend.ffi` and the FFI SHA-256.
The theorems therefore trust the compiler and the two native libraries. `fastHasherTag` brings the two
SHA-256 equivalence axioms into the axiom list through its `Hasher` instance, as in
`GloasValidatorIndexPins`.

The data file is the pyspec's output and no theorem depends on where it came from: the
theorems are about the decoded values. `include_str` reads the file when this module
elaborates. Lake does not track it, so a regenerated file needs a rebuild of this module.
Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.GloasPyspecReplayPins

open EthCLLib.Spec
open SizzLean
open EthCLSpecs EthCLSpecs.Proofs
open EthCLSpecs.Tests.ChainReplay
open EthCLSpecs.Tests.ChainData
open scoped EthCLSpecs.Gloas.Downgrade

/-- The Gloas `minimal` preset. -/
@[reducible] def preset : Gloas.Preset := Gloas.minimal

/-- The `minimal` config with Gloas at epoch 6, the override the reproduction script makes. -/
@[reducible] def config : Gloas.Config := { Gloas.minimalConfig with gloasForkEpoch := 6 }

-- The four instances every declaration below resolves, kept inside this module.

attribute [local instance] preset config fastHasherTag CryptoBackend.ffi

/-- The objects of the data file, in order. `include_str` reads the file, relative to this
module, when the module elaborates. -/
def dump : List (String × ByteArray) := parseDump (include_str "data/index_split.txt")

/-- The upstream genesis state: `create_genesis_state` at 64 validators of 32 ETH. -/
def genesis : Fulu.BeaconState := genesisOf dump

/-- The last state the two chains share: the genesis state after the 40 shared blocks, at
slot 40. `none` if the replay rejects. -/
def shared? : Option Fulu.BeaconState :=
  replayFulu (Fulu.forkSlot Gloas.Const.gloasForkEpoch) (fuluSteps (fuluBlocks dump "shared")) genesis

/-- Chain A from the shared state `t`: seven more Fulu blocks, the boundary slot, the upgrade,
and empty slots to 56. -/
def chainA? (t : Fulu.BeaconState) : Option Gloas.BeaconState :=
  replayChain (fuluSteps (fuluBlocks dump "chainA") ++ [.slots 48]) [.slots 56] t

/-- Chain B from the shared state `t`: empty slots to the boundary, the upgrade, and eight
Gloas blocks to slot 56. -/
def chainB? (t : Fulu.BeaconState) : Option Gloas.BeaconState :=
  replayChain [.slots 48] (gloasSteps (gloasBlocks dump "chainB")) t

/-- 64 ETH in Gwei: the balance of the one builder, from its two deposits of 32 ETH. -/
def builderBalance : Gloas.Gwei := 64000000000

/-- One evaluation of the three replays, and the facts the theorems read off them. All three
are accepted. The two end states sit at one slot with one finalized checkpoint, whose epoch
starts below the slot of the shared state.

* Each registry has 66 validators. Validators 64 and 65 have one public key each in the two
  end states, and two different keys between them. Validator 64 carries builder credentials:
  it is the deposit a chain without the cutoff would have made a builder from.
* Validator 64 has no `activation_eligibility_epoch` at or below the finalized epoch, in
  either end state. Validator 63, the last one of the genesis registry, has one in chain A.
* Each chain has one builder, with one key and the balance of two deposits, and one queued
  deposit. -/
def check : Bool :=
  match shared? with
  | none => false
  | some t =>
    match chainA? t, chainB? t with
    | some a, some b =>
      decide (a.slot = b.slot) && decide (a.finalizedCheckpoint = b.finalizedCheckpoint) &&
        decide ((Gloas.computeStartSlotAtEpoch a.finalizedCheckpoint.epoch).toNat < t.slot.toNat) &&
        decide ((Gloas.computeStartSlotAtEpoch b.finalizedCheckpoint.epoch).toNat < t.slot.toNat) &&
        decide (a.validators.val.size = 66) && decide (b.validators.val.size = 66) &&
        (match a.validators.val[64]?, b.validators.val[64]?,
            a.validators.val[65]?, b.validators.val[65]? with
          | some x, some y, some x', some y' =>
              decide (x.pubkey = y.pubkey) && decide (x'.pubkey = y'.pubkey) &&
              decide (x.pubkey ≠ x'.pubkey) &&
              Gloas.isBuilderWithdrawalCredential x.withdrawalCredentials &&
              decide (¬ x.activationEligibilityEpoch ≤ a.finalizedCheckpoint.epoch) &&
              decide (¬ y.activationEligibilityEpoch ≤ b.finalizedCheckpoint.epoch)
          | _, _, _, _ => false) &&
        (match a.validators.val[63]? with
          | some x => decide (x.activationEligibilityEpoch ≤ a.finalizedCheckpoint.epoch)
          | none => false) &&
        decide (a.builders.val.map (·.pubkey) = b.builders.val.map (·.pubkey)) &&
        decide (a.builders.val.map (·.balance) = #[builderBalance]) &&
        decide (b.builders.val.map (·.balance) = #[builderBalance]) &&
        decide (a.pendingDeposits.val.size = 1) && decide (b.pendingDeposits.val.size = 1)
    | _, _ => false

/-- The replays pass the check. One `native_decide` runs the 55 block transitions, with each
block signature, attestation signature and state root verified by the model. -/
theorem check_true : check = true := by native_decide

/-- The facts of `check`, as propositions about the shared state and the two end states. -/
theorem replay_facts :
    ∃ (t : Fulu.BeaconState) (a b : Gloas.BeaconState),
      shared? = some t ∧ chainA? t = some a ∧ chainB? t = some b ∧ a.slot = b.slot ∧
      a.finalizedCheckpoint = b.finalizedCheckpoint ∧
      Gloas.FinalizedBelow t.slot a ∧ Gloas.FinalizedBelow t.slot b ∧
      a.validators.val.size = 66 ∧ b.validators.val.size = 66 ∧
      (∃ (h' : 64 < a.validators.val.size) (h'' : 64 < b.validators.val.size)
          (k' : 65 < a.validators.val.size) (k'' : 65 < b.validators.val.size),
        a.validators.val[64].pubkey = b.validators.val[64].pubkey ∧
        a.validators.val[65].pubkey = b.validators.val[65].pubkey ∧
        a.validators.val[64].pubkey ≠ a.validators.val[65].pubkey ∧
        Gloas.isBuilderWithdrawalCredential a.validators.val[64].withdrawalCredentials = true ∧
        ¬ a.validators.val[64].activationEligibilityEpoch ≤ a.finalizedCheckpoint.epoch ∧
        ¬ b.validators.val[64].activationEligibilityEpoch ≤ b.finalizedCheckpoint.epoch) ∧
      (∃ (h : 63 < a.validators.val.size),
        a.validators.val[63].activationEligibilityEpoch ≤ a.finalizedCheckpoint.epoch) ∧
      a.builders.val.map (·.pubkey) = b.builders.val.map (·.pubkey) ∧
      a.builders.val.map (·.balance) = #[builderBalance] ∧
      b.builders.val.map (·.balance) = #[builderBalance] ∧
      a.pendingDeposits.val.size = 1 ∧ b.pendingDeposits.val.size = 1 := by
  have h := check_true
  unfold check at h
  split at h
  · cases h
  · next t ht =>
    split at h
    · next a b ha hb =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hslot, hfin⟩, hfa⟩, hfb⟩, hsa⟩, hsb⟩, h64⟩, h63⟩, hbk⟩, hba⟩, hbb⟩, hpa⟩,
        hpb⟩ := h
      split at h64
      · next x y x' y' hx hy hx' hy' =>
        obtain ⟨h1, rfl⟩ := Array.getElem?_eq_some_iff.mp hx
        obtain ⟨h2, rfl⟩ := Array.getElem?_eq_some_iff.mp hy
        obtain ⟨h1', rfl⟩ := Array.getElem?_eq_some_iff.mp hx'
        obtain ⟨h2', rfl⟩ := Array.getElem?_eq_some_iff.mp hy'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h64
        obtain ⟨⟨⟨⟨⟨he64, he65⟩, hne⟩, hcred⟩, hea⟩, heb⟩ := h64
        split at h63
        · next z hz =>
          obtain ⟨h3, rfl⟩ := Array.getElem?_eq_some_iff.mp hz
          exact ⟨t, a, b, ht, ha, hb, hslot, hfin, hfa, hfb, hsa, hsb,
            ⟨h1, h2, h1', h2', he64, he65, hne, hcred, hea, heb⟩,
            ⟨h3, of_decide_eq_true h63⟩, hbk, hba, hbb, hpa, hpb⟩
        · cases h63
      · cases h64
    · cases h

/-- The genesis state satisfies `SimpleStateInvariants`, the hypothesis the in-fork theorem
puts on its anchors. -/
theorem genesis_invariants : Fulu.SimpleStateInvariants genesis :=
  ⟨by native_decide,
    ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩,
    ⟨by native_decide, by native_decide, by native_decide⟩,
    ⟨by native_decide, by native_decide⟩⟩

/-- The scenario's config satisfies the rules the proofs put on a config. -/
theorem config_valid : @Gloas.ConfigValid preset config := by
  apply @Gloas.ConfigValid.mk preset config <;> decide

/-- The shared state is reachable from the genesis state. -/
theorem shared_reachable {t : Fulu.BeaconState} (h : shared? = some t) :
    Fulu.ReachableState (Fulu.Anchors.only genesis) true Gloas.Const.gloasForkEpoch t :=
  replayFulu_reachable _ genesis t h (.anchor rfl (by native_decide))

/-- A state `t` reachable from the upstream genesis state, and two Gloas states reachable from
`t`, at one slot and with one finalized checkpoint that is older than `t`, hold one public key
at every validator index. Every block is one the upstream pyspec built and signed, and the
flag is `true`, so the model checked each signature and each state root on the way.

The agreement is the conclusion of `indexAssignment_fromFulu`, applied to the three
reachability facts and to `CompatibleFinality`. No key is evaluated for it. Each registry has
66 validators, so the conclusion covers the two validators the chains made from the deposits
of slot 31, on two sides of the upgrade. -/
theorem validatorIndex_agrees_from_genesis :
    ∃ (t : Fulu.BeaconState) (w' w'' : Gloas.BeaconState),
      Fulu.ReachableState (Fulu.Anchors.only genesis) true Gloas.Const.gloasForkEpoch t ∧
      Gloas.ReachableState (Gloas.Anchors.onlyFulu t) true Gloas.Const.farFutureEpoch w' ∧
      Gloas.ReachableState (Gloas.Anchors.onlyFulu t) true Gloas.Const.farFutureEpoch w'' ∧
      w'.slot = w''.slot ∧
      w'.finalizedCheckpoint = w''.finalizedCheckpoint ∧
      Gloas.FinalizedBelow t.slot w' ∧ Gloas.FinalizedBelow t.slot w'' ∧
      w'.validators.val.size = 66 ∧ w''.validators.val.size = 66 ∧
      ∀ (i : Nat) (h' : i < w'.validators.val.size) (h'' : i < w''.validators.val.size),
        w'.validators.val[i].pubkey = w''.validators.val[i].pubkey := by
  obtain ⟨t, a, b, ht, ha, hb, hslot, hfin, hfa, hfb, hsa, hsb, -⟩ := replay_facts
  exact ⟨t, a, b, shared_reachable ht, replayChain_reachable ha, replayChain_reachable hb,
    hslot, hfin, hfa, hfb, hsa, hsb,
    Gloas.indexAssignment_fromFulu (anchors := Fulu.Anchors.only genesis)
      (fun _ h => h ▸ genesis_invariants) (shared_reachable ht)
      (replayChain_reachable ha) (replayChain_reachable hb) (Or.inl hfa)⟩

/-! ## The finalized validators -/

/-- The finalized-validator theorem on the two replayed chains, and where it stops.

* Validator 63 has a finalized `activation_eligibility_epoch` in chain A, so
  `finalizedValidators_pubkey_eq_fromFulu` gives one public key in both end states at every
  index up to 63. That part is a consequence of the theorem, with no evaluation of the keys.
* Validator 64 has no finalized `activation_eligibility_epoch` in either end state, so that
  theorem says nothing about index 64. `validatorIndex_agrees_from_genesis` covers it.

The preset has eight slots per epoch, which `decide` checks. -/
theorem finalizedValidators_on_replay :
    ∃ (t : Fulu.BeaconState) (w' w'' : Gloas.BeaconState),
      Fulu.ReachableState (Fulu.Anchors.only genesis) true Gloas.Const.gloasForkEpoch t ∧
      Gloas.ReachableState (Gloas.Anchors.onlyFulu t) true Gloas.Const.farFutureEpoch w' ∧
      Gloas.ReachableState (Gloas.Anchors.onlyFulu t) true Gloas.Const.farFutureEpoch w'' ∧
      (∀ j, j ≤ 63 →
        ∃ (h' : j < w'.validators.val.size) (h'' : j < w''.validators.val.size),
          w''.validators.val[j].pubkey = w'.validators.val[j].pubkey) ∧
      ∃ (h' : 64 < w'.validators.val.size) (h'' : 64 < w''.validators.val.size),
        ¬ w'.validators.val[64].activationEligibilityEpoch ≤ w'.finalizedCheckpoint.epoch ∧
        ¬ w''.validators.val[64].activationEligibilityEpoch ≤ w''.finalizedCheckpoint.epoch := by
  obtain ⟨t, a, b, ht, ha, hb, -, -, hfa, -, -, -, ⟨h1, h2, -, -, -, -, -, -, hea, heb⟩,
    ⟨h63, he63⟩, -⟩ := replay_facts
  refine ⟨t, a, b, shared_reachable ht, replayChain_reachable ha, replayChain_reachable hb,
    fun j hj => ?_, h1, h2, hea, heb⟩
  exact Gloas.finalizedValidators_pubkey_eq_fromFulu (by decide)
    (anchors := Fulu.Anchors.only genesis) (fun _ h => h ▸ genesis_invariants)
    (shared_reachable ht) (replayChain_reachable ha) (replayChain_reachable hb)
    hfa.atOrBefore hj h63 he63

end EthCLSpecs.Tests.GloasPyspecReplayPins
