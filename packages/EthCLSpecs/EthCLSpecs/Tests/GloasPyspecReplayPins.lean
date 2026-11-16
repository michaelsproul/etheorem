import EthCLSpecs.Proofs.Gloas.FinalizedValidators
import EthCLSpecs.Tests.ChainReplay

/-!
# `EthCLSpecs.Tests.GloasPyspecReplayPins`: the index split on chains the upstream pyspec built

`GloasValidatorIndexPins` proves the index split from a hand-built Fulu state. This module
proves it from a genesis state, on chains of real blocks. The genesis state and every signed
block come from the upstream pyspec at v1.7.0-beta.4. `scripts/repro_validator_index_split.py`
builds them with the upstream test helpers and writes them, as SSZ in hex, to
`data/index_split.txt`. The model decodes them and replays them through
`ChainReplay.replayChain`, at `validated = true`. A block the replay accepts is a block whose
signature the model verified and whose post-state root the model and the pyspec agree on.

## The two chains

The preset is `minimal`, and Gloas activates at epoch 6, slot 48.

* **Shared.** The genesis state with 64 validators, then 40 blocks with full attestations. The
  block at slot 31 carries two deposit requests of 32 ETH: key 64 with builder credentials
  `0xB0`, and key 65 with `0x01` credentials.
* **Chain A.** Seven more Fulu blocks with attestations, slots 41 to 47. The upgrade at slot
  48. Empty slots to 56.
* **Chain B.** No block in slots 41 to 47. The upgrade at slot 48. Eight Gloas blocks with
  attestations, slots 49 to 56.

Chain A justifies epoch 5 in time, so it finalizes epoch 4 at the last Fulu epoch transition.
The deposits' slot is then finalized, and Fulu's `processPendingDeposits` makes validators 64
and 65 from the two deposits. Chain B finalizes epoch 4 one epoch later, under Gloas. By then
`onboardBuildersFromPendingDeposits` has made a builder from the first deposit, and the second
becomes validator 64.

Both end states sit at slot 56 and hold the finalized checkpoint of epoch 4, with one root.
`validators[64]` is key 64 on chain A and key 65 on chain B.

## What the theorems state

`validatorIndex_diverges_from_genesis` gives the shared state at slot 40, reachable from the
genesis state, and the two end states, both `ReachableState` from the shared state.
`indexAssignmentFromFulu_false` is the negation of the property: `IndexAssignmentFromFulu`
(`Proofs/Gloas/IndexAssignment.lean`) is the statement of the in-fork theorem
`indexAssignment_of_compatibleFinality` with a Fulu state as the common state, and it is
false. Both end states have finalized epoch 4, which starts at slot 32, below the shared
state's slot, so `CompatibleFinality` holds on both of its sides. The genesis state satisfies
`SimpleStateInvariants` and the config satisfies `ConfigValid`.

## The finalized validators

`finalizedValidators_on_replay` applies the finalized-validator theorem
(`Proofs/Gloas/FinalizedValidators.lean`) to the same pair. The two end states agree at every
index up to 63, and validator 64 has no finalized `activation_eligibility_epoch` in either.
So the rule "hold a validator once its eligibility epoch is finalized" keeps index 64 out of
a client's map on both chains.

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
open scoped EthCLSpecs.Gloas.Downgrade

/-- The Gloas `minimal` preset. -/
@[reducible] def preset : Gloas.Preset := Gloas.minimal

/-- The `minimal` config with Gloas at epoch 6, the override the reproduction script makes. -/
@[reducible] def config : Gloas.Config := { Gloas.minimalConfig with gloasForkEpoch := 6 }

-- The four instances every declaration below resolves, kept inside this module.

attribute [local instance] preset config fastHasherTag CryptoBackend.ffi

/-- The value of one lowercase hex digit. -/
def hexDigit (c : Char) : UInt8 :=
  if c.isDigit then (c.toNat - '0'.toNat).toUInt8 else (c.toNat - 'a'.toNat + 10).toUInt8

/-- The bytes a hex string spells, two digits per byte. -/
def ofHex (s : String) : ByteArray :=
  go s.toList ByteArray.empty
where
  go : List Char → ByteArray → ByteArray
    | a :: b :: rest, acc => go rest (acc.push (hexDigit a * 16 + hexDigit b))
    | _, acc => acc

/-- The objects of the data file, in order: one `name hex` line each. `include_str` reads
the file, relative to this module, when the module elaborates. -/
def dump : List (String × ByteArray) :=
  ((include_str "data/index_split.txt").splitOn "\n").filterMap fun line =>
    match line.splitOn " " with
    | [name, hex] => some (name, ofHex hex)
    | _ => none

/-- The objects with the given name, in file order. -/
def objects (name : String) : List ByteArray := (dump.filter (·.1 == name)).map (·.2)

/-- The upstream genesis state: `create_genesis_state` at 64 validators of 32 ETH. A decode
failure gives the default state, which `check` would then reject at the first block. -/
def genesis : Fulu.BeaconState :=
  match objects "genesis" with
  | [bytes] => (SSZ.deserialize (T := Fulu.BeaconState) bytes).toOption.getD default
  | _ => default

/-- The signed Fulu blocks with the given name. -/
def fuluBlocks (name : String) : List Fulu.SignedBeaconBlock :=
  (objects name).filterMap fun bytes =>
    (SSZ.deserialize (T := Fulu.SignedBeaconBlock) bytes).toOption

/-- The signed Gloas blocks with the given name. -/
def gloasBlocks (name : String) : List Gloas.SignedBeaconBlock :=
  (objects name).filterMap fun bytes =>
    (SSZ.deserialize (T := Gloas.SignedBeaconBlock) bytes).toOption

/-- `state_transition` for each block: advance to the block's slot, then apply the block. -/
def fuluSteps (blocks : List Fulu.SignedBeaconBlock) : List FuluStep :=
  blocks.flatMap fun sb => [.slots sb.message.slot, .block sb]

/-- `state_transition` for each Gloas block, as `fuluSteps`. -/
def gloasSteps (blocks : List Gloas.SignedBeaconBlock) : List GloasStep :=
  blocks.flatMap fun sb => [.slots sb.message.slot, .block sb]

/-- The last state the two chains share: the genesis state after the 40 shared blocks, at
slot 40. `none` if the replay rejects. -/
def shared? : Option Fulu.BeaconState :=
  replayFulu (Fulu.forkSlot Gloas.Const.gloasForkEpoch) (fuluSteps (fuluBlocks "shared")) genesis

/-- Chain A from the shared state `t`: seven more Fulu blocks, the boundary slot, the upgrade,
and empty slots to 56. -/
def chainA? (t : Fulu.BeaconState) : Option Gloas.BeaconState :=
  replayChain (fuluSteps (fuluBlocks "chainA") ++ [.slots 48]) [.slots 56] t

/-- Chain B from the shared state `t`: empty slots to the boundary, the upgrade, and eight
Gloas blocks to slot 56. -/
def chainB? (t : Fulu.BeaconState) : Option Gloas.BeaconState :=
  replayChain [.slots 48] (gloasSteps (gloasBlocks "chainB")) t

/-- One evaluation of the three replays, and the facts the theorems read off them. All three
are accepted. The two end states sit at one slot with one finalized checkpoint, whose epoch
starts below the slot of the shared state, and validator 64 has two public keys.

The last three lines read the `activation_eligibility_epoch` of two validators. Validator 64
has none at or below the finalized epoch, in either end state. Validator 63, the last one of
the genesis registry, has one in chain A. -/
def check : Bool :=
  match shared? with
  | none => false
  | some t =>
    match chainA? t, chainB? t with
    | some a, some b =>
      decide (a.slot = b.slot) && decide (a.finalizedCheckpoint = b.finalizedCheckpoint) &&
        decide ((Gloas.computeStartSlotAtEpoch a.finalizedCheckpoint.epoch).toNat < t.slot.toNat) &&
        decide ((Gloas.computeStartSlotAtEpoch b.finalizedCheckpoint.epoch).toNat < t.slot.toNat) &&
        (match a.validators.val[64]?, b.validators.val[64]? with
          | some x, some y => decide (x.pubkey ≠ y.pubkey) &&
              decide (¬ x.activationEligibilityEpoch ≤ a.finalizedCheckpoint.epoch) &&
              decide (¬ y.activationEligibilityEpoch ≤ b.finalizedCheckpoint.epoch)
          | _, _ => false) &&
        (match a.validators.val[63]? with
          | some x => decide (x.activationEligibilityEpoch ≤ a.finalizedCheckpoint.epoch)
          | none => false)
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
      (∃ (h' : 64 < a.validators.val.size) (h'' : 64 < b.validators.val.size),
        a.validators.val[64].pubkey ≠ b.validators.val[64].pubkey ∧
        ¬ a.validators.val[64].activationEligibilityEpoch ≤ a.finalizedCheckpoint.epoch ∧
        ¬ b.validators.val[64].activationEligibilityEpoch ≤ b.finalizedCheckpoint.epoch) ∧
      ∃ (h : 63 < a.validators.val.size),
        a.validators.val[63].activationEligibilityEpoch ≤ a.finalizedCheckpoint.epoch := by
  have h := check_true
  unfold check at h
  split at h
  · cases h
  · next t ht =>
    split at h
    · next a b ha hb =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨hslot, hfin⟩, hfa⟩, hfb⟩, h64⟩, h63⟩ := h
      split at h64
      · next x y hx hy =>
        obtain ⟨h1, rfl⟩ := Array.getElem?_eq_some_iff.mp hx
        obtain ⟨h2, rfl⟩ := Array.getElem?_eq_some_iff.mp hy
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h64
        obtain ⟨⟨hne, hea⟩, heb⟩ := h64
        split at h63
        · next z hz =>
          obtain ⟨h3, rfl⟩ := Array.getElem?_eq_some_iff.mp hz
          exact ⟨t, a, b, ht, ha, hb, hslot, hfin, hfa, hfb, ⟨h1, h2, hne, hea, heb⟩, h3,
            of_decide_eq_true h63⟩
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
`t`, at one slot and with one finalized checkpoint that is older than `t`, hold two public
keys at validator index 64. Every block is one the upstream pyspec built and signed, and the
flag is `true`, so the model checked each signature and each state root on the way. -/
theorem validatorIndex_diverges_from_genesis :
    ∃ (t : Fulu.BeaconState) (w' w'' : Gloas.BeaconState),
      Fulu.ReachableState (Fulu.Anchors.only genesis) true Gloas.Const.gloasForkEpoch t ∧
      Gloas.ReachableState (Gloas.Anchors.onlyFulu t) true Gloas.Const.farFutureEpoch w' ∧
      Gloas.ReachableState (Gloas.Anchors.onlyFulu t) true Gloas.Const.farFutureEpoch w'' ∧
      w'.slot = w''.slot ∧
      w'.finalizedCheckpoint = w''.finalizedCheckpoint ∧
      Gloas.FinalizedBelow t.slot w' ∧ Gloas.FinalizedBelow t.slot w'' ∧
      ∃ (i : Nat) (h' : i < w'.validators.val.size) (h'' : i < w''.validators.val.size),
        w'.validators.val[i].pubkey ≠ w''.validators.val[i].pubkey := by
  obtain ⟨t, a, b, ht, ha, hb, hslot, hfin, hfa, hfb, ⟨h1, h2, hne, -, -⟩, -⟩ := replay_facts
  exact ⟨t, a, b, shared_reachable ht, replayChain_reachable ha, replayChain_reachable hb,
    hslot, hfin, hfa, hfb, 64, h1, h2, hne⟩

/-- The index assignment is not stable across the Gloas upgrade: `IndexAssignmentFromFulu` is
false.

`IndexAssignmentFromFulu` is the statement of the in-fork theorem
`indexAssignment_of_compatibleFinality` with a Fulu state as the common state. Here the common
state is the upstream chain at slot 40, reachable from the upstream genesis state, which
satisfies `SimpleStateInvariants`. Both end states have finalized epoch 4, which starts at
slot 32, so both sides of `CompatibleFinality` hold. The proof trusts the compiler and the two
native libraries; the module docstring says what was evaluated. -/
theorem indexAssignmentFromFulu_false : ¬ Gloas.IndexAssignmentFromFulu := by
  obtain ⟨t, a, b, ht, ha, hb, -, -, hfa, -, ⟨h1, h2, hne, -, -⟩, -⟩ := replay_facts
  exact Gloas.not_indexAssignmentFromFulu (anchors := Fulu.Anchors.only genesis)
    (fun _ h => h ▸ genesis_invariants) (shared_reachable ht)
    (replayChain_reachable ha) (replayChain_reachable hb) (Or.inl hfa) h1 h2 hne

/-! ## The finalized validators -/

/-- The finalized-validator theorem on the two replayed chains. It applies to the pair that
refutes `IndexAssignmentFromFulu`, and it stops in front of the index where they differ.

* Validator 63 has a finalized `activation_eligibility_epoch` in chain A, so
  `finalizedValidators_pubkey_eq_fromFulu` gives one public key in both end states at every
  index up to 63. That part is a consequence of the theorem, with no evaluation of the keys.
* Validator 64, the index with two keys, has no finalized `activation_eligibility_epoch` in
  either end state. A map that holds the finalized validators alone holds neither key.

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
        w'.validators.val[64].pubkey ≠ w''.validators.val[64].pubkey ∧
        ¬ w'.validators.val[64].activationEligibilityEpoch ≤ w'.finalizedCheckpoint.epoch ∧
        ¬ w''.validators.val[64].activationEligibilityEpoch ≤ w''.finalizedCheckpoint.epoch := by
  obtain ⟨t, a, b, ht, ha, hb, -, -, hfa, -, h64, h63, he63⟩ := replay_facts
  refine ⟨t, a, b, shared_reachable ht, replayChain_reachable ha, replayChain_reachable hb,
    fun j hj => ?_, h64⟩
  exact Gloas.finalizedValidators_pubkey_eq_fromFulu (by decide)
    (anchors := Fulu.Anchors.only genesis) (fun _ h => h ▸ genesis_invariants)
    (shared_reachable ht) (replayChain_reachable ha) (replayChain_reachable hb)
    hfa.atOrBefore hj h63 he63

end EthCLSpecs.Tests.GloasPyspecReplayPins
