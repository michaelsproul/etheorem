import EthCLSpecs.Proofs.Fulu.Reachable

/-!
# `EthCLSpecs.Tests.DepositScenario`: one Fulu state, two chains, and a deposit queue

The Fulu half of a concrete scenario that `GloasValidatorIndexPins` and
`HezeValidatorIndexPins` finish. Each of them runs two chains with one finalized checkpoint
across a fork upgrade, and compares the public keys the chains hold at one validator index.
Across the Gloas upgrade the keys agree, by the onboarding cutoff. Across the Heze upgrade
they differ. This module builds the common ancestor and the one block that separates the
chains.

## The two chains

`anchor queue` is a Fulu state at slot 519, the last slot of epoch 64 at eight slots per
epoch. It has sixteen active validators, a finalized checkpoint at epoch 62, and the deposit
queue `queue`. The callers put `topUp` first in the queue, a deposit for validator 1.

* The quiet chain has no block at slot 519. At the epoch transition `ppdLoop`
  (`Fulu/EpochProcessing.lean:234-267`) meets `topUp` first, and `topUp` takes the churn of
  the epoch or more.
* The exit chain has `signedExitBlock` at slot 519, a block that carries a voluntary exit of
  validator 1. At the epoch transition `ppdLoop` postpones `topUp`, because validator 1 is
  exiting. The churn is free, so the scan goes on to the deposits behind `topUp`.

So the exit chain makes validators from the queue one epoch or more before the quiet chain
does. A fork upgrade that falls in that gap sees two queues.

## Why the definitions bind the preset

Gloas reaches the Fulu `Preset` and `Config` through its `Downgrade` bridge, and Heze through
two bridges. The definitions here take both as instance arguments, so each pins module
instantiates them at its own `minimal` preset. The slot and epoch numbers assume the eight
slots per epoch and the 64-epoch `SHARD_COMMITTEE_PERIOD` of `minimal`.

## Running a step to a value

`ReachableState` takes each step as an equation `runPure act v = .ok ((), w)`. A concrete run
gives `w` by evaluation alone, so `postOf` names the result, and `succeeds` is the `Bool` that
`native_decide` checks. `runPure_eq_of_succeeds` joins the two.

## Signatures

Every key in the scenario is a known BLS secret key, and every signature comes from blst
through `LeanHazmat.Bls.sign`. The scenario therefore runs on `CryptoBackend.ffi`, with no
signature check switched off.
-/

set_option autoImplicit false

namespace EthCLSpecs.Tests.DepositScenario

open EthCLLib.Spec
open EthCLLib.Proofs (pureState runPure)
open SizzLean (SSZRepr)
open SizzLean.Cache
open EthCLSpecs.Fulu
open EthCLSpecs.Proofs.Fulu (FuluRun)

/-! ## Running a step to a value -/

section Run

variable [HasherTag]

/-- The post-state of `act` on `v`. A rejected run returns `v`; `succeeds` tells the two
apart. -/
def postOf {T : Type} [SSZRepr T]
    (act : StateT (SSZ.Box HasherTag.H T) (Except StateTransitionError) Unit) (v : T) : T :=
  match runPure act v with
  | .ok (_, w) => w
  | .error _ => v

/-- `true` when the run of `act` on `v` does not reject. -/
def succeeds {T : Type} [SSZRepr T]
    (act : StateT (SSZ.Box HasherTag.H T) (Except StateTransitionError) Unit) (v : T) : Bool :=
  match runPure act v with
  | .ok _ => true
  | .error _ => false

/-- A run that `succeeds` ends in `postOf`. The `ok` case closes by `rfl`: the result pair is
`((), w)` up to the eta rules for `Unit` and for pairs. -/
theorem runPure_eq_of_succeeds {T : Type} [SSZRepr T]
    {act : StateT (SSZ.Box HasherTag.H T) (Except StateTransitionError) Unit} {v : T}
    (h : succeeds act v = true) : runPure act v = .ok ((), postOf act v) := by
  unfold succeeds at h
  unfold postOf
  cases hr : runPure act v with
  | ok p => rfl
  | error e => rw [hr] at h; cases h

end Run

/-! ## Keys and signatures -/

/-- The BLS secret key with scalar `n`, as 32 big-endian bytes. The validators use the
scalars 1 to 16, and the depositors of new keys use scalars above 100. -/
def secretKey (n : Nat) : ByteArray := ⟨(Array.replicate 31 (0 : UInt8)).push (UInt8.ofNat n)⟩

/-- The public key of `secretKey n`, from blst. -/
def pubkey (n : Nat) : Vector UInt8 48 := bytesToVec 48 (LeanHazmat.Bls.skToPk (secretKey n))

/-- The signature of `secretKey n` over a signing root, from blst. -/
def sign (n : Nat) (signingRoot : Vector UInt8 32) : Vector UInt8 96 :=
  bytesToVec 96 (LeanHazmat.Bls.sign (secretKey n) (vecToBytes signingRoot))

/-- `eth` ETH in Gwei. -/
def gwei (eth : Nat) : UInt64 := UInt64.ofNat (eth * 1000000000)

/-- Withdrawal credentials with the prefix byte `pfx`, eleven zero bytes, and a fixed 20-byte
address. -/
def creds (pfx : UInt8) : Vector UInt8 32 :=
  Vector.ofFn fun i : Fin 32 => if i.val = 0 then pfx else if i.val < 12 then 0 else 0xaa

section

variable [Preset] [Config] [HasherTag]

/-- An `SSZList` from an array. The preset is a variable here, so no proof of the capacity
bound exists at this point; the list is empty when the array does not fit. Every array in the
scenario has three elements or sixteen, far under each capacity of `minimal`. -/
def listOf {α : Type} {cap : Nat} (a : Array α) : SizzLean.Repr.SSZList α cap :=
  if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], Nat.zero_le cap⟩

/-! ## The deposits -/

/-- The proof-of-possession `is_valid_deposit_signature` checks, signed by `secretKey n`. -/
def depositSignature (n : Nat) (wc : Bytes32) (amount : Gwei) : BLSSignature :=
  let msg : DepositMessage := { pubkey := pubkey n, withdrawalCredentials := wc, amount }
  let domain := computeDomain Const.domainDeposit Const.genesisForkVersion (Vector.replicate 32 0)
  sign n (computeSigningRoot msg domain)

/-- A deposit of `eth` ETH for validator 1, which holds key 2. The spec does not check the
signature of a deposit for a key the registry holds, so it is zero. The slot is below the
finalized slot 496. -/
def topUp (eth : Nat) : PendingDeposit :=
  { pubkey := pubkey 2, withdrawalCredentials := creds 0x01, amount := gwei eth,
    signature := Vector.replicate 96 0, slot := 480 }

/-- A deposit of 32 ETH for the new key `n`, with credentials of prefix `pfx` and a valid
proof-of-possession. Fulu makes a validator from it, whatever the prefix. -/
def newKeyDeposit (n : Nat) (pfx : UInt8) (slot : Slot) : PendingDeposit :=
  { pubkey := pubkey n, withdrawalCredentials := creds pfx, amount := gwei 32,
    signature := depositSignature n (creds pfx) (gwei 32), slot }

/-! ## The anchor -/

/-- The registry size of the anchor. Sixteen validators give each of the eight slots a
committee of two, which the Gloas PTC computation needs to be non-empty. -/
def numValidators : Nat := 16

/-- Validator `i` of the anchor holds key `i + 1`: active since epoch 0, 32 ETH, `0x01`
credentials, no exit. -/
def validator (i : Nat) : Validator :=
  { pubkey := pubkey (i + 1), withdrawalCredentials := creds 0x01, effectiveBalance := gwei 32,
    slashed := false, activationEligibilityEpoch := 0, activationEpoch := 0,
    exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }

/-- The finalized checkpoint of the anchor, at epoch 62. Its start slot is 496, above the
slot of each queued deposit. The two justified checkpoints hold the same value. -/
def finalized : Checkpoint := { epoch := 62, root := Vector.replicate 32 0x62 }

/-- The anchor with a zero proposer lookahead. `anchor` fills the lookahead from this state's
own shuffling. No validator has a participation flag, so no epoch transition below justifies
a checkpoint, and the finalized checkpoint stays at `finalized` on every chain. -/
def anchorBase (queue : Array PendingDeposit) : BeaconState :=
  { (default : BeaconState) with
    slot := 519
    forkData := { previousVersion := Const.electraForkVersion,
                  currentVersion := Const.fuluForkVersion, epoch := 0 }
    latestBlockHeader :=
      { slot := 518, proposerIndex := 0, parentRoot := Vector.replicate 32 1,
        stateRoot := Vector.replicate 32 2, bodyRoot := Vector.replicate 32 3 }
    validators := listOf (Array.ofFn (n := numValidators) fun i => validator i.val)
    balances := listOf (Array.replicate numValidators (gwei 32))
    previousEpochParticipation := listOf (Array.replicate numValidators 0)
    currentEpochParticipation := listOf (Array.replicate numValidators 0)
    inactivityScores := listOf (Array.replicate numValidators 0)
    previousJustifiedCheckpoint := finalized
    currentJustifiedCheckpoint := finalized
    finalizedCheckpoint := finalized
    currentSyncCommittee :=
      { pubkeys := Vector.ofFn fun i => pubkey (i.val % numValidators + 1),
        aggregatePubkey := pubkey 1 }
    nextSyncCommittee :=
      { pubkeys := Vector.ofFn fun i => pubkey (i.val % numValidators + 1),
        aggregatePubkey := pubkey 1 }
    pendingDeposits := listOf queue }

/-- The common ancestor of the two chains: a Fulu state at slot 519 with the deposit queue
`queue`. The proposer lookahead holds the proposers of epochs 64 and 65, as
`get_beacon_proposer_indices` computes them on `anchorBase`. -/
def anchor (queue : Array PendingDeposit) : BeaconState :=
  let base := anchorBase queue
  let current := (getBeaconProposerIndices (pureState base) 64).toOption.getD #[]
  let next := (getBeaconProposerIndices (pureState base) 65).toOption.getD #[]
  { base with
    proposerLookahead := Vector.ofFn fun i : Fin (2 * Const.slotsPerEpoch) =>
      if i.val < Const.slotsPerEpoch then current[i.val]!
      else next[i.val - Const.slotsPerEpoch]! }

/-! ## The block at slot 519 -/

/-- The proposer of slot 519, from the anchor's lookahead. Validator `i` signs with key
`i + 1`. -/
def proposer (queue : Array PendingDeposit) : ValidatorIndex :=
  getBeaconProposerIndex (pureState (anchor queue))

/-- The voluntary exit of validator 1, signed by its key over the Capella exit domain. Epoch
64 is the first epoch at which a validator active since epoch 0 may exit. -/
def exit (queue : Array PendingDeposit) : SignedVoluntaryExit :=
  let message : VoluntaryExit := { epoch := 64, validatorIndex := 1 }
  let domain := computeDomain Const.domainVoluntaryExit Const.capellaForkVersion
    (anchor queue).genesisValidatorsRoot
  { message, signature := sign 2 (computeSigningRoot message domain) }

/-- The body of the block at slot 519. It carries the exit and no other operation. The RANDAO
reveal is the proposer's signature over epoch 64. The sync aggregate has no participant, so
its signature is the point at infinity. The payload extends the anchor's payload header. -/
def exitBlockBody (queue : Array PendingDeposit) : BeaconBlockBody :=
  let v := anchor queue
  let randaoDomain := getDomain (pureState v) Const.domainRandao 64
  { (default : BeaconBlockBody) with
    randaoReveal :=
      sign ((proposer queue).toNat + 1) (computeSigningRoot (64 : Epoch) randaoDomain)
    voluntaryExits := listOf #[exit queue]
    syncAggregate :=
      { syncCommitteeBits := default, syncCommitteeSignature := Const.g2PointAtInfinity }
    executionPayload :=
      { (default : ExecutionPayload) with
        parentHash := v.latestExecutionPayloadHeader.blockHash
        prevRandao := v.randaoMixes[0]!
        timestamp := (computeTimeAtSlot v.genesisTime 519).toOption.getD 0 } }

/-- The block with a zero state root. `processBlock` does not read the state root, so this
block gives the post-state whose root the sealed block claims. -/
def exitBlockUnsealed (queue : Array PendingDeposit) : BeaconBlock :=
  { slot := 519, proposerIndex := proposer queue,
    parentRoot := htr (anchor queue).latestBlockHeader,
    stateRoot := Vector.replicate 32 0, body := exitBlockBody queue }

variable [CryptoBackend]

/-- The block at slot 519, with the root of its own post-state. -/
def exitBlock (queue : Array PendingDeposit) : BeaconBlock :=
  { exitBlockUnsealed queue with
    stateRoot :=
      htr (postOf (processBlock (StateTransition := FuluRun) (exitBlockUnsealed queue))
        (anchor queue)) }

/-- The signed block: the proposer's signature over the block, in the proposer domain. -/
def signedExitBlock (queue : Array PendingDeposit) : SignedBeaconBlock :=
  let domain := getDomain (pureState (anchor queue)) Const.domainBeaconProposer 64
  { message := exitBlock queue,
    signature := sign ((proposer queue).toNat + 1) (computeSigningRoot (exitBlock queue) domain) }

/-! ## The two chains, up to the Fulu boundary -/

/-- The quiet chain at slot 520: the anchor advanced through the epoch 64 transition with no
block. -/
def quietBoundary (queue : Array PendingDeposit) : BeaconState :=
  postOf (processSlots (StateTransition := FuluRun) 520) (anchor queue)

/-- The exit chain after its block at slot 519. Validator 1 has an exit epoch. -/
def exitBlockPost (queue : Array PendingDeposit) : BeaconState :=
  postOf (processBlock (StateTransition := FuluRun) (signedExitBlock queue).message)
    (anchor queue)

/-- The exit chain at slot 520: the block's post-state advanced through the epoch 64
transition. -/
def exitBoundary (queue : Array PendingDeposit) : BeaconState :=
  postOf (processSlots (StateTransition := FuluRun) 520) (exitBlockPost queue)

end

end EthCLSpecs.Tests.DepositScenario
