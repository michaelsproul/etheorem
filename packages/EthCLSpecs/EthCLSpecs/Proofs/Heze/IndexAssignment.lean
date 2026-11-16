import EthCLSpecs.Proofs.Heze.IndexAssignment.Slots
import EthCLSpecs.Proofs.Heze.IndexAssignment.Block
import EthCLSpecs.Proofs.Heze.ReachableInvariants
import EthCLSpecs.Proofs.Gloas.IndexAssignment

/-!
# `EthCLSpecs.Proofs.Heze.IndexAssignment`: Heze chains with compatible finality share the index assignment

The Heze counterpart of `Proofs/Gloas/IndexAssignment.lean`. `Proofs/Fulu/IndexAssignment.lean`
states the property, says why `CompatibleFinality` is compatible finality, and outlines the
proof.
`indexAssignment_of_compatibleFinality` is the same theorem over the Heze `BeaconState`: two
chains from one reachable Heze state, with compatible finality, hold the same public key at
every index both have.

## The common state is a Heze state

`ReachableState` for Heze includes the `upgrade` step, so the common state `t` may be a
state the chain reached through the Heze upgrade. `ReachableState (Anchors.only t)` has no
Fulu and no Gloas anchor, so no `upgrade` step fires after `t`. Both chains run under the Heze
rules from `t` on, with the upgrade in the history they share.

With the upgrade after the common state the statement is false. `IndexAssignmentFromFulu`
is the same statement with a Fulu state as `t`, and `not_indexAssignmentFromFulu` reduces its
refutation to one pair of chains. `Tests/HezeValidatorIndexPins.lean` gives the pair.

## What Heze changes in the proof

One rule: a deposit for a new key with BLS credentials adds no validator (EIP-8365).
`depositValid` carries it, so the list argument of `Proofs/DepositQueue.lean` applies as it
is. The rule is the same on both chains from `t` on, which is why it does no harm here and
splits the assignment across the upgrade.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend htr)
open EthCLSpecs.Heze
open EthCLSpecs.Heze.Const (slotsPerEpoch slotsPerEpochLt)
open EthCLSpecs.Proofs.DepositQueue
open scoped EthCLSpecs.Heze.Downgrade EthCLSpecs.Gloas.Downgrade
open IndexAssignment (registryKeys depositValid finalizedSlot DepositProgress Ctx StepInv
  processSlots_progress processBlock_keepsFrame)

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The states reachable from `t` by the `slots` and `block` steps of `ReachableState`, with
each block at slot `d` or later. The constructors carry the premises of the `ReachableState`
ones, so a state reachable from a reachable `t` is reachable (`ReachableFrom.reachable`).

`processBlockHeader` asserts that a block's slot is the state's slot, so the `block` premise
`d ≤ v.slot.toNat` bounds the block's own slot. -/
inductive ReachableFrom (validated : Bool) (nextForkEpoch : Epoch) (t : BeaconState) (d : Nat) :
    BeaconState → Prop where
  | refl : ReachableFrom validated nextForkEpoch t d t
  | slots {v w : BeaconState} (target : Slot) :
      ReachableFrom validated nextForkEpoch t d v →
      target.toNat ≤ forkSlot nextForkEpoch →
      runPure (processSlots (StateTransition := HezeRun) target) v = .ok ((), w) →
      ReachableFrom validated nextForkEpoch t d w
  | block {v w : BeaconState} (signedBlock : SignedBeaconBlock) :
      ReachableFrom validated nextForkEpoch t d v →
      v.slot.toNat < forkSlot nextForkEpoch →
      d ≤ v.slot.toNat →
      (validated = true → verifyBlockSignature (pureState v) signedBlock = true) →
      runPure (processBlock (StateTransition := HezeRun) signedBlock.message) v = .ok ((), w) →
      (validated = true → signedBlock.message.stateRoot = htr w) →
      ReachableFrom validated nextForkEpoch t d w

/-- `w` finalized no block applied after `t`: each block between `t` and `w` sits at slot `d`
or later, and the first slot of the finalized epoch of `w` is below `d`. The block of the
finalized checkpoint is the last block at or before that slot, so it is at or before `t`. -/
def FinalizedBefore (validated : Bool) (nextForkEpoch : Epoch) (t w : BeaconState) : Prop :=
  ∃ d : Nat, ReachableFrom validated nextForkEpoch t d w ∧
    (computeStartSlotAtEpoch w.finalizedCheckpoint.epoch).toNat < d

namespace ReachableFrom

variable {anchors : Anchors} {validated : Bool} {nextForkEpoch : Epoch}

/-- A state reachable from a reachable state is reachable. -/
theorem reachable {t w : BeaconState} {d : Nat}
    (ht : ReachableState anchors validated nextForkEpoch t)
    (h : ReachableFrom validated nextForkEpoch t d w) :
    ReachableState anchors validated nextForkEpoch w := by
  induction h with
  | refl => exact ht
  | slots target _ hw hrun ih => exact .slots target ih hw hrun
  | block sb _ hw _ hsig hrun hroot ih => exact .block sb ih hw hsig hrun hroot

/-- A lower bound on the block slots can only be weakened. At `0` it says nothing. -/
theorem mono {t w : BeaconState} {d d' : Nat} (hle : d' ≤ d)
    (h : ReachableFrom validated nextForkEpoch t d w) :
    ReachableFrom validated nextForkEpoch t d' w := by
  induction h with
  | refl => exact .refl
  | slots target _ hw hrun ih => exact .slots target ih hw hrun
  | block sb _ hw hd hsig hrun hroot ih =>
    exact .block sb ih hw (Nat.le_trans hle hd) hsig hrun hroot

end ReachableFrom

omit [HasherTag] [CryptoBackend] in
/-- The finalized slot in `Nat`: the finalized epoch times `SLOTS_PER_EPOCH`, with no wrap.
`computeStartSlotAtEpoch` multiplies in `uint64`. Under `SimpleStateInvariants` the finalized
epoch is at most the state's epoch, so the product is at most the state's slot. -/
theorem finalizedSlot_toNat {z : BeaconState} (hz : SimpleStateInvariants z) :
    (finalizedSlot z).toNat = z.finalizedCheckpoint.epoch.toNat * slotsPerEpoch := by
  obtain ⟨c1, c2, c3⟩ := hz.checkpointOrder
  have hp := EthCLLib.Proofs.saturatingSub_toNat (computeEpochAtSlot z.slot) 1
  have he := computeEpochAtSlot_toNat z.slot
  simp only [UInt64.le_iff_toNat_le] at c1 c2 c3
  have hle : z.finalizedCheckpoint.epoch.toNat ≤ z.slot.toNat / slotsPerEpoch := by omega
  have hmul : z.finalizedCheckpoint.epoch.toNat * slotsPerEpoch ≤ z.slot.toNat :=
    Nat.le_trans (Nat.mul_le_mul_right _ hle) (Nat.div_mul_le_self _ _)
  have hlt : z.slot.toNat < 2 ^ 64 := z.slot.toNat_lt
  unfold finalizedSlot computeStartSlotAtEpoch
  rw [UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' slotsPerEpochLt]
  exact Nat.mod_eq_of_lt (by omega)

variable {anchors : Anchors} {validated : Bool} {nextForkEpoch : Epoch}

/-- A chain whose blocks after `t` sit at slot `d` or later, and whose finalized slot is below
`d`, stays on the queue of `t`: its keys are the keys of `t` moved by a prefix of that queue.

The conclusion is conditional on the finalized slot of the end state, and the induction runs
on the conditional. A step from `x` to `z` takes the bound at `z` back to `x`, because the
finalized slot does not fall. A `slots` step then applies `OnQueue.scan`: each consumed
deposit has a slot at or below the finalized slot, below `d`, so it is no deposit of a later
block. A `block` step applies `OnQueue.append`: each appended deposit names a held key, or
carries the block's slot, which is `d` or later. -/
theorem ReachableFrom.onQueue (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ u, anchors.heze u → SimpleStateInvariants u)
    {t w : BeaconState} {d : Nat} (ht : ReachableState anchors validated nextForkEpoch t)
    (h : ReachableFrom validated nextForkEpoch t d w) :
    (finalizedSlot w).toNat < d →
    OnQueue (fun e : PendingDeposit => e.pubkey) depositValid (registryKeys t).toList
      t.pendingDeposits.val.toList (fun e => d ≤ e.slot.toNat)
      (registryKeys w).toList w.pendingDeposits.val.toList := by
  induction h with
  | refl => exact fun _ => OnQueue.start _ _ _ _ _
  | slots target hv _ hrun ih =>
    have hinv := (hv.reachable ht).simpleStateInvariants hF hG hH
    refine (processSlots_progress
      (fun x => (finalizedSlot x).toNat < d →
        OnQueue (fun e : PendingDeposit => e.pubkey) depositValid (registryKeys t).toList
          t.pendingDeposits.val.toList (fun e => d ≤ e.slot.toNat)
          (registryKeys x).toList x.pendingDeposits.val.toList)
      ?_ target _ hinv ih).runPure_ok hrun
    intro x z hx hz hprog hPx hzfin
    obtain ⟨hep, hscan⟩ := hprog.deposits
    have hxfin : (finalizedSlot x).toNat < d := by
      rw [finalizedSlot_toNat hx]
      rw [finalizedSlot_toNat hz] at hzfin
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp hep)) hzfin
    exact (hPx hxfin).scan _ _ hscan fun e hfe hadm => by
      have := UInt64.le_iff_toNat_le.mp hfe
      omega
  | @block v w sb hv _ hd _ hrun _ ih =>
    intro hfin
    have hinv := (hv.reachable ht).simpleStateInvariants hF hG hH
    have hst := (processBlock_keepsFrame sb.message (Ctx.of v true) rfl v
      (StepInv.start v true hinv.registrySizes)).runPure_ok hrun
    obtain ⟨-, hf, hk, ⟨extra, hq, hadm⟩, -⟩ := hst
    simp only [Ctx.of] at hf hk hq hadm
    have hfv : (finalizedSlot v).toNat < d := by
      unfold finalizedSlot at hfin ⊢
      rw [← hf]
      exact hfin
    rw [hk, hq, Array.toList_append]
    refine (ih hfv).append _ _ fun e he => ?_
    rcases (hadm e (Array.mem_toList_iff.mp he)).2 with h | h
    · exact Or.inl (Array.mem_toList_iff.mpr h)
    · exact Or.inr (by rw [h]; exact hd)

/-- Any chain from `t` tracks the queue of `t`: it is still on that queue, or its keys extend
the keys of the whole queue. No hypothesis on finality or on the block slots is needed. -/
theorem ReachableFrom.tracks (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ u, anchors.heze u → SimpleStateInvariants u)
    {t w : BeaconState} {d : Nat} (ht : ReachableState anchors validated nextForkEpoch t)
    (h : ReachableFrom validated nextForkEpoch t d w) :
    Tracks (fun e : PendingDeposit => e.pubkey) depositValid (registryKeys t).toList
      t.pendingDeposits.val.toList (registryKeys w).toList w.pendingDeposits.val.toList := by
  induction h with
  | refl => exact Tracks.start _ _ _ _
  | slots target hv _ hrun ih =>
    have hinv := (hv.reachable ht).simpleStateInvariants hF hG hH
    refine (processSlots_progress
      (fun x => Tracks (fun e : PendingDeposit => e.pubkey) depositValid (registryKeys t).toList
        t.pendingDeposits.val.toList (registryKeys x).toList x.pendingDeposits.val.toList)
      ?_ target _ hinv ih).runPure_ok hrun
    intro x z _ _ hprog hPx
    exact hPx.scan _ _ hprog.deposits.2
  | @block v w sb hv _ _ _ hrun _ ih =>
    have hinv := (hv.reachable ht).simpleStateInvariants hF hG hH
    have hst := (processBlock_keepsFrame sb.message (Ctx.of v true) rfl v
      (StepInv.start v true hinv.registrySizes)).runPure_ok hrun
    obtain ⟨-, -, hk, ⟨extra, hq, -⟩, -⟩ := hst
    simp only [Ctx.of] at hk hq
    rw [hk, hq, Array.toList_append]
    exact ih.append _ _ _

/-- The one-sided form of the theorem: `w'` finalized no block after `t`, with the bound `d`
named, and `w''` is any state reachable from `t`. -/
theorem validators_pubkey_eq_of_reachableFrom
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ u, anchors.heze u → SimpleStateInvariants u)
    {t w' w'' : BeaconState} {d : Nat}
    (ht : ReachableState anchors validated nextForkEpoch t)
    (h' : ReachableFrom validated nextForkEpoch t d w')
    (hfin : (computeStartSlotAtEpoch w'.finalizedCheckpoint.epoch).toNat < d)
    (h'' : ReachableFrom validated nextForkEpoch t 0 w'')
    (i : Nat) (hi' : i < w'.validators.val.size) (hi'' : i < w''.validators.val.size) :
    w'.validators.val[i].pubkey = w''.validators.val[i].pubkey := by
  have hcmp := comparable _ _ (h'.onQueue hF hG hH ht hfin) (h''.tracks hF hG hH ht)
  -- `registryKeys w` is `w.validators.val.map (·.pubkey)`, so its list has the registry's
  -- length and its entry `i` is the key of validator `i`.
  have h1 : i < (registryKeys w').toList.length := by simpa [registryKeys] using hi'
  have h2 : i < (registryKeys w'').toList.length := by simpa [registryKeys] using hi''
  have := getElem_eq_of_comparable hcmp i h1 h2
  simpa [registryKeys] using this

/-- The theorem in the working forms of the proof.

* `w'` and `w''` are reachable from `t` in the path relation.
* One of the two finalized no block applied after `t` (`FinalizedBefore`).

Then validator `i` has one public key in both registries, for every `i` both hold.
`indexAssignment_of_compatibleFinality` is the statement over `ReachableState`. -/
theorem validators_pubkey_eq_of_finalizedBefore
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ u, anchors.heze u → SimpleStateInvariants u)
    {t w' w'' : BeaconState}
    (ht : ReachableState anchors validated nextForkEpoch t)
    (h' : ReachableFrom validated nextForkEpoch t 0 w')
    (h'' : ReachableFrom validated nextForkEpoch t 0 w'')
    (hcompat : FinalizedBefore validated nextForkEpoch t w' ∨
      FinalizedBefore validated nextForkEpoch t w'')
    (i : Nat) (hi' : i < w'.validators.val.size) (hi'' : i < w''.validators.val.size) :
    w'.validators.val[i].pubkey = w''.validators.val[i].pubkey := by
  rcases hcompat with ⟨d, hd, hfin⟩ | ⟨d, hd, hfin⟩
  · exact validators_pubkey_eq_of_reachableFrom hF hG hH ht hd hfin h'' i hi' hi''
  · exact (validators_pubkey_eq_of_reachableFrom hF hG hH ht hd hfin h' i hi'' hi').symm

/-- Along one chain the assignment never changes: a state reachable from `t` holds the key of
`t` at every index of `t`. `t` finalized no block after itself, so the theorem applies with
`t` as the first chain. -/
theorem validators_pubkey_eq_of_descendant
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ u, anchors.heze u → SimpleStateInvariants u)
    {t w : BeaconState} (ht : ReachableState anchors validated nextForkEpoch t)
    (h : ReachableFrom validated nextForkEpoch t 0 w)
    (i : Nat) (hi : i < t.validators.val.size) (hi' : i < w.validators.val.size) :
    t.validators.val[i].pubkey = w.validators.val[i].pubkey :=
  validators_pubkey_eq_of_finalizedBefore hF hG hH ht .refl h
    (Or.inl ⟨_, .refl, Nat.lt_succ_self _⟩) i hi hi'

/-! ## The statement over `ReachableState`

The theorem above names the path relation `ReachableFrom`. The statement below needs no new
relation. "Reachable from `t`" is `ReachableState` with the one anchor `t`, and "compatible
finality" is a predicate on the two states and the slot of `t`. -/

/-- No state is reachable from an anchor set that holds no state of any fork. -/
theorem ReachableState.false_of_no_anchor {anchors : Anchors} (hF : ∀ u, ¬ anchors.fulu u)
    (hG : ∀ u, ¬ anchors.gloas u) (hH : ∀ u, ¬ anchors.heze u) {v : BeaconState}
    (h : ReachableState anchors validated nextForkEpoch v) : False := by
  induction h with
  | anchor ha _ => exact hH _ ha
  | upgrade hu _ _ _ => exact EthCLSpecs.Proofs.Gloas.ReachableState.false_of_no_anchor hF hG hu
  | slots _ _ _ _ ih => exact ih
  | block _ _ _ _ _ _ ih => exact ih

/-- The anchor set that holds the one Heze state `t` and no Fulu or Gloas state. Every state
reachable from it descends from `t` by `slots` and `block` steps: with no earlier anchor, no
`upgrade` step can fire. So `ReachableState (Anchors.only t)` reads "reachable from `t`". -/
def Anchors.only (t : BeaconState) : Anchors :=
  { fulu := fun _ => False, gloas := fun _ => False, heze := (· = t) }

/-- `w` has finalized no slot at or after `σ`: the first slot of its finalized epoch is below
`σ`. -/
def FinalizedBelow (σ : Slot) (w : BeaconState) : Prop :=
  (computeStartSlotAtEpoch w.finalizedCheckpoint.epoch).toNat < σ.toNat

/-- Compatible finality of two states that descend from a common state at slot `σ`: one of
the two has finalized no slot at or after `σ`. Its finalized checkpoint block is then a block
of the common history, so it lies on the other chain too. -/
def CompatibleFinality (σ : Slot) (w' w'' : BeaconState) : Prop :=
  FinalizedBelow σ w' ∨ FinalizedBelow σ w''

/-- A state reachable from the one anchor `t` is reachable from `t` in the path relation. -/
theorem ReachableFrom.of_only {t w : BeaconState}
    (h : ReachableState (Anchors.only t) validated nextForkEpoch w) :
    ReachableFrom validated nextForkEpoch t 0 w := by
  induction h with
  | anchor ha _ => exact ha ▸ .refl
  | upgrade hu _ _ _ =>
    exact (EthCLSpecs.Proofs.Gloas.ReachableState.false_of_no_anchor (fun _ h => h)
      (fun _ h => h) hu).elim
  | slots target _ hw hrun ih => exact .slots target ih hw hrun
  | block sb _ hw hsig hrun hroot ih => exact .block sb ih hw (Nat.zero_le _) hsig hrun hroot

/-- Slots only grow along a chain from `t`. -/
theorem ReachableFrom.slot_le (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ u, anchors.heze u → SimpleStateInvariants u)
    {t w : BeaconState} {d : Nat} (ht : ReachableState anchors validated nextForkEpoch t)
    (h : ReachableFrom validated nextForkEpoch t d w) : t.slot ≤ w.slot := by
  induction h with
  | refl => exact UInt64.le_refl _
  | slots target hv _ hrun ih =>
    have hinv := (hv.reachable ht).simpleStateInvariants hF hG hH
    obtain ⟨hs, hlt, _⟩ := (processSlots_ensures target _ hinv).runPure_ok hrun
    exact UInt64.le_trans ih (hs ▸ UInt64.le_of_lt hlt)
  | block sb hv _ _ _ hrun _ ih =>
    have hinv := (hv.reachable ht).simpleStateInvariants hF hG hH
    rw [((processBlock_ensures _ _ hinv).runPure_ok hrun).1]
    exact ih

/-- Each block of a chain from `t` sits at the slot of `t` or later, so the bound `0` on the
block slots rises to that slot. -/
theorem ReachableFrom.raise (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ u, anchors.heze u → SimpleStateInvariants u)
    {t w : BeaconState} (ht : ReachableState anchors validated nextForkEpoch t)
    (h : ReachableFrom validated nextForkEpoch t 0 w) :
    ReachableFrom validated nextForkEpoch t t.slot.toNat w := by
  induction h with
  | refl => exact .refl
  | slots target _ hw hrun ih => exact .slots target ih hw hrun
  | block sb hv hw _ hsig hrun hroot ih =>
    exact .block sb ih hw (UInt64.le_iff_toNat_le.mp (hv.slot_le hF hG hH ht)) hsig hrun hroot

/-- Two Heze chains with compatible finality hold the same public key at every validator index
both have.

* `t` is a reachable Heze state, and the Fulu, Gloas and Heze anchors satisfy their fork's
  `SimpleStateInvariants`.
* `w'` and `w''` are reachable from `t`: `ReachableState` with the one anchor `t`.
* The finality of the two is compatible at the slot of `t`: one of them has finalized no slot
  at or after it. The module docstring says why that is compatible finality.

Then validator `i` has one public key in both registries, for every `i` both hold. The proof
rests on Lean's three standard axioms and on no hash or signature assumption. -/
theorem indexAssignment_of_compatibleFinality
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → EthCLSpecs.Proofs.Gloas.SimpleStateInvariants u)
    (hH : ∀ u, anchors.heze u → SimpleStateInvariants u)
    {t w' w'' : BeaconState}
    (ht : ReachableState anchors validated nextForkEpoch t)
    (h' : ReachableState (Anchors.only t) validated nextForkEpoch w')
    (h'' : ReachableState (Anchors.only t) validated nextForkEpoch w'')
    (hc : CompatibleFinality t.slot w' w'')
    (i : Nat) (hi' : i < w'.validators.val.size) (hi'' : i < w''.validators.val.size) :
    w'.validators.val[i].pubkey = w''.validators.val[i].pubkey := by
  have f' := ReachableFrom.of_only h'
  have f'' := ReachableFrom.of_only h''
  refine validators_pubkey_eq_of_finalizedBefore hF hG hH ht f' f'' ?_ i hi' hi''
  rcases hc with hc | hc
  · exact Or.inl ⟨_, f'.raise hF hG hH ht, hc⟩
  · exact Or.inr ⟨_, f''.raise hF hG hH ht, hc⟩

end

end EthCLSpecs.Proofs.Heze

/-! ## Across the upgrade

`indexAssignment_of_compatibleFinality` takes a Heze state as the common state `t`.
`IndexAssignmentFromFulu` is the same statement with a Fulu state as `t`, so each chain passes
the Gloas and Heze upgrades on its own. That statement is false.
`not_indexAssignmentFromFulu` reduces its refutation to one pair of chains, and
`Tests/HezeValidatorIndexPins.lean` gives the pair. -/

namespace EthCLSpecs.Proofs.Heze

open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Heze (Preset Config BeaconState)
open EthCLSpecs.Heze.Const (farFutureEpoch)
open scoped EthCLSpecs.Heze.Downgrade EthCLSpecs.Gloas.Downgrade

section AcrossUpgrade

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-- The anchor set that holds one Fulu state and no Gloas or Heze state. Every state reachable
from this set descends from `u`, so `ReachableState (Anchors.onlyFulu u)` reads "reachable
from `u`", through both upgrades. -/
def Anchors.onlyFulu (u : EthCLSpecs.Fulu.BeaconState) : Anchors :=
  { fulu := (· = u), gloas := fun _ => False, heze := fun _ => False }

/-- The index-assignment property with a Fulu common state: for a reachable Fulu state `t`,
two Heze states reachable from `t`, and compatible finality at the slot of `t`, validator `i`
has one public key in both states. The hypotheses are those of
`indexAssignment_of_compatibleFinality`, at `validated = true`, with the upgrades after `t`. -/
def IndexAssignmentFromFulu : Prop :=
  ∀ (anchors : EthCLSpecs.Proofs.Fulu.Anchors) (t : EthCLSpecs.Fulu.BeaconState)
    (w' w'' : BeaconState),
    (∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u) →
    EthCLSpecs.Proofs.Fulu.ReachableState anchors true EthCLSpecs.Gloas.Const.gloasForkEpoch t →
    ReachableState (Anchors.onlyFulu t) true farFutureEpoch w' →
    ReachableState (Anchors.onlyFulu t) true farFutureEpoch w'' →
    CompatibleFinality t.slot w' w'' →
    ∀ (i : Nat) (h' : i < w'.validators.val.size) (h'' : i < w''.validators.val.size),
      w'.validators.val[i].pubkey = w''.validators.val[i].pubkey

/-- One pair of chains refutes `IndexAssignmentFromFulu`: a reachable Fulu state, two Heze
states reachable from it with compatible finality, and one index with two keys. -/
theorem not_indexAssignmentFromFulu {anchors : EthCLSpecs.Proofs.Fulu.Anchors}
    {t : EthCLSpecs.Fulu.BeaconState} {w' w'' : BeaconState}
    (hA : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (ht : EthCLSpecs.Proofs.Fulu.ReachableState anchors true
      EthCLSpecs.Gloas.Const.gloasForkEpoch t)
    (h' : ReachableState (Anchors.onlyFulu t) true farFutureEpoch w')
    (h'' : ReachableState (Anchors.onlyFulu t) true farFutureEpoch w'')
    (hc : CompatibleFinality t.slot w' w'')
    {i : Nat} (hi' : i < w'.validators.val.size) (hi'' : i < w''.validators.val.size)
    (hne : w'.validators.val[i].pubkey ≠ w''.validators.val[i].pubkey) :
    ¬ IndexAssignmentFromFulu :=
  fun h => hne (h anchors t w' w'' hA ht h' h'' hc i hi' hi'')

end AcrossUpgrade

end EthCLSpecs.Proofs.Heze
