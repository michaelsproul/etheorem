import EthCLSpecs.Proofs.Gloas.IndexAssignment
import EthCLSpecs.Proofs.Gloas.IndexAssignment.Onboarding
import EthCLSpecs.Proofs.Gloas.FinalizedValidators

/-!
# `EthCLSpecs.Proofs.Gloas.IndexAssignmentFromFulu`: the index assignment across the Gloas upgrade

`indexAssignment_fromFulu` proves the index-assignment property for two Gloas chains that
share a Fulu state. With compatible finality, the two chains hold the same public key at
every validator index both have. Each chain passes the Gloas upgrade on its own.
`indexAssignmentFromFulu` is the same fact, as a proof of the statement
`IndexAssignmentFromFulu` (`Proofs/Gloas/IndexAssignment.lean`).

`Proofs/Fulu/IndexAssignment.lean` states the property and says why `CompatibleFinality` is
compatible finality. The in-fork theorems cover two Fulu chains, and two Gloas chains with the
upgrade in the history they share. This module covers the case between them.

## The spec this proof is about

The Fulu to Gloas upgrade is the upgrade of the consensus-specs branch
`dapplion:gloas-onboard-cutoff`: `onboardBuildersFromPendingDeposits`
(`Gloas/Operations.lean`) and `upgradeToGloas` (`Gloas/Upgrade.lean`) follow that branch. It
is not the upgrade of the pinned release v1.7.0-beta.4, and `DISCREPANCIES.md` records the
deviation. At the pinned release the property is false (`SPECS_ARCHITECTURE.md` §11.6).

## The fact about the upgrade

The in-fork theorems rest on one list argument (`Proofs/DepositQueue.lean`): each chain
consumes the queue of the common state from the front, so the two key lists are prefixes of
one list. The builder onboarding takes deposits out of the middle of the queue, which the
argument does not allow. The onboarding cutoff restores it. Two facts meet at the first slot
of epoch `GLOAS_FORK_EPOCH - 2`, the cutoff.

* **No Fulu scan consumes a deposit above the cutoff.** A scan consumes a deposit whose slot is
  at or below the first slot of the finalized epoch. An epoch transition leaves a finalized
  epoch at or below the epoch before the one that ends (`SlotProgress.finalized`,
  `Proofs/Fulu/IndexAssignment/Slots.lean`). The last Fulu transition ends epoch
  `GLOAS_FORK_EPOCH - 1`.
* **The onboarding takes no deposit at or below the cutoff.** It takes `Onboardable` deposits
  alone, and each has a slot above the cutoff
  (`onboardBuildersFromPendingDeposits_ensures`, `Proofs/Gloas/IndexAssignment/Onboarding.lean`).

So a deposit that one chain applied before the fork is in the queue of every other chain
after the fork, as a validator deposit.

## One reading of the queue for both forks

The proof reads the queue of each state through a filter.

* `queueAtFork x`, for a Fulu state `x`: the queue, copied to the Gloas deposit type, with the
  deposits `StaysValidAtFork` keeps. Those have a valid signature and are not `Onboardable`.
* `validQueue w`, for a Gloas state `w`: the deposits of the queue with a valid signature.

A deposit with an invalid signature adds no validator, so a queue and its filtered form give
one key list (`DepositQueue.keysAfter_filter`). The onboarding keeps some of those deposits
and drops others, by rules that read the registry and the deposits it kept before. The filter
removes them from the argument, and with them every fact about the builder registry.

Three steps relate the readings.

* A Fulu scan is a scan of `queueAtFork` (`Scan.map`, then `Scan.filter`). The filter drops no
  consumed deposit with a valid signature, by the first fact above.
* The upgrade maps one reading to the other: `validQueue` of the upgraded state is
  `queueAtFork` of the Fulu state (`gloasChain_upgrade`). The cutoff the step computes is
  `forkCutoff`, because the upgrade runs at the fork slot (`onboardingCutoff_toNat`).
* A Gloas scan is a scan of `validQueue`.

## The induction

`DepositQueue.Chain` packs the two facts of the list argument for one state: the chain is on
the queue of the common state while it has finalized no slot at or after that state, and it
tracks that queue in any case. `FuluChain R Q d x` and `GloasChain R Q d w` are `Chain` at
the keys `R`, the queue `Q` and the slot `d` of a start, for a Fulu state and a Gloas state.
For the common state `t` of this module the three values are its keys, `queueAtFork t` and
its slot.

* `fuluChain_of_reachable`: each Fulu state reachable from anchors on the chain, before the
  fork.
* `gloasChain_upgrade`: the upgrade takes `FuluChain` to `GloasChain`.
* `gloasChain_of_reachable`: each Gloas state reachable from anchors on the chain.

`Chain.comparable` then gives two key lists of which one is a prefix of the other.

## The two forks' deposits

Fulu and Gloas each declare `PendingDeposit`, and `upgradeToGloas` copies the queue one deposit
at a time. `upgradeDeposit` is that copy. It keeps the key, the slot and the validity of a
deposit. The validity fact, `depositValid_upgradeDeposit`, closes by `rfl`: the Gloas
`isValidDepositSignature` is the replayed Fulu body, and under the `Downgrade` bridge the two
unfold to one term.

The proof rests on Lean's three standard axioms and on no hash or signature assumption.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend saturatingSub)
open EthCLSpecs.Gloas
open EthCLSpecs.Gloas.Const (slotsPerEpoch slotsPerEpochPos slotsPerEpochLt gloasForkEpoch
  gloasForkVersion farFutureEpoch)
open EthCLSpecs.Proofs.DepositQueue
open scoped EthCLSpecs.Gloas.Downgrade
open IndexAssignment (registryKeys depositValid finalizedSlot Ctx StepInv SlotProgress
  processSlots_progress processBlock_keepsFrame Onboardable StaysValid onboardingCutoff
  completeUpgradeToGloas_ensures)

section

variable [Preset] [HasherTag] [Config] [CryptoBackend]

/-! ## The queue across the upgrade -/

/-- The copy `upgradeToGloas` makes of one queued deposit: each field of the Fulu deposit, in
the Gloas container. `upgradeToGloas` names a private converter with this body, so the proof
states its own. -/
def upgradeDeposit (e : EthCLSpecs.Fulu.PendingDeposit) : PendingDeposit :=
  { pubkey := e.pubkey, withdrawalCredentials := e.withdrawalCredentials, amount := e.amount,
    signature := e.signature, slot := e.slot }

omit [Config] [CryptoBackend] in
/-- The queue of the upgraded state is the Fulu queue, copied by `upgradeDeposit`. The private
converter of `Gloas/Upgrade.lean` unfolds to `upgradeDeposit`, so the proof is `rfl`. -/
theorem upgradeToGloas_pendingDeposits (fv : Version) (u : EthCLSpecs.Fulu.BeaconState) :
    (upgradeToGloas fv u).pendingDeposits.val = u.pendingDeposits.val.map upgradeDeposit := rfl

/-- The copy keeps the validity of a deposit. Gloas inherits `isValidDepositSignature`, so its
body is the Fulu body over the Gloas `DepositMessage`. The two containers have one SSZ
layout, and the Fulu constants come from the Gloas ones through the `Downgrade` bridge, so
both sides reduce to one `blsVerify` call and the proof is `rfl`. -/
theorem depositValid_upgradeDeposit (e : EthCLSpecs.Fulu.PendingDeposit) :
    depositValid (upgradeDeposit e) = EthCLSpecs.Proofs.Fulu.IndexAssignment.depositValid e :=
  rfl

/-- The onboarding cutoff of the fork, in `Nat`: the first slot of epoch
`GLOAS_FORK_EPOCH - 2`, and slot `0` when the fork epoch is below two. The product is in
`Nat`, so it does not wrap for a fork epoch no chain reaches. -/
def forkCutoff : Nat := (gloasForkEpoch.toNat - 2) * slotsPerEpoch

/-- A deposit with a valid signature that the onboarding at the fork leaves queued: it has no
builder withdrawal credentials, or its slot is at or below `forkCutoff`. This is
`StaysValid` at the cutoff of the fork slot (`staysValid_eq_atFork`). -/
def StaysValidAtFork (d : PendingDeposit) : Bool :=
  depositValid d &&
    !(isBuilderWithdrawalCredential d.withdrawalCredentials && decide (forkCutoff < d.slot.toNat))

/-- The queue of a Fulu state as the proof reads it: copied to the Gloas deposit type, with
the deposits `StaysValidAtFork` keeps. These are the deposits with a valid signature that the
upgrade leaves in the queue. -/
def queueAtFork (x : EthCLSpecs.Fulu.BeaconState) : List PendingDeposit :=
  (x.pendingDeposits.val.toList.map upgradeDeposit).filter StaysValidAtFork

/-- The queue of a Gloas state as the proof reads it: the deposits with a valid
signature. -/
def validQueue (w : BeaconState) : List PendingDeposit :=
  w.pendingDeposits.val.toList.filter depositValid

/-- The Fulu state `x` is on a chain that started at keys `R` and queue `Q`, at slot `d`:
`DepositQueue.Chain`, read at the finalized slot, the slot, the keys and `queueAtFork` of `x`.
The start is a Fulu state with keys `R` and `queueAtFork` equal to `Q`. The predicate names
the three values and no state, so two starts with one key list and one queue share it. -/
def FuluChain (R : List BLSPubkey) (Q : List PendingDeposit) (d : Nat)
    (x : EthCLSpecs.Fulu.BeaconState) : Prop :=
  Chain (fun e : PendingDeposit => e.pubkey) depositValid (fun e => e.slot.toNat) R Q d
    (EthCLSpecs.Proofs.Fulu.IndexAssignment.finalizedSlot x).toNat x.slot.toNat
    (EthCLSpecs.Proofs.Fulu.IndexAssignment.registryKeys x).toList (queueAtFork x)

/-- The Gloas state `w` is on a chain that started at keys `R` and queue `Q`, at slot `d`: the
same `Chain` as `FuluChain`, read at the finalized slot, the slot, the keys and `validQueue`
of `w`. The start is a Fulu state, as for `FuluChain`, or a Gloas state with keys `R` and
`validQueue` equal to `Q`. -/
def GloasChain (R : List BLSPubkey) (Q : List PendingDeposit) (d : Nat) (w : BeaconState) :
    Prop :=
  Chain (fun e : PendingDeposit => e.pubkey) depositValid (fun e => e.slot.toNat) R Q d
    (finalizedSlot w).toNat w.slot.toNat (registryKeys w).toList (validQueue w)

/-! ## The Fulu steps -/

/-- One Fulu slot before the fork keeps the chain. The scan of the slot is a scan of
`queueAtFork`: each consumed deposit has a slot at or below the finalized slot of `z`, which
is at or below `forkCutoff`, so `StaysValidAtFork` drops no consumed deposit with a valid
signature. -/
theorem fuluChain_slot {R : List BLSPubkey} {Q : List PendingDeposit} {d : Nat}
    {x z : EthCLSpecs.Fulu.BeaconState}
    (hx : EthCLSpecs.Proofs.Fulu.SimpleStateInvariants x)
    (hz : EthCLSpecs.Proofs.Fulu.SimpleStateInvariants z)
    (hprog : EthCLSpecs.Proofs.Fulu.IndexAssignment.SlotProgress x z)
    (hle : z.slot.toNat ≤ EthCLSpecs.Proofs.Fulu.forkSlot gloasForkEpoch)
    (h : FuluChain R Q d x) : FuluChain R Q d z := by
  obtain ⟨hep, hscan⟩ := hprog.deposits
  have hfx := EthCLSpecs.Proofs.Fulu.finalizedSlot_toNat hx
  have hfz := EthCLSpecs.Proofs.Fulu.finalizedSlot_toNat hz
  have hspe : EthCLSpecs.Fulu.Const.slotsPerEpoch = slotsPerEpoch := rfl
  rw [hspe] at hfx hfz
  -- The finalized epoch of `z` is at most `GLOAS_FORK_EPOCH - 2`: it is at most the epoch
  -- before the epoch of `x`, and `x` sits below the fork slot.
  have hb : z.finalizedCheckpoint.epoch.toNat ≤ gloasForkEpoch.toNat - 2 := by
    have h1 := UInt64.le_iff_toNat_le.mp hprog.finalized
    rw [EthCLLib.Proofs.saturatingSub_toNat, EthCLSpecs.Proofs.Fulu.computeEpochAtSlot_toNat,
      hspe] at h1
    have hs := hprog.slot
    have hlt : x.slot.toNat < gloasForkEpoch.toNat * slotsPerEpoch := by
      have hle' : z.slot.toNat ≤ gloasForkEpoch.toNat * slotsPerEpoch := hle
      omega
    have hdiv : x.slot.toNat / slotsPerEpoch < gloasForkEpoch.toNat :=
      Nat.div_lt_of_lt_mul (Nat.mul_comm _ _ ▸ hlt)
    have h1' : (1 : UInt64).toNat = 1 := rfl
    omega
  have hcut : (EthCLSpecs.Proofs.Fulu.IndexAssignment.finalizedSlot z).toNat ≤ forkCutoff := by
    rw [hfz]
    exact Nat.mul_le_mul_right _ hb
  -- The scan, read at the Gloas deposit type and then through the fork filter.
  have hscan' := (hscan.map _ _ (fun e : PendingDeposit => e.pubkey) depositValid upgradeDeposit
    (fin' := fun e => e.slot ≤ EthCLSpecs.Proofs.Fulu.IndexAssignment.finalizedSlot z)
    (fun _ => rfl) depositValid_upgradeDeposit (fun _ he => he)).filter _ _ StaysValidAtFork
    (fun e he hv => by
      have hes : e.slot.toNat ≤ forkCutoff := Nat.le_trans (UInt64.le_iff_toNat_le.mp he) hcut
      have hnot : ¬ forkCutoff < e.slot.toNat := Nat.not_lt.mpr hes
      simp [StaysValidAtFork, hv, hnot])
  exact h.scan _ _ hscan'
    (by rw [hfx, hfz]; exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp hep))
    (by have := hprog.slot; omega) (fun _ he => UInt64.le_iff_toNat_le.mp he)

/-- One Fulu block keeps the chain. The block keeps the slot, the finalized epoch and the keys,
and it appends deposits that name a held key or carry the block's slot. `upgradeDeposit`
copies the key and the slot, so the appended part of `queueAtFork` has the same property. -/
theorem fuluChain_block {R : List BLSPubkey} {Q : List PendingDeposit} {d : Nat}
    {v w : EthCLSpecs.Fulu.BeaconState}
    (hinv : EthCLSpecs.Proofs.Fulu.SimpleStateInvariants v)
    (block : EthCLSpecs.Fulu.BeaconBlock)
    (hrun : runPure (EthCLSpecs.Fulu.processBlock
      (StateTransition := EthCLSpecs.Proofs.Fulu.FuluRun) block) v = .ok ((), w))
    (h : FuluChain R Q d v) : FuluChain R Q d w := by
  have hst := (EthCLSpecs.Proofs.Fulu.IndexAssignment.processBlock_keepsFrame block
    (EthCLSpecs.Proofs.Fulu.IndexAssignment.Ctx.of v true) rfl v
    (EthCLSpecs.Proofs.Fulu.IndexAssignment.StepInv.start v true hinv.registrySizes)).runPure_ok
      hrun
  obtain ⟨hs, hf, hk, ⟨extra, hq, hadm⟩, -⟩ := hst
  simp only [EthCLSpecs.Proofs.Fulu.IndexAssignment.Ctx.of] at hs hf hk hq hadm
  have e1 : (EthCLSpecs.Proofs.Fulu.IndexAssignment.finalizedSlot w).toNat
      = (EthCLSpecs.Proofs.Fulu.IndexAssignment.finalizedSlot v).toNat := by
    unfold EthCLSpecs.Proofs.Fulu.IndexAssignment.finalizedSlot
    rw [hf]
  have e4 : queueAtFork w
      = queueAtFork v ++ (extra.toList.map upgradeDeposit).filter StaysValidAtFork := by
    unfold queueAtFork
    rw [hq, Array.toList_append, List.map_append, List.filter_append]
  unfold FuluChain
  rw [e1, hs, hk, e4]
  refine Chain.append _ _ h fun e he => ?_
  obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp (List.mem_filter.mp he).1
  rcases (hadm e₀ (Array.mem_toList_iff.mp he₀)).2 with h1 | h1
  · exact Or.inl (Array.mem_toList_iff.mpr h1)
  · refine Or.inr ?_
    show v.slot.toNat ≤ e₀.slot.toNat
    rw [h1]
    exact Nat.le_refl _

variable {validated : Bool} {nextForkEpoch : Epoch}

/-- Every Fulu state reachable before the Gloas fork is on the chain, when each anchor is. The
`slots` case carries the chain through `processSlots_progress`, under the hypothesis that the
slot is at or below the fork slot: each state of the loop is, because the target is. -/
theorem fuluChain_of_reachable {anchors : EthCLSpecs.Proofs.Fulu.Anchors}
    {R : List BLSPubkey} {Q : List PendingDeposit} {d : Nat} {x : EthCLSpecs.Fulu.BeaconState}
    (hA : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (h0 : ∀ u, anchors.fulu u → FuluChain R Q d u)
    (h : EthCLSpecs.Proofs.Fulu.ReachableState anchors validated gloasForkEpoch x) :
    FuluChain R Q d x := by
  induction h with
  | anchor ha _ => exact h0 _ ha
  | slots target hv hw hrun ih =>
    have hinv := EthCLSpecs.Proofs.Fulu.ReachableState.simpleStateInvariants hA hv
    have hP := (EthCLSpecs.Proofs.Fulu.IndexAssignment.processSlots_progress
      (fun x => x.slot.toNat ≤ EthCLSpecs.Proofs.Fulu.forkSlot gloasForkEpoch →
        FuluChain R Q d x)
      (fun x z hx hz hprog hPx hzle =>
        fuluChain_slot hx hz hprog hzle (hPx (by have := hprog.slot; omega)))
      target _ hinv (fun _ => ih)).runPure_ok hrun
    have hslot := ((EthCLSpecs.Proofs.Fulu.processSlots_ensures target _ hinv).runPure_ok hrun).1
    exact hP (by rw [hslot]; exact hw)
  | @block v w sb hv _ _ hrun _ ih =>
    exact fuluChain_block (EthCLSpecs.Proofs.Fulu.ReachableState.simpleStateInvariants hA hv)
      sb.message hrun ih

/-! ## The upgrade -/

omit [Preset] [HasherTag] [Config] [CryptoBackend] in
/-- The cutoff arithmetic in `uint64`: `max(e, 2) - 2` is `e - 2`, floored at zero. -/
theorem max_two_sub_two_toNat (e : UInt64) : (max e 2 - 2).toNat = e.toNat - 2 := by
  have h2 : (2 : UInt64).toNat = 2 := rfl
  have hmax : max e 2 = if e ≤ 2 then 2 else e := rfl
  rw [hmax]
  split
  · rename_i hle
    have := UInt64.le_iff_toNat_le.mp hle
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_refl _)]
    omega
  · rename_i hle
    have hle' : (2 : UInt64) ≤ e := UInt64.le_of_lt (UInt64.not_le.mp hle)
    rw [UInt64.toNat_sub_of_le _ _ hle', h2]

omit [HasherTag] [CryptoBackend] in
/-- At the fork slot the cutoff the onboarding computes is `forkCutoff`. The epoch of the fork
slot is `GLOAS_FORK_EPOCH`, and the product does not wrap: it is at most the fork slot, which
is a slot of a state. -/
theorem onboardingCutoff_toNat {v : BeaconState}
    (htrig : v.slot.toNat = forkSlot gloasForkEpoch) :
    (onboardingCutoff v).toNat = forkCutoff := by
  have htrig' : v.slot.toNat = gloasForkEpoch.toNat * slotsPerEpoch := htrig
  have hlt : v.slot.toNat < 2 ^ 64 := v.slot.toNat_lt
  have hepoch : (computeEpochAtSlot v.slot).toNat = gloasForkEpoch.toNat := by
    rw [computeEpochAtSlot_toNat, htrig']
    exact Nat.mul_div_cancel _ slotsPerEpochPos
  have hle : (gloasForkEpoch.toNat - 2) * slotsPerEpoch ≤ gloasForkEpoch.toNat * slotsPerEpoch :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  unfold onboardingCutoff computeStartSlotAtEpoch forkCutoff
  rw [UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' slotsPerEpochLt, max_two_sub_two_toNat, hepoch]
  exact Nat.mod_eq_of_lt (by omega)

/-- At the fork slot the filter of the onboarding contract is `StaysValidAtFork`. -/
theorem staysValid_eq_atFork {v : BeaconState} (htrig : v.slot.toNat = forkSlot gloasForkEpoch)
    (d : PendingDeposit) : StaysValid (onboardingCutoff v) d = StaysValidAtFork d := by
  have hcut := onboardingCutoff_toNat htrig
  have hiff : onboardingCutoff v < d.slot ↔ forkCutoff < d.slot.toNat := by
    rw [UInt64.lt_iff_toNat_lt, hcut]
  simp [StaysValid, Onboardable, StaysValidAtFork, hiff]

/-- The upgrade takes the chain across. `upgradeToGloas` copies the slot, the finalized epoch,
the keys and the queue, and `completeUpgradeToGloas` keeps the first three. Its queue, read
through `depositValid`, is the copied queue read through `StaysValidAtFork`, which is
`queueAtFork` of the Fulu state. So the four values of the chain stay as they are. -/
theorem gloasChain_upgrade {R : List BLSPubkey} {Q : List PendingDeposit} {d : Nat}
    {u : EthCLSpecs.Fulu.BeaconState} {w : BeaconState}
    (hu : EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (htrig : u.slot.toNat = forkSlot gloasForkEpoch)
    (hrun : runPure (completeUpgradeToGloas (StateTransition := GloasRun))
      (upgradeToGloas gloasForkVersion u) = .ok ((), w))
    (h : FuluChain R Q d u) : GloasChain R Q d w := by
  obtain ⟨hs, hf, hk, -, hq⟩ := (completeUpgradeToGloas_ensures _
    (upgradeToGloas_invariants _ hu).registrySizes).runPure_ok hrun
  have e1 : (finalizedSlot w).toNat
      = (EthCLSpecs.Proofs.Fulu.IndexAssignment.finalizedSlot u).toNat := by
    unfold finalizedSlot
    rw [hf]
    rfl
  have e2 : w.slot.toNat = u.slot.toNat := by
    rw [hs]
    rfl
  have e3 : (registryKeys w).toList
      = (EthCLSpecs.Proofs.Fulu.IndexAssignment.registryKeys u).toList := by
    rw [hk]
    exact congrArg (fun view => view.keys.toList) (registryView_upgradeToGloas gloasForkVersion u)
  have e4 : validQueue w = queueAtFork u := by
    unfold validQueue queueAtFork
    rw [hq, upgradeToGloas_pendingDeposits, Array.toList_map]
    exact List.filter_congr fun d _ => staysValid_eq_atFork (v := upgradeToGloas gloasForkVersion u)
      htrig d
  unfold GloasChain
  rw [e1, e2, e3, e4]
  exact h

/-! ## The Gloas steps -/

/-- One Gloas slot keeps the chain. The scan of the slot is a scan of `validQueue`: the filter
drops deposits with an invalid signature alone. -/
theorem gloasChain_slot {R : List BLSPubkey} {Q : List PendingDeposit} {d : Nat}
    {x z : BeaconState}
    (hx : SimpleStateInvariants x) (hz : SimpleStateInvariants z) (hprog : SlotProgress x z)
    (h : GloasChain R Q d x) : GloasChain R Q d z := by
  obtain ⟨hep, hscan⟩ := hprog.deposits
  have hscan' := hscan.filter _ _ depositValid (fun _ _ hv => hv)
  exact h.scan _ _ hscan'
    (by
      rw [finalizedSlot_toNat hx, finalizedSlot_toNat hz]
      exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp hep))
    (by have := hprog.slot; omega) (fun _ he => UInt64.le_iff_toNat_le.mp he)

/-- One Gloas block keeps the chain, as a Fulu block does. -/
theorem gloasChain_block {R : List BLSPubkey} {Q : List PendingDeposit} {d : Nat}
    {v w : BeaconState}
    (hinv : SimpleStateInvariants v) (block : BeaconBlock)
    (hrun : runPure (processBlock (StateTransition := GloasRun) block) v = .ok ((), w))
    (h : GloasChain R Q d v) : GloasChain R Q d w := by
  have hst := (processBlock_keepsFrame block (Ctx.of v true) rfl v
    (StepInv.start v true hinv.registrySizes)).runPure_ok hrun
  obtain ⟨hs, hf, hk, ⟨extra, hq, hadm⟩, -⟩ := hst
  simp only [Ctx.of] at hs hf hk hq hadm
  have e1 : (finalizedSlot w).toNat = (finalizedSlot v).toNat := by
    unfold finalizedSlot
    rw [hf]
  have e4 : validQueue w = validQueue v ++ extra.toList.filter depositValid := by
    unfold validQueue
    rw [hq, Array.toList_append, List.filter_append]
  unfold GloasChain
  rw [e1, hs, hk, e4]
  refine Chain.append _ _ h fun e he => ?_
  have he₀ : e ∈ extra.toList := (List.mem_filter.mp he).1
  rcases (hadm e (Array.mem_toList_iff.mp he₀)).2 with h1 | h1
  · exact Or.inl (Array.mem_toList_iff.mpr h1)
  · refine Or.inr ?_
    show v.slot.toNat ≤ e.slot.toNat
    rw [h1]
    exact Nat.le_refl _

/-- Every reachable Gloas state is on the chain, when each Fulu anchor and each Gloas anchor
is. The `upgrade` case starts at a reachable Fulu state, which is on the chain by
`fuluChain_of_reachable`, and `gloasChain_upgrade` takes it across. -/
theorem gloasChain_of_reachable {anchors : Anchors}
    {R : List BLSPubkey} {Q : List PendingDeposit} {d : Nat} {w : BeaconState}
    (hF : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    (hG : ∀ u, anchors.gloas u → SimpleStateInvariants u)
    (h0F : ∀ u, anchors.fulu u → FuluChain R Q d u)
    (h0G : ∀ u, anchors.gloas u → GloasChain R Q d u)
    (h : ReachableState anchors validated nextForkEpoch w) : GloasChain R Q d w := by
  induction h with
  | anchor ha _ => exact h0G _ ha
  | @upgrade u w hu htrig _ hrun =>
    exact gloasChain_upgrade (EthCLSpecs.Proofs.Fulu.ReachableState.simpleStateInvariants hF hu)
      htrig hrun (fuluChain_of_reachable hF h0F hu)
  | slots target hv _ hrun ih =>
    have hinv := hv.simpleStateInvariants hF hG
    exact (processSlots_progress (GloasChain R Q d)
      (fun x z hx hz hprog hPx => gloasChain_slot hx hz hprog hPx) target _ hinv ih).runPure_ok
        hrun
  | @block v w sb hv _ _ hrun _ ih =>
    exact gloasChain_block (hv.simpleStateInvariants hF hG) sb.message hrun ih

/-- A Fulu state is on the chain that starts at its own keys, queue and slot. -/
theorem fuluChain_start (t : EthCLSpecs.Fulu.BeaconState) :
    FuluChain (EthCLSpecs.Proofs.Fulu.IndexAssignment.registryKeys t).toList (queueAtFork t)
      t.slot.toNat t :=
  Chain.start _ _ _ _ _ _ _

/-! ## The theorem -/

/-- Two Gloas chains from one Fulu state, with compatible finality, hold the same public key at
every validator index both have.

* `t` is a reachable Fulu state, and the Fulu anchors satisfy `SimpleStateInvariants`.
* `w'` and `w''` are Gloas states reachable from `t`, through the upgrade: `ReachableState`
  with the one Fulu anchor `t`.
* The finality of the two is compatible at the slot of `t`: one of them has finalized no slot
  at or after it.

Then validator `i` has one public key in both registries, for every `i` both hold. The chain
with no finalized slot at or after `t` is on the queue of `t`, the other chain tracks that
queue, and `Chain.comparable` makes one key list a prefix of the other.

The statement holds at each `validated` flag and each end of the Gloas window. The proof rests
on Lean's three standard axioms and on no hash or signature assumption. -/
theorem indexAssignment_fromFulu {anchors : EthCLSpecs.Proofs.Fulu.Anchors}
    (hA : ∀ u, anchors.fulu u → EthCLSpecs.Proofs.Fulu.SimpleStateInvariants u)
    {t : EthCLSpecs.Fulu.BeaconState} {w' w'' : BeaconState}
    (ht : EthCLSpecs.Proofs.Fulu.ReachableState anchors validated gloasForkEpoch t)
    (h' : ReachableState (Anchors.onlyFulu t) validated nextForkEpoch w')
    (h'' : ReachableState (Anchors.onlyFulu t) validated nextForkEpoch w'')
    (hc : CompatibleFinality t.slot w' w'')
    (i : Nat) (hi' : i < w'.validators.val.size) (hi'' : i < w''.validators.val.size) :
    w'.validators.val[i].pubkey = w''.validators.val[i].pubkey := by
  have hts := EthCLSpecs.Proofs.Fulu.ReachableState.simpleStateInvariants hA ht
  -- The one anchor is the Fulu state `t`, which is on its own chain. No Gloas anchor exists.
  have chain : ∀ {w : BeaconState}, ReachableState (Anchors.onlyFulu t) validated nextForkEpoch w →
      GloasChain (EthCLSpecs.Proofs.Fulu.IndexAssignment.registryKeys t).toList (queueAtFork t)
        t.slot.toNat w :=
    fun h => gloasChain_of_reachable (anchors := Anchors.onlyFulu t)
      (fun u (hu : u = t) => hu ▸ hts) (fun _ hu => False.elim hu)
      (fun u (hu : u = t) => hu ▸ fuluChain_start t) (fun _ hu => False.elim hu) h
  have c' := chain h'
  have c'' := chain h''
  have hcmp : (registryKeys w').toList <+: (registryKeys w'').toList ∨
      (registryKeys w'').toList <+: (registryKeys w').toList := by
    rcases hc with hc | hc
    · exact c'.comparable _ _ hc c''
    · exact (c''.comparable _ _ hc c').symm
  -- `registryKeys w` is `w.validators.val.map (·.pubkey)`, so its list has the registry's
  -- length and its entry `i` is the key of validator `i`.
  have h1 : i < (registryKeys w').toList.length := by simpa [registryKeys] using hi'
  have h2 : i < (registryKeys w'').toList.length := by simpa [registryKeys] using hi''
  have := getElem_eq_of_comparable hcmp i h1 h2
  simpa [registryKeys] using this

/-- The index assignment is stable across the Gloas upgrade: `IndexAssignmentFromFulu` holds.
The statement is `indexAssignment_fromFulu` at `validated = true` and at a Gloas window with
no end. -/
theorem indexAssignmentFromFulu : IndexAssignmentFromFulu :=
  fun _ _ _ _ hA ht h' h'' hc i hi' hi'' => indexAssignment_fromFulu hA ht h' h'' hc i hi' hi''

end

end EthCLSpecs.Proofs.Gloas
