/-!
# `EthCLSpecs.Proofs.FinalizedRegistry`: a validator with a finalized eligibility epoch is in the common history

A client keeps one map from validator index to public key for every chain it follows. The map
is sound for the validators it holds when every chain the client follows agrees on them. This
module holds the argument for one rule of admission: a validator enters the map once its
`activation_eligibility_epoch` is finalized, together with every validator at a lower index.

The argument reads no spec code. It works on a `View`, the four values it needs from a beacon
state, and on `Follows`, what a chain keeps true of its views. The fork modules
`Proofs/<Fork>/FinalizedValidators.lean` prove that the state transition keeps `Follows`, the
fork upgrades included.

## The argument

Let `t` be a state, and `w` a state on a chain from `t`.

* **The registry only grows.** The keys of `t` are a prefix of the keys of `w`
  (`Follows.keys`).
* **A validator added after `t` becomes eligible after `t`.** Its
  `activation_eligibility_epoch` starts above the slot of `t` (`Follows.late`). A new validator
  starts at `FAR_FUTURE_EPOCH`, and `process_registry_updates` later writes
  `current_epoch + 1`, at a slot that is the slot of `t` or a later one.

Now let `w` have finalized an epoch that starts at or before the slot of `t`. A validator of
`w` whose eligibility epoch is finalized has an eligibility epoch that starts at or before the
slot of `t`. So `t` holds that validator already (`Follows.lt_size_of_finalized`), and every
chain from `t` holds it at the same index with the same key (`keys_eq_of_finalized`).

No step of this depends on what a queued deposit becomes. That is the difference from the
index assignment of all validators, which a fork upgrade can split
(`Proofs/Gloas/IndexAssignment.lean`).
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.FinalizedRegistry

/-- What the argument reads from a beacon state of any fork: the slot, the finalized epoch, the
public keys of the registry in index order, and the `activation_eligibility_epoch` of each
validator. `κ` is the type of a public key. -/
structure View (κ : Type) where
  slot : Nat
  finalizedEpoch : UInt64
  keys : Array κ
  elig : Array UInt64

variable {κ : Type}

/-- `w` follows `t`, at `spe` slots per epoch. The registry of `w` extends the registry of `t`,
`w` is at the slot of `t` or later, and each validator of `w` that `t` does not hold has an
eligibility epoch that starts above the slot of `t`. The product is in `Nat`, so
`FAR_FUTURE_EPOCH` does not wrap. -/
structure Follows (spe : Nat) (t w : View κ) : Prop where
  size : w.elig.size = w.keys.size
  slot : t.slot ≤ w.slot
  keys : t.keys.toList <+: w.keys.toList
  late : ∀ (j : Nat) (h : j < w.elig.size), t.keys.size ≤ j → t.slot < w.elig[j].toNat * spe

/-- A view follows itself. No index is at or above its own registry size. -/
theorem Follows.refl (spe : Nat) {t : View κ} (h : t.elig.size = t.keys.size) :
    Follows spe t t :=
  ⟨h, Nat.le_refl _, List.prefix_refl _, fun _ hj hle => absurd (h ▸ hj) (Nat.not_lt.mpr hle)⟩

/-- One more step of the chain, from `x` to `z`. The registry grows, the slot does not fall,
and each eligibility epoch of `z` is the one `x` has at that index, or it starts above the
slot of `x`. Then `z` follows whatever `x` follows.

`x.elig[j]? = some z.elig[j]` reads "index `j` is in `x`, with the same value". -/
theorem Follows.step {spe : Nat} {t x z : View κ} (hx : Follows spe t x)
    (hsize : z.elig.size = z.keys.size) (hslot : x.slot ≤ z.slot)
    (hkeys : x.keys.toList <+: z.keys.toList)
    (helig : ∀ (j : Nat) (h : j < z.elig.size),
      x.elig[j]? = some z.elig[j] ∨ x.slot < z.elig[j].toNat * spe) :
    Follows spe t z := by
  refine ⟨hsize, Nat.le_trans hx.slot hslot, hx.keys.trans hkeys, fun j hj hle => ?_⟩
  rcases helig j hj with h | h
  · obtain ⟨hjx, he⟩ := Array.getElem?_eq_some_iff.mp h
    rw [← he]
    exact hx.late j hjx hle
  · exact Nat.lt_of_le_of_lt hx.slot h

/-- A validator of `w` with a finalized eligibility epoch is a validator of `t`, when the
finalized epoch of `w` starts at or before the slot of `t`. A validator that `t` does not hold
has an eligibility epoch that starts above that slot, so above the finalized epoch. -/
theorem Follows.lt_size_of_finalized {spe : Nat} {t w : View κ} (h : Follows spe t w)
    (hfin : w.finalizedEpoch.toNat * spe ≤ t.slot) {i : Nat} (hi : i < w.elig.size)
    (he : w.elig[i] ≤ w.finalizedEpoch) : i < t.keys.size := by
  apply Nat.lt_of_not_le
  intro hle
  have h1 := h.late i hi hle
  have h2 : w.elig[i].toNat * spe ≤ w.finalizedEpoch.toNat * spe :=
    Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp he)
  omega

/-- A validator of `t` is a validator of `w`, at the same index and with the same key. -/
theorem Follows.getElem_keys {spe : Nat} {t w : View κ} (h : Follows spe t w) {j : Nat}
    (hj : j < t.keys.size) : ∃ hj' : j < w.keys.size, w.keys[j] = t.keys[j] := by
  have hlen : t.keys.toList.length ≤ w.keys.toList.length := h.keys.length_le
  have hj' : j < w.keys.size := by
    simp only [Array.length_toList] at hlen
    omega
  refine ⟨hj', ?_⟩
  have hjl : j < t.keys.toList.length := by simpa using hj
  have := h.keys.getElem hjl
  simpa using this.symm

/-- Two chains from `t` agree on the finalized validators of one of them.

`w'` and `w''` follow `t`, and the finalized epoch of `w'` starts at or before the slot of
`t`. Validator `i` of `w'` has a finalized eligibility epoch. Then every index `j` up to `i`
is in both registries, with one public key. -/
theorem keys_eq_of_finalized {spe : Nat} {t w' w'' : View κ} (h' : Follows spe t w')
    (h'' : Follows spe t w'') (hfin : w'.finalizedEpoch.toNat * spe ≤ t.slot) {i j : Nat}
    (hji : j ≤ i) (hi : i < w'.elig.size) (he : w'.elig[i] ≤ w'.finalizedEpoch) :
    ∃ (hj' : j < w'.keys.size) (hj'' : j < w''.keys.size), w''.keys[j] = w'.keys[j] := by
  have hjt : j < t.keys.size := Nat.lt_of_le_of_lt hji (h'.lt_size_of_finalized hfin hi he)
  obtain ⟨hj', e'⟩ := h'.getElem_keys hjt
  obtain ⟨hj'', e''⟩ := h''.getElem_keys hjt
  exact ⟨hj', hj'', e''.trans e'.symm⟩

/-- The symmetric form. One of the two views has a finalized epoch that starts at or before the
slot of `t`, and validator `i` has a finalized eligibility epoch in both. Then `i` has one
public key in both. -/
theorem keys_eq_of_both_finalized {spe : Nat} {t w' w'' : View κ} (h' : Follows spe t w')
    (h'' : Follows spe t w'')
    (hfin : w'.finalizedEpoch.toNat * spe ≤ t.slot ∨ w''.finalizedEpoch.toNat * spe ≤ t.slot)
    {i : Nat} (hi' : i < w'.elig.size) (hi'' : i < w''.elig.size)
    (he' : w'.elig[i] ≤ w'.finalizedEpoch) (he'' : w''.elig[i] ≤ w''.finalizedEpoch) :
    ∃ (h₁ : i < w'.keys.size) (h₂ : i < w''.keys.size), w'.keys[i] = w''.keys[i] := by
  rcases hfin with hfin | hfin
  · obtain ⟨h₁, h₂, e⟩ := keys_eq_of_finalized h' h'' hfin (Nat.le_refl i) hi' he'
    exact ⟨h₁, h₂, e.symm⟩
  · obtain ⟨h₂, h₁, e⟩ := keys_eq_of_finalized h'' h' hfin (Nat.le_refl i) hi'' he''
    exact ⟨h₁, h₂, e⟩

end EthCLSpecs.Proofs.FinalizedRegistry
