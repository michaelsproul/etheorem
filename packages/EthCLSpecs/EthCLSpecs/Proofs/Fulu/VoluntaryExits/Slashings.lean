import EthCLSpecs.Proofs.Fulu.VoluntaryExits

/-!
# `EthCLSpecs.Proofs.Fulu.VoluntaryExits.Slashings`: slashings keep the exit view

`process_operations` applies the proposer slashings and the attester slashings of a block
before its voluntary exits. A slashing calls `slash_validator`, which exits the slashed
validator and writes its record. An exit of that validator would then fail.

`exitView_of_slashings` proves that the slashings change nothing else an exit reads. Let `S`
hold every validator the slashings can slash. The state after the slashings then has the
`ExitView S` of the state before them. With `voluntaryExits_succeed_of_exitView`, exits of
validators outside `S` that pass the gates before the slashings succeed after them.

The proofs are frame proofs, in the style of the `KeepsCore` proofs of `Invariants/`. The
invariant is `fun w => ExitView S s w` for a fixed start `s`. Each step is partial correctness:
it says what a successful run keeps, and a slashing may still fail.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Fulu

open EthCLLib.Proofs
open EthCLLib.Spec (HasherTag CryptoBackend)
open EthCLSpecs.Fulu

section

variable [Preset] [HasherTag]

omit [HasherTag] in
/-- An exit view extends by one more step that keeps it. -/
theorem ExitView.step {S : ValidatorIndex → Prop} {s v w : BeaconState} (hv : ExitView S s v)
    (h : ExitView S v w) : ExitView S s w :=
  (hv.trans h).mono (fun _ hi => hi.elim id id)

omit [HasherTag] in
/-- A record update of `v` has the exit view of `v` when it leaves alone the slot, the genesis
validators root, the registry and the pending partial withdrawals. -/
theorem ExitView.of_fields (S : ValidatorIndex → Prop) (v w : BeaconState)
    (hslot : w.slot = v.slot) (hroot : w.genesisValidatorsRoot = v.genesisValidatorsRoot)
    (hvals : w.validators = v.validators)
    (hpend : w.pendingPartialWithdrawals = v.pendingPartialWithdrawals) : ExitView S v w :=
  ⟨hslot, hroot, by rw [hvals], fun _ _ _ => by rw [hvals], fun _ hp => Or.inr (hpend ▸ hp)⟩

omit [HasherTag] in
/-- A record update of `v` has the exit view of `v` when it overwrites the record of a validator
in `S`, and leaves alone the slot, the genesis validators root and the pending partial
withdrawals. -/
theorem ExitView.of_set {S : ValidatorIndex → Prop} {i : ValidatorIndex} (hi : S i)
    (v w : BeaconState) (y : Validator) (hslot : w.slot = v.slot)
    (hroot : w.genesisValidatorsRoot = v.genesisValidatorsRoot)
    (hvals : w.validators = v.validators.set! i.toNat y)
    (hpend : w.pendingPartialWithdrawals = v.pendingPartialWithdrawals) : ExitView S v w := by
  refine ⟨hslot, hroot, by rw [hvals]; simp, fun j hj hlt => ?_, fun p hp => Or.inr (hpend ▸ hp)⟩
  have hne : i.toNat ≠ j.toNat := fun h' => hj (UInt64.toNat_inj.mp h'.symm ▸ hi)
  rw [hvals, sszList_set!_getElem!_of_ne _ _ hlt hne]

/-! ## Box-returning balance writes -/

/-- `increaseBalance` writes the balances of the box it is handed, which an exit does not read.
The threaded state stays, and the returned box holds a value with the exit view. -/
theorem increaseBalance_keepsExitView (i : ValidatorIndex) (d : Gwei) {S : ValidatorIndex → Prop}
    {s s0 v : BeaconState} (hs : ExitView S s s0) :
    RunEnsures v (increaseBalance (StateTransition := FuluRun) (pureState s0) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ ExitView S s s') := by
  unfold increaseBalance
  run_ensures
  exact ⟨trivial, _, rfl, hs.step (ExitView.of_fields S s0 _ rfl rfl rfl rfl)⟩

/-- `decreaseBalance` writes the balances of the box it is handed, as `increaseBalance` does. -/
theorem decreaseBalance_keepsExitView (i : ValidatorIndex) (d : Gwei) {S : ValidatorIndex → Prop}
    {s s0 v : BeaconState} (hs : ExitView S s s0) :
    RunEnsures v (decreaseBalance (StateTransition := FuluRun) (pureState s0) i d)
      (fun b w => w = v ∧ ∃ s', b = pureState s' ∧ ExitView S s s') := by
  unfold decreaseBalance
  run_ensures
  exact ⟨trivial, _, rfl, hs.step (ExitView.of_fields S s0 _ rfl rfl rfl rfl)⟩

variable [Config]

/-! ## The exit of a validator in `S` -/

/-- `compute_exit_epoch_and_update_churn` writes the two churn fields, which the exit view does
not cover. -/
theorem computeExitEpochAndUpdateChurn_keepsExitView (b : Gwei) (S : ValidatorIndex → Prop)
    (s : BeaconState) :
    Preserves (fun w => ExitView S s w)
      (computeExitEpochAndUpdateChurn (StateTransition := FuluRun) b) := by
  intro v hv
  unfold computeExitEpochAndUpdateChurn
  run_ensures
  all_goals exact hv.step (ExitView.of_fields S v _ rfl rfl rfl rfl)

/-- `initiate_validator_exit` of a validator in `S` keeps the exit view: it writes that
validator's record and the two churn fields. -/
theorem initiateValidatorExit_keepsExitView {S : ValidatorIndex → Prop} {i : ValidatorIndex}
    (hi : S i) (s : BeaconState) :
    Preserves (fun w => ExitView S s w) (initiateValidatorExit (StateTransition := FuluRun) i) := by
  intro v hv
  unfold initiateValidatorExit
  run_ensures
  · exact hv
  · refine Preserves.run (computeExitEpochAndUpdateChurn_keepsExitView _ S s) hv (fun _ w hw => ?_)
    run_ensures
    exact hw.step (ExitView.of_set hi w _ _ rfl rfl rfl rfl)

/-- `slash_validator` of a validator in `S` keeps the exit view. It exits the validator, marks
its record slashed, and writes the slashings vector and three balances. -/
theorem slashValidator_keepsExitView {S : ValidatorIndex → Prop} {i : ValidatorIndex} (hi : S i)
    (s : BeaconState) :
    Preserves (fun w => ExitView S s w) (slashValidator (StateTransition := FuluRun) i) := by
  intro v hv
  unfold slashValidator
  run_ensures
  refine Preserves.run (initiateValidatorExit_keepsExitView hi s) hv (fun _ w hw => ?_)
  run_ensures
  refine RunEnsures.weaken (decreaseBalance_keepsExitView _ _
    (hw.step (ExitView.of_set hi w _ _ rfl rfl rfl rfl))) (fun _ _ hbox => ?_)
  obtain ⟨hst, _, hb, hs1⟩ := hbox
  subst hst hb
  run_ensures
  refine RunEnsures.weaken (increaseBalance_keepsExitView _ _ hs1) (fun _ _ hbox => ?_)
  obtain ⟨hst, _, hb, hs2⟩ := hbox
  subst hst hb
  run_ensures
  refine RunEnsures.weaken (increaseBalance_keepsExitView _ _ hs2) (fun _ _ hbox => ?_)
  obtain ⟨hst, _, hb, hs3⟩ := hbox
  subst hst hb
  run_ensures
  exact hs3

variable [CryptoBackend]

/-! ## Slashings -/

/-- `process_proposer_slashing` keeps the exit view when `S` holds the slashed proposer. -/
theorem processProposerSlashing_keepsExitView {S : ValidatorIndex → Prop} (ps : ProposerSlashing)
    (hS : S ps.signedHeader1.message.proposerIndex) (s : BeaconState) :
    Preserves (fun w => ExitView S s w)
      (processProposerSlashing (StateTransition := FuluRun) ps) := by
  intro v hv
  unfold processProposerSlashing
  run_ensures
  exact Preserves.run (slashValidator_keepsExitView hS s) hv (fun _ _ hw => hw)

/-- The validator indices `process_attester_slashing` walks: the indices both attestations
name, sorted. It slashes a subset of them. -/
def attesterSlashingIndices (asl : AttesterSlashing) : Array ValidatorIndex :=
  (EthCLLib.Spec.arrayInter asl.attestation1.attestingIndices.toArray
    asl.attestation2.attestingIndices.toArray).qsort (· < ·)

/-- `process_attester_slashing` keeps the exit view when `S` holds every index the slashing
walks. -/
theorem processAttesterSlashing_keepsExitView {S : ValidatorIndex → Prop} (asl : AttesterSlashing)
    (hS : ∀ i ∈ attesterSlashingIndices asl, S i) (s : BeaconState) :
    Preserves (fun w => ExitView S s w)
      (processAttesterSlashing (StateTransition := FuluRun) asl) := by
  intro v hv
  unfold processAttesterSlashing
  run_ensures
  -- The loop invariant carries the exit view, and that the indices still to walk are in `S`.
  rw [← Array.forIn_toList]
  refine RunEnsures.weaken (runEnsures_forIn_list
    (fun rest (_ : Bool) w => ExitView S s w ∧ ∀ x ∈ rest, S x) (fun _ w => ExitView S s w)
    (fun idx rest _ w hI => ?_) (fun _ _ hI => hI.1) _ _ _
    ⟨hv, fun x hx => hS x (Array.mem_toList_iff.mp hx)⟩) (fun _ w hw => ?_)
  · obtain ⟨hw, hrest⟩ := hI
    have hidx : S idx := hrest idx List.mem_cons_self
    have hrest' : ∀ x ∈ rest, S x := fun x hx => hrest x (List.mem_cons_of_mem _ hx)
    run_ensures
    · refine Preserves.run (slashValidator_keepsExitView hidx s) hw (fun _ w' hw' => ?_)
      run_ensures
      exact ⟨hw', hrest'⟩
    · exact ⟨hw, hrest'⟩
  · run_ensures
    exact hw

/-! ## The slashings of a block -/

omit [Config] [CryptoBackend] in
/-- `ForM.forM` over an array keeps `P` when the handler does on each element of the array. The
membership form of `Preserves.forM_array`. -/
theorem preserves_forM_array_mem {α : Type} {P : BeaconState → Prop}
    {handler : α → FuluRun PUnit} (xs : Array α) (hf : ∀ x ∈ xs, Preserves P (handler x)) :
    Preserves P (ForM.forM xs handler) := by
  have hlist : ∀ l : List α, (∀ x ∈ l, Preserves P (handler x)) → ∀ v, P v →
      RunEnsures v (l.foldlM (fun (_ : PUnit) => handler) ⟨⟩) (fun _ w => P w) := by
    intro l
    induction l with
    | nil =>
      intro _ v hv
      rw [List.foldlM_nil]
      exact runEnsures_pure hv
    | cons x rest ih =>
      intro h v hv
      rw [List.foldlM_cons]
      exact runEnsures_bind ((h x List.mem_cons_self v hv).weaken fun _ w hw =>
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) w hw)
  intro v hv
  rw [show (ForM.forM xs handler) = (xs.foldlM (fun (_ : PUnit) => handler) ⟨⟩) from rfl,
    ← Array.foldlM_toList]
  exact hlist xs.toList (fun x hx => hf x (Array.mem_toList_iff.mp hx)) v hv

/-- The state after the proposer slashings and the attester slashings of a block has the exit
view of the state before them, when `S` holds every validator they can slash: the proposer of
each proposer slashing, and each index an attester slashing walks.

The two runs are the folds `process_operations` makes over the slashings. The theorem assumes
they succeed and says what a successful run keeps. -/
theorem exitView_of_slashings {S : ValidatorIndex → Prop} {s s₁ s₂ : BeaconState}
    (pss : Array ProposerSlashing) (ass : Array AttesterSlashing)
    (hps : ∀ ps ∈ pss, S ps.signedHeader1.message.proposerIndex)
    (has : ∀ asl ∈ ass, ∀ i ∈ attesterSlashingIndices asl, S i)
    (h₁ : runPure (ForM.forM pss (processProposerSlashing (StateTransition := FuluRun))) s =
      .ok ((), s₁))
    (h₂ : runPure (ForM.forM ass (processAttesterSlashing (StateTransition := FuluRun))) s₁ =
      .ok ((), s₂)) :
    ExitView S s s₂ := by
  have hv₁ : ExitView S s s₁ :=
    (preserves_forM_array_mem pss
      (fun ps hps' => processProposerSlashing_keepsExitView ps (hps ps hps') s) s
      (ExitView.refl S s)).runPure_ok h₁
  exact (preserves_forM_array_mem ass
    (fun asl hasl => processAttesterSlashing_keepsExitView asl (has asl hasl) s) s₁
    hv₁).runPure_ok h₂

end

end EthCLSpecs.Proofs.Fulu
