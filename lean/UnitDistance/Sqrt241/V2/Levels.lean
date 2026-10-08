module

public import UnitDistance.Sqrt241.V2.Cut41
public import UnitDistance.Sqrt241.Levels.Family
public import UnitDistance.ProfiniteQuotientTower

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Version 2: the levels `K_j` and their Galois closures

The cut quotient `A41.ActualQuotient` is infinite and profinite, so it has a chain of open
normal subgroups `V_j` of index tending to infinity (`ProfiniteQuotient.openNormalChain`).
With `projB41 : G_B → A41.ActualQuotient`:

* `levelGroupB j = projB41⁻¹(V_j)`, open and normal in `G_B`, containing `kernelHat41`;
* `levelGroup j = levelGroupB j ⊓ detKer ≤ Ĝ`, open, normal in `G_B` (not in `Ĝ`);
* **`level j = Ω^{levelGroup j}`**: a finite extension of `ℚ` containing the detector field
  `D = Ω^{detKer}` (hence `M` and `B`), of degree `[Ĝ : levelGroup j] → ∞`;
* `closureGroup j = σ̂-core of levelGroup j`, normal in `Ĝ`, and
  **`levelClosure j = Ω^{closureGroup j}`**, finite Galois over `ℚ`, containing `level j`.
  It is admissible for the symmetric input: `inputSym.kernelHat ≤ Gal(Ω/levelClosure j) ≤ core`
  (`inputSym.kernelHat` is normal in `Ĝ` and lies in `kernelHat41 ⊓ detKer`).

The restriction `levelConj j` of `c₁` to `level j` exists because `c₁ ∈ G_B` normalizes
`levelGroup j`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.V2

open Tower Presentation Cut GroupData ProCGroups Retained Filter

/-! ### A chain in the cut quotient -/

instance cutQuotient_totallyDisconnected : TotallyDisconnectedSpace A41.ActualQuotient :=
  ProCGroups.totallyDisconnectedSpace_quotient_closedNormal A41.kernel
    (SourceLifts.kernel_isClosed _)

instance cutQuotient_infinite : Infinite A41.ActualQuotient := infinite41

theorem exists_chain : ∃ U : ℕ → OpenNormalSubgroup A41.ActualQuotient,
    ((U 0 : Subgroup A41.ActualQuotient) = ⊤) ∧ (∀ j, U (j + 1) ≤ U j) ∧
      Tendsto (fun j => Nat.card (A41.ActualQuotient ⧸ (U j).toSubgroup)) atTop atTop :=
  ProfiniteQuotient.openNormalChain A41.ActualQuotient

/-- Open normal subgroups of the cut quotient of index tending to infinity. -/
def chain : ℕ → OpenNormalSubgroup A41.ActualQuotient := exists_chain.choose

theorem chain_tendsto :
    Tendsto (fun j => Nat.card (A41.ActualQuotient ⧸ (chain j).toSubgroup)) atTop atTop :=
  exists_chain.choose_spec.2.2

/-! ### The level groups -/

/-- `U_j ≤ G_B`, the preimage of `V_j`. -/
def levelGroupB (j : ℕ) : Subgroup GB := (chain j).toSubgroup.comap projB41.toMonoidHom

instance levelGroupB_normal (j : ℕ) : (levelGroupB j).Normal := by
  unfold levelGroupB
  infer_instance

theorem isOpen_levelGroupB (j : ℕ) : IsOpen (levelGroupB j : Set GB) :=
  (chain j).isOpen.preimage projB41.continuous

theorem levelGroupB_index (j : ℕ) :
    (levelGroupB j).index = Nat.card (A41.ActualQuotient ⧸ (chain j).toSubgroup) :=
  Subgroup.index_comap_of_surjective _ projB41_surjective

/-- **`W_j = U_j ⊓ detKer`**, the fixing group of the level `K_j`. -/
def levelGroup (j : ℕ) : Subgroup Ghat := (levelGroupB j).map GB.subtype ⊓ input.detKer

theorem isOpen_levelGroup (j : ℕ) : IsOpen (levelGroup j : Set Ghat) := by
  have h1 : IsOpen (((levelGroupB j).map GB.subtype : Subgroup Ghat) : Set Ghat) := by
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact GB_isOpen.isOpenMap_subtype_val _ (isOpen_levelGroupB j)
  exact h1.inter input.isOpen_detKer

theorem isClosed_levelGroup (j : ℕ) : IsClosed (levelGroup j : Set Ghat) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_levelGroup j)

theorem levelGroup_le_detKer (j : ℕ) : levelGroup j ≤ input.detKer := inf_le_right

theorem levelGroup_le_GB (j : ℕ) : levelGroup j ≤ GB := by
  rintro _ ⟨⟨u, -, rfl⟩, -⟩
  exact u.2

theorem mem_levelGroup_iff (j : ℕ) (x : Ghat) :
    x ∈ levelGroup j ↔ ∃ hx : x ∈ GB, projB41 ⟨x, hx⟩ ∈ chain j ∧ x ∈ input.detKer := by
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hd⟩
    exact ⟨u.2, hu, hd⟩
  · rintro ⟨hx, hc, hd⟩
    exact ⟨⟨⟨x, hx⟩, hc, rfl⟩, hd⟩

/-- `G_B` normalizes `W_j`. -/
theorem levelGroup_conj_mem (j : ℕ) {h x : Ghat} (hh : h ∈ GB) (hx : x ∈ levelGroup j) :
    h * x * h⁻¹ ∈ levelGroup j := by
  obtain ⟨hxB, hc, hd⟩ := (mem_levelGroup_iff j x).mp hx
  have hm : h * x * h⁻¹ ∈ GB := GB.mul_mem (GB.mul_mem hh hxB) (GB.inv_mem hh)
  refine (mem_levelGroup_iff j _).mpr ⟨hm, ?_, input.detKer_normal.conj_mem x hd h⟩
  have he : (⟨h * x * h⁻¹, hm⟩ : GB) = ⟨h, hh⟩ * ⟨x, hxB⟩ * (⟨h, hh⟩ : GB)⁻¹ := rfl
  rw [he, map_mul, map_mul, map_inv]
  exact (chain j).isNormal'.conj_mem _ hc _

theorem kernelHat41_le_levelGroup (j : ℕ) : kernelHat41 ≤ levelGroup j := by
  intro x hx
  obtain ⟨hxB, h1⟩ := (mem_kernelHat41_iff x).mp hx
  refine (mem_levelGroup_iff j x).mpr ⟨hxB, ?_, kernelHat41_le_detKer hx⟩
  rw [h1]
  exact (chain j).one_mem

theorem frob41_pow_four_mem_levelGroup (j : ℕ) :
    ((Local.frob41 0 : GB) : Ghat) ^ 4 ∈ levelGroup j :=
  kernelHat41_le_levelGroup j frob41_pow_four_mem

/-! ### The levels -/

/-- **The level `K_j = Ω^{W_j}`.** -/
def level (j : ℕ) : IntermediateField ℚ Omega := IntermediateField.fixedField (levelGroup j)

theorem level_fixingSubgroup (j : ℕ) : (level j).fixingSubgroup = levelGroup j :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨levelGroup j, isClosed_levelGroup j⟩

instance level_finiteDimensional (j : ℕ) : FiniteDimensional ℚ (level j) :=
  (InfiniteGalois.isOpen_iff_finite (level j)).mp (by
    rw [level_fixingSubgroup]
    exact isOpen_levelGroup j)

instance level_numberField (j : ℕ) : NumberField (level j) :=
  NumberField.of_module_finite ℚ _

theorem detectorField_le_level (j : ℕ) : input.detectorField ≤ level j :=
  IntermediateField.fixedField_le (levelGroup_le_detKer j)

theorem M_le_level (j : ℕ) : input.M ≤ level j :=
  input.M_le_detectorField.trans (detectorField_le_level j)

theorem BinOmega_le_level (j : ℕ) : BinOmega ≤ level j :=
  BinOmega_le_EOmega.trans (input.EOmega_le_M.trans (M_le_level j))

theorem mem_level_iff (j : ℕ) (x : Omega) : x ∈ level j ↔ ∀ w ∈ levelGroup j, w x = x := by
  constructor
  · intro hx w hw
    exact hx ⟨w, hw⟩
  · intro h w
    exact h w.1 w.2

theorem finrank_level (j : ℕ) : Module.finrank ℚ (level j) = (levelGroup j).index := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, level_fixingSubgroup]

instance levelGroup_finiteIndex (j : ℕ) : (levelGroup j).FiniteIndex := by
  constructor
  rw [← finrank_level]
  exact Module.finrank_pos.ne'

theorem index_levelGroupB_le (j : ℕ) : (levelGroupB j).index ≤ (levelGroup j).index := by
  have h1 : ((levelGroupB j).map GB.subtype).index ≤ (levelGroup j).index :=
    Subgroup.index_antitone inf_le_left
  have h2 : (levelGroupB j).index ≤ ((levelGroupB j).map GB.subtype).index := by
    rw [Subgroup.index_map_subtype, GB_index]
    omega
  exact h2.trans h1

/-- **The degrees of the levels tend to infinity.** -/
theorem level_degree_tendsto :
    Tendsto (fun j => Module.finrank ℚ (level j)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun j => (levelGroupB j).index)
  · intro j
    rw [finrank_level]
    exact index_levelGroupB_le j
  · simp only [levelGroupB_index]
    exact chain_tendsto

/-! ### The Galois closures -/

/-- The `σ̂`-core of `W_j`, normal in `Ĝ`. -/
def closureGroup (j : ℕ) : Subgroup Ghat := sigmaCore (levelGroup j)

instance closureGroup_normal (j : ℕ) : (closureGroup j).Normal :=
  sigmaCore_normal _ (fun _ hh _ hx => levelGroup_conj_mem j hh hx)

theorem isOpen_closureGroup (j : ℕ) : IsOpen (closureGroup j : Set Ghat) :=
  isOpen_sigmaCore _ (isOpen_levelGroup j)

theorem isClosed_closureGroup (j : ℕ) : IsClosed (closureGroup j : Set Ghat) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_closureGroup j)

/-- **The Galois closure `K̃_j = Ω^{σ̂-core W_j}`** of the level. -/
def levelClosure (j : ℕ) : IntermediateField ℚ Omega :=
  IntermediateField.fixedField (closureGroup j)

theorem levelClosure_fixingSubgroup (j : ℕ) :
    (levelClosure j).fixingSubgroup = closureGroup j :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨closureGroup j, isClosed_closureGroup j⟩

theorem levelClosure_finite_galois (j : ℕ) :
    FiniteDimensional ℚ (levelClosure j) ∧ IsGalois ℚ (levelClosure j) := by
  apply (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (levelClosure j)).mp
  rw [levelClosure_fixingSubgroup]
  exact ⟨isOpen_closureGroup j, closureGroup_normal j⟩

instance levelClosure_finiteDimensional (j : ℕ) : FiniteDimensional ℚ (levelClosure j) :=
  (levelClosure_finite_galois j).1

instance levelClosure_isGalois (j : ℕ) : IsGalois ℚ (levelClosure j) :=
  (levelClosure_finite_galois j).2

instance levelClosure_numberField (j : ℕ) : NumberField (levelClosure j) :=
  NumberField.of_module_finite ℚ _

theorem level_le_levelClosure (j : ℕ) : level j ≤ levelClosure j :=
  IntermediateField.fixedField_le (sigmaCore_le _)

theorem M_le_levelClosure (j : ℕ) : input.M ≤ levelClosure j :=
  (M_le_level j).trans (level_le_levelClosure j)

/-- The symmetric cut fixes the Galois closure. -/
theorem inputSym_kernelHat_le_levelClosure (j : ℕ) :
    inputSym.kernelHat ≤ (levelClosure j).fixingSubgroup := by
  rw [levelClosure_fixingSubgroup]
  exact le_sigmaCore_of_normal
    ((inputSym_kernelHat_le_kernelHat41).trans (kernelHat41_le_levelGroup j))

theorem levelClosure_fixing_le_core (j : ℕ) : (levelClosure j).fixingSubgroup ≤ input.core := by
  rw [levelClosure_fixingSubgroup]
  exact (sigmaCore_le _).trans ((levelGroup_le_detKer j).trans input.detKer_le_core)

/-! ### Complex conjugation on the levels -/

/-- `c₁ ∈ Ĝ`. -/
abbrev cHat : Ghat := ((input.E.conj 0 : GB) : Ghat)

theorem cHat_mem_GB : cHat ∈ GB := (input.E.conj 0).2

theorem cHat_mem_level (j : ℕ) {x : Omega} (hx : x ∈ level j) : cHat x ∈ level j := by
  rw [mem_level_iff] at hx ⊢
  intro w hw
  have hw' : cHat⁻¹ * w * cHat⁻¹⁻¹ ∈ levelGroup j :=
    levelGroup_conj_mem j (GB.inv_mem cHat_mem_GB) hw
  have h := hx _ hw'
  rw [inv_inv] at h
  have h2 := congrArg cHat h
  simpa [AlgEquiv.mul_apply, ← AlgEquiv.aut_inv] using h2

theorem cHat_inv_mem_level (j : ℕ) {x : Omega} (hx : x ∈ level j) : cHat⁻¹ x ∈ level j := by
  rw [mem_level_iff] at hx ⊢
  intro w hw
  have hw' : cHat * w * cHat⁻¹ ∈ levelGroup j := levelGroup_conj_mem j cHat_mem_GB hw
  have h : cHat (w (cHat⁻¹ x)) = x := hx _ hw'
  apply cHat.injective
  rw [h, ← AlgEquiv.mul_apply cHat cHat⁻¹, mul_inv_cancel, AlgEquiv.one_apply]

/-- The restriction of `c₁` to `K_j`, as a ring automorphism. -/
def levelConjRing (j : ℕ) : level j ≃+* level j where
  toFun x := ⟨cHat x, cHat_mem_level j x.2⟩
  invFun x := ⟨cHat⁻¹ x, cHat_inv_mem_level j x.2⟩
  left_inv x := by
    apply Subtype.ext
    change cHat⁻¹ (cHat (x : Omega)) = x
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  right_inv x := by
    apply Subtype.ext
    change cHat (cHat⁻¹ (x : Omega)) = x
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  map_mul' x y := Subtype.ext (map_mul cHat (x : Omega) y)
  map_add' x y := Subtype.ext (map_add cHat (x : Omega) y)

@[simp] theorem coe_levelConjRing (j : ℕ) (x : level j) :
    ((levelConjRing j x : level j) : Omega) = cHat x := rfl

/-- The complex embedding `φ|K_j`. -/
def levelPhi (j : ℕ) : level j →+* ℂ := input.phi.comp (level j).val.toRingHom

theorem levelConj_isConj (j : ℕ) (x : level j) :
    levelPhi j (levelConjRing j x) = star (levelPhi j x) := by
  change input.phi (cHat (x : Omega)) = star (input.phi (x : Omega))
  exact input.conj_isConj.eq (x : Omega)

end UnitDistance.Sqrt241.V2
