module

public import UnitDistance.Sqrt241.Retained.Sym
public import UnitDistance.Sqrt241.Levels.Census
public import UnitDistance.Sqrt241.Local.Cap41

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Version 2: the cut with the cap at `41₁`

`localElements41` is version 1's family of local elements with caps
`Frob(29₁), Frob(29₂), Frob(41₁)` (`Local/Cap41.lean`) in place of
`Frob(29₁), Frob(29₂), F₇²`. Its relations and labels hold (the label of `Frob(41₁)`,
`00111000`, is a good cap vector: `capVector41_good`), so the presentation of `G_B` and the
Golod–Shafarevich inequality of version 1 apply unchanged: the cut quotient
`A41.ActualQuotient` is infinite (`infinite41`).

The cut is **not** `σ̂`-stable (the conjugate prime `41₂` is not capped), so it is not an
`Input`; the arithmetic projection `projB41 : G_B → A41.ActualQuotient` and the cut kernel
`kernelHat41 ≤ G_B ≤ Ĝ` are built as for an `Input` (`Retained/Basic.lean`), and
`kernelHat41` is normal in `G_B` only. It contains the symmetric cut kernel
(`inputSym_kernelHat_le_kernelHat41`), which is normal in `Ĝ`, and `Frob(41₁)⁴`
(`frob41_pow_four_mem`), and lies in version 1's detector kernel (`kernelHat41_le_detKer`):
fourth powers of elements of `G_B` lie in `detKer` (`Input.pow_four_mem_detKer`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.V2

open Tower Presentation Cut GroupData ProCGroups ProCGroups.Presentations Retained
open _root_.UnitDistance.Sqrt241.Local

/-! ### Fourth powers lie in the detector kernel -/

theorem _root_.UnitDistance.Sqrt241.Retained.Input.pow_four_mem_magnusKer (I : Input) {g : Ghat}
    (hg : g ∈ GB) :
    g ^ 4 ∈ I.magnusKer := by
  refine (I.mem_magnusKer_iff _).mpr ⟨GB.pow_mem hg 4, ?_⟩
  have he : (⟨g ^ 4, GB.pow_mem hg 4⟩ : GB) = (⟨g, hg⟩ : GB) ^ 4 := rfl
  rw [he, map_pow]
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (I.magnusB ⟨g, hg⟩)
  rw [← hy, ← QuotientGroup.mk_pow, Magnus.pow_four, QuotientGroup.mk_one]

theorem _root_.UnitDistance.Sqrt241.Retained.Input.pow_four_mem_detKer (I : Input) {g : Ghat}
    (hg : g ∈ GB) :
    g ^ 4 ∈ I.detKer := by
  have hg' : sigmaHat⁻¹ * g * sigmaHat ∈ GB := by
    simpa using GB_normal.conj_mem g hg sigmaHat⁻¹
  have he : sigmaHat⁻¹ * g ^ 4 * sigmaHat = (sigmaHat⁻¹ * g * sigmaHat) ^ 4 := by
    have h := map_pow (MulAut.conj sigmaHat⁻¹) g 4
    simp only [MulAut.conj_apply, inv_inv] at h
    exact h
  rw [Input.detKer, mem_sigmaCore_iff, he]
  exact ⟨⟨I.pow_four_mem_retainedKer hg, I.pow_four_mem_magnusKer hg⟩,
    ⟨I.pow_four_mem_retainedKer hg', I.pow_four_mem_magnusKer hg'⟩⟩

/-! ### The local elements with the cap at `41₁` -/

/-- **Version 2's local elements**: the caps are `Frob(29₁), Frob(29₂), Frob(41₁)`. -/
def localElements41 : LocalElements where
  conj := ![conj₁, conj₂]
  tameInertia := tameInertia
  tameFrobenius := tameFrobenius
  dyadic := dyadicLocal
  cap := ![frob29 0, frob29 1, frob41 0]

theorem localElements41_relations : localElements41.Relations where
  conj_sq k := by
    fin_cases k
    · exact conj₁_sq
    · exact conj₂_sq
  tame q := by
    rw [← tameN_eq_tameNorm]
    exact tame_relation q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The label `00111000` of `Frob(41₁)` is a good cap vector. -/
theorem capVector41_good : CapGood (frob41Vec 0) := by decide +kernel

theorem localElements41_labels : localElements41.Labels where
  conj k := by
    fin_cases k
    · exact genusLabel_of_hasLabelHat _ _ conj₁_hasLabel
    · exact genusLabel_of_hasLabelHat _ _ conj₂_hasLabel
  tameInertia q := by
    exact (genusLabel_of_hasLabelHat _ _ (tameInertia_hasLabel q)).trans
      (congrArg _ (by fin_cases q <;> rfl))
  tameFrobenius q := by
    exact (genusLabel_of_hasLabelHat _ _ (tameFrobenius_hasLabel q)).trans
      (congrArg _ (by fin_cases q <;> rfl))
  dyadicA P := by
    exact (genusLabel_of_hasLabelHat _ _ (dyadicLocal_generator_hasLabel P 0)).trans
      (congrArg _ (by fin_cases P <;> rfl))
  dyadicB P := by
    exact (genusLabel_of_hasLabelHat _ _ (dyadicLocal_generator_hasLabel P 1)).trans
      (congrArg _ (by fin_cases P <;> rfl))
  dyadicC P := by
    exact (genusLabel_of_hasLabelHat _ _ (dyadicLocal_generator_hasLabel P 2)).trans
      (congrArg _ (by fin_cases P <;> rfl))
  cap k := by
    have h0 : genusLabel (frob29 0) = Multiplicative.ofAdd (GroupData.capVector 0) :=
      (genusLabel_of_hasLabelHat _ _ (frob29_hasLabel 0)).trans (congrArg _ rfl)
    have h1 : genusLabel (frob29 1) = Multiplicative.ofAdd (GroupData.capVector 1) :=
      (genusLabel_of_hasLabelHat _ _ (frob29_hasLabel 1)).trans (congrArg _ rfl)
    have h2 : genusLabel (frob41 0) = Multiplicative.ofAdd (frob41Vec 0) :=
      genusLabel_of_hasLabelHat _ _ (frob41_hasLabel 0)
    fin_cases k
    · change CapGood (genusLabel (frob29 0)).toAdd
      rw [h0]; exact capVector_good 0
    · change CapGood (genusLabel (frob29 1)).toAdd
      rw [h1]; exact capVector_good 1
    · change CapGood (genusLabel (frob41 0)).toAdd
      rw [h2]; exact capVector41_good

/-! ### The cut quotient and the arithmetic projection -/

/-- The lifts of version 2's local elements to `F(8)`. -/
abbrev A41 : SourceLifts := localElements41.sourceLifts

theorem hL41 : A41.Labels := LocalElements.sourceLifts_labels localElements41_labels

theorem hgen41 : A41.Presentation genuineRelation :=
  LocalElements.presentation localElements41_relations localElements41_labels

theorem relationKernel_le_kernel41 : (relationKernel : Subgroup Source) ≤ A41.kernel := by
  rw [← LocalElements.relators_generate localElements41_relations localElements41_labels]
  exact A41.relators_closure_le_kernel genuineRelation detector_genuineRelation

/-- **The version 2 cut quotient is infinite** (Golod–Shafarevich, as in version 1). -/
theorem infinite41 : Infinite A41.ActualQuotient :=
  A41.infinite_of_presentation hL41 genuineRelation detector_genuineRelation hgen41

/-- `F(8)/R → F(8)/cut`. -/
def liftR41 : (Source ⧸ (relationKernel : Subgroup Source)) →ₜ* A41.ActualQuotient :=
  ProCGroups.QuotientGroup.liftₜ (relationKernel : Subgroup Source) A41.projection
    (fun _ hg => A41.projection_eq_one_of_mem (relationKernel_le_kernel41 hg))

/-- **`G_B → F(8)/cut`** for the cut with the cap at `41₁`. -/
def projB41 : GB →ₜ* A41.ActualQuotient :=
  liftR41.comp ⟨freeQuotientEquiv.symm.toMulEquiv.toMonoidHom, freeQuotientEquiv.symm.continuous⟩

theorem projB41_freeMap (g : Source) : projB41 (freeMap g) = A41.projection g := by
  have h : freeQuotientEquiv.symm (freeMap g) =
      QuotientGroup.mk' (relationKernel : Subgroup Source) g := by
    rw [ContinuousMulEquiv.symm_apply_eq]
    rfl
  change liftR41 (freeQuotientEquiv.symm (freeMap g)) = _
  rw [h]
  rfl

theorem projB41_surjective : Function.Surjective projB41 := by
  intro x
  obtain ⟨g, rfl⟩ := A41.projection_surjective x
  exact ⟨freeMap g, projB41_freeMap g⟩

/-! ### The cut kernel in `Ĝ` -/

/-- **The cut kernel with the cap at `41₁`**, as a subgroup of `G_B ≤ Ĝ`. -/
def kernelHat41 : Subgroup Ghat := projB41.toMonoidHom.ker.map GB.subtype

theorem mem_kernelHat41_iff (g : Ghat) :
    g ∈ kernelHat41 ↔ ∃ h : g ∈ GB, projB41 ⟨g, h⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem kernelHat41_le_GB : kernelHat41 ≤ GB := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

/-- `G_B`-conjugation preserves `kernelHat41`. -/
theorem kernelHat41_conj_mem {h x : Ghat} (hh : h ∈ GB) (hx : x ∈ kernelHat41) :
    h * x * h⁻¹ ∈ kernelHat41 := by
  obtain ⟨hxB, hx1⟩ := (mem_kernelHat41_iff x).mp hx
  have hm : h * x * h⁻¹ ∈ GB := GB.mul_mem (GB.mul_mem hh hxB) (GB.inv_mem hh)
  refine (mem_kernelHat41_iff _).mpr ⟨hm, ?_⟩
  have he : (⟨h * x * h⁻¹, hm⟩ : GB) = ⟨h, hh⟩ * ⟨x, hxB⟩ * (⟨h, hh⟩ : GB)⁻¹ := rfl
  rw [he, map_mul, map_mul, map_inv, hx1, mul_one, mul_inv_cancel]

theorem kernelHat41_eq_map : kernelHat41 = A41.kernel.map freeHat.toMonoidHom := by
  ext x
  rw [mem_kernelHat41_iff]
  constructor
  · rintro ⟨hx, h1⟩
    obtain ⟨s, hs⟩ := freeMap_surjective (⟨x, hx⟩ : GB)
    refine ⟨s, ?_, ?_⟩
    · rw [← hs, projB41_freeMap] at h1
      exact (QuotientGroup.eq_one_iff s).mp h1
    · change ((freeMap s : GB) : Ghat) = x
      rw [hs]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨freeHat_mem s, ?_⟩
    change projB41 (freeMap s) = 1
    rw [projB41_freeMap]
    exact A41.projection_eq_one_of_mem hs

/-- `Frob(41₁)⁴` lies in the cut kernel. -/
theorem frob41_pow_four_mem : ((frob41 0 : GB) : Ghat) ^ 4 ∈ kernelHat41 := by
  rw [kernelHat41_eq_map]
  refine ⟨A41.cap 2 ^ 4, A41.deep_mem_kernel 6, ?_⟩
  change freeHat (LocalElements.lift (frob41 0) ^ 4) = _
  rw [map_pow, freeHat_apply, LocalElements.freeMap_lift]

/-- The fourth power of the lift of `Frob(29_P)` is a cut word with the cap at `41₁`. -/
theorem lift_frob29_pow_four_mem41 (P : Fin 2) :
    LocalElements.lift (frob29 P) ^ 4 ∈ A41.kernel := by
  fin_cases P
  · exact A41.deep_mem_kernel 4
  · exact A41.deep_mem_kernel 5

theorem localElementsSym_cap_lift_mem (k : Fin 3) :
    LocalElements.lift (localElementsSym.cap k) ^ 4 ∈ A41.kernel := by
  fin_cases k
  · exact lift_frob29_pow_four_mem41 0
  · exact lift_frob29_pow_four_mem41 1
  · exact lift_frob29_pow_four_mem41 0

/-- **The symmetric cut lies in the cut with the cap at `41₁`.** -/
theorem inputSym_kernelHat_le_kernelHat41 : inputSym.kernelHat ≤ kernelHat41 := by
  rw [Input.kernelHat_eq_map, kernelHat41_eq_map]
  apply Subgroup.map_mono
  exact kernel_le_of_same_local localElements41 localElementsSym rfl rfl rfl rfl
    localElementsSym_cap_lift_mem

/-- **The cut with the cap at `41₁` lies in version 1's detector kernel.** -/
theorem kernelHat41_le_detKer : kernelHat41 ≤ input.detKer := by
  rw [kernelHat41_eq_map, Subgroup.map_le_iff_le_comap]
  have hN : IsClosed ((input.detKer.comap freeHat.toMonoidHom : Subgroup Source) : Set Source) :=
    input.isClosed_detKer.preimage freeHat.continuous
  have hsym : localElementsSym.sourceLifts.kernel ≤ input.detKer.comap freeHat.toMonoidHom := by
    rw [← Subgroup.map_le_iff_le_comap]
    change inputSym.A.kernel.map freeHat.toMonoidHom ≤ _
    rw [← Input.kernelHat_eq_map]
    exact (inputSym_kernelHat_le).trans input.kernelHat_le_detKer
  apply kernel_le_of_same_local' localElementsSym localElements41 rfl rfl rfl rfl _ hN hsym
  intro k
  change freeHat (LocalElements.lift (localElements41.cap k) ^ 4) ∈ input.detKer
  rw [map_pow, freeHat_apply, LocalElements.freeMap_lift]
  exact input.pow_four_mem_detKer (localElements41.cap k).2

theorem kernelHat41_le_core : kernelHat41 ≤ input.core :=
  kernelHat41_le_detKer.trans input.detKer_le_core

theorem isClosed_kernelHat41 : IsClosed (kernelHat41 : Set Ghat) := by
  have hK : IsClosed ((projB41.toMonoidHom.ker : Subgroup GB) : Set GB) :=
    ProCGroups.ContinuousMonoidHom.isClosed_ker projB41
  have hc : IsCompact ((projB41.toMonoidHom.ker : Subgroup GB) : Set GB) := hK.isCompact
  have h := hc.image (continuous_subtype_val : Continuous (fun x : GB => (x : Ghat)))
  rw [kernelHat41, Subgroup.coe_map, Subgroup.coe_subtype]
  exact h.isClosed

end UnitDistance.Sqrt241.V2
