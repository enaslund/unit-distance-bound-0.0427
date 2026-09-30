module

public import UnitDistance.Sqrt241.Relation.RadicalReciprocity
public import UnitDistance.Sqrt241.Relation.SqrtCharacter
public import UnitDistance.Sqrt241.Relation.LiftCorrection
public import UnitDistance.Sqrt241.Base.Selmer
public import UnitDistance.Sqrt241.Base.Units
public import UnitDistance.Sqrt241.Base.ClassNumber
public import UnitDistance.Sqrt241.Base.Signs

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Quadratic characters of `B` with prescribed inertia (via the ideal-square radical)

`prescribedQuadraticInertia_B : PrescribedQuadraticInertia B S`: every finite
family of local quadratic characters is realized on inertia outside `S` by a
global quadratic character of `B` unramified outside the family and `S`.

Proof. The generic realizer
`exists_absoluteCharacter_of_finiteSupport_radical_annihilator` applies to a
family whose reciprocity functional kills the ideal-square radical of `B`.
Since `h(B) = 1` and `𝓞_Bˣ = ±ε^ℤ` modulo squares, the radical is spanned by
the classes of `−1` and `ε` (`radical_B`). The family is corrected on the six
places of `S` by `a·γ₋₁ + b·γ_ε`, where `γ₋₁, γ_ε` are the characters of
`B(√−1)`, `B(√ε)` (unramified outside the dyadic places). By global
reciprocity their summed reciprocity values over `S` on `(−1, ε)` are
`(0, 1)` and `(1, 1)` (they are read off at the two real places, where `ε`
is positive at `placePlus` and negative at `placeMinus`), an invertible matrix
over `𝔽₂`.
-/

open NumberField IsDedekindDomain
open scoped NumberField BigOperators

noncomputable section

namespace UnitDistance.Sqrt241.Relation

open ClassFieldTower.Sawin ClassFieldTower.Martinet.Shafarevich ClassFieldTower.ProP
open GlobalClassFieldTheory.Reciprocity Base

local instance characterBH1Module
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod 2) (ContinuousH1ZMod (p := 2) (G := G)) := continuousH1ZModModule

local instance characterBH1AddCommGroup
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    AddCommGroup (ContinuousH1ZMod (p := 2) (G := G)) :=
  ContinuousAddMonoidHom.instAddCommGroup (Additive G) (ZMod 2)

/-! ## The ideal-square radical of `B` -/

theorem integralUnitToIdealSquareRadical_surjective_B :
    Function.Surjective (integralUnitToIdealNthPowerRadicalQuotient B (2 : ℕ+)) := by
  have hClass : Subsingleton (ClassGroup (𝓞 B)) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq classNumber_eq_one)
  intro x
  have hKer : x ∈ (idealNthPowerRadicalToClassTorsion B (2 : ℕ+)).ker := by
    apply Subtype.ext
    exact hClass.elim _ _
  rw [← range_ordinaryUnitToIdealRadical_eq_ker_toClassTorsion B (2 : ℕ+)] at hKer
  obtain ⟨u, hu⟩ := hKer
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
  exact ⟨v, hu⟩

theorem radicalUnit_mul (u w : (𝓞 B)ˣ) :
    radicalUnit B (u * w) = radicalUnit B u + radicalUnit B w := by
  unfold radicalUnit
  rw [map_mul]
  rfl

theorem radicalUnit_pow (u : (𝓞 B)ˣ) (n : ℕ) :
    radicalUnit B (u ^ n) = n • radicalUnit B u := by
  induction n with
  | zero =>
    rw [pow_zero, zero_nsmul]
    unfold radicalUnit
    rw [map_one]
    rfl
  | succ k ih =>
    rw [pow_succ, radicalUnit_mul, ih, succ_nsmul]

theorem radical_two_nsmul (y : idealPowerRadicalModP B 2) : 2 • y = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 y]
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [h2, zero_smul]

/-- The ideal-square radical of `B` is spanned by the classes of `−1` and `ε`. -/
theorem radical_B (x : idealPowerRadicalModP B 2) :
    ∃ p q : ZMod 2, x = p • radicalUnit B (-1) + q • radicalUnit B epsUnit := by
  obtain ⟨u, hu⟩ := integralUnitToIdealSquareRadical_surjective_B (Additive.toMul x)
  obtain ⟨a, b, -, -, w, rfl⟩ := unit_eq_mul_sq u
  refine ⟨(a : ZMod 2), (b : ZMod 2), ?_⟩
  have hx : x = radicalUnit B ((-1) ^ a * epsUnit ^ b * w ^ 2) := by
    unfold radicalUnit
    rw [hu]
    rfl
  rw [hx, radicalUnit_mul, radicalUnit_mul, radicalUnit_pow, radicalUnit_pow, radicalUnit_pow,
    radical_two_nsmul, add_zero, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

/-! ## The two real places of `B` -/

theorem placePlus_isReal : placePlus.IsReal :=
  InfinitePlace.isReal_mk_iff.mpr complexEmbPlus_isReal

theorem placeMinus_isReal : placeMinus.IsReal :=
  InfinitePlace.isReal_mk_iff.mpr complexEmbMinus_isReal

theorem embedding_of_isReal_placePlus (h : placePlus.IsReal) (x : B) :
    InfinitePlace.embedding_of_isReal h x = embPlus x := by
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply]
  change (InfinitePlace.mk complexEmbPlus).embedding x = _
  rw [InfinitePlace.embedding_mk_eq_of_isReal complexEmbPlus_isReal]
  rfl

theorem embedding_of_isReal_placeMinus (h : placeMinus.IsReal) (x : B) :
    InfinitePlace.embedding_of_isReal h x = embMinus x := by
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply]
  change (InfinitePlace.mk complexEmbMinus).embedding x = _
  rw [InfinitePlace.embedding_mk_eq_of_isReal complexEmbMinus_isReal]
  rfl

theorem sum_infinitePlace_B (f : InfinitePlace B → ZMod 2) :
    ∑ w, f w = f placePlus + f placeMinus := by
  classical
  have huniv : (Finset.univ : Finset (InfinitePlace B)) = {placePlus, placeMinus} := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact infinitePlace_eq w
  rw [huniv, Finset.sum_pair placePlus_ne_placeMinus]

/-! ## The characters of `B(√−1)` and `B(√ε)` -/

theorem coe_neg_one_int : (((-1 : 𝓞 B) : 𝓞 B) : B) = -1 := by
  simp

theorem not_isSquare_neg_one_int : ¬ IsSquare (((-1 : 𝓞 B) : 𝓞 B) : B) := by
  rw [coe_neg_one_int]
  exact not_isSquare_neg_one

/-- The quadratic character of `B(√−1)`. -/
def gammaNegOne : Field.absoluteGaloisGroup B →ₜ* Multiplicative (ZMod 2) :=
  sqrtCharacter (((-1 : 𝓞 B) : 𝓞 B) : B) not_isSquare_neg_one_int

/-- The quadratic character of `B(√ε)`. -/
def gammaEps : Field.absoluteGaloisGroup B →ₜ* Multiplicative (ZMod 2) :=
  sqrtCharacter ((eps : 𝓞 B) : B) not_isSquare_eps

theorem two_mul_unit_not_mem {a : 𝓞 B} (ha : IsUnit a) (v : HeightOneSpectrum (𝓞 B))
    (hv : v ∉ S) : 2 * a ∉ v.asIdeal := by
  intro h
  apply hv
  change (30 : 𝓞 B) ∈ v.asIdeal
  rcases v.isPrime.mem_or_mem h with h2 | ha'
  · have h30 : (30 : 𝓞 B) = 2 * 15 := by norm_num
    rw [h30]
    exact v.asIdeal.mul_mem_right _ h2
  · exact absurd (v.asIdeal.eq_top_of_isUnit_mem ha' ha) v.isPrime.ne_top

theorem gammaNegOne_inertia (v : HeightOneSpectrum (𝓞 B)) (hv : v ∉ S)
    (σ : finitePlaceAbsoluteInertiaSubgroup B v) :
    gammaNegOne (finitePlaceAbsoluteDecompositionInclusion B v σ.1) = 1 :=
  sqrtCharacter_inertia (-1 : 𝓞 B) not_isSquare_neg_one_int v
    (two_mul_unit_not_mem isUnit_one.neg v hv) σ

theorem gammaEps_inertia (v : HeightOneSpectrum (𝓞 B)) (hv : v ∉ S)
    (σ : finitePlaceAbsoluteInertiaSubgroup B v) :
    gammaEps (finitePlaceAbsoluteDecompositionInclusion B v σ.1) = 1 :=
  sqrtCharacter_inertia eps not_isSquare_eps v
    (two_mul_unit_not_mem epsUnit.isUnit v hv) σ

theorem gammaNegOne_infinite (w : InfinitePlace B) (hw : w.IsReal) :
    gammaNegOne (absoluteInfinitePlaceArtinNegOne B w) ≠ 1 := by
  intro h
  have h' := (sqrtCharacter_infinite_eq_one_iff _ not_isSquare_neg_one_int w hw).mp h
  rw [coe_neg_one_int, map_neg, map_one] at h'
  linarith

theorem gammaEps_placePlus :
    gammaEps (absoluteInfinitePlaceArtinNegOne B placePlus) = 1 := by
  apply (sqrtCharacter_infinite_eq_one_iff _ not_isSquare_eps placePlus placePlus_isReal).mpr
  rw [embedding_of_isReal_placePlus]
  exact embPlus_eps_pos

theorem gammaEps_placeMinus :
    gammaEps (absoluteInfinitePlaceArtinNegOne B placeMinus) ≠ 1 := by
  intro h
  have h' := (sqrtCharacter_infinite_eq_one_iff _ not_isSquare_eps placeMinus
    placeMinus_isReal).mp h
  rw [embedding_of_isReal_placeMinus] at h'
  linarith [embMinus_eps_neg]

/-! ## Summed reciprocity values on `S` -/

/-- The summed reciprocity value over `SFin` of a global character unramified
outside `S` on the class of a unit, read off at the two real places. -/
theorem sum_SFin_localRadicalValueAt (γ : Field.absoluteGaloisGroup B →ₜ* Multiplicative (ZMod 2))
    (hγ : ∀ v : HeightOneSpectrum (𝓞 B), v ∉ S →
      ∀ σ : finitePlaceAbsoluteInertiaSubgroup B v,
        γ (finitePlaceAbsoluteDecompositionInclusion B v σ.1) = 1)
    (u : (𝓞 B)ˣ) :
    ∑ v : ↥SFin, localRadicalValueAt B v.1
        (h1OfCharacter (γ.comp (finitePlaceAbsoluteDecompositionInclusion B v.1)))
        (radicalUnit B u) =
      (if embPlus ((u : 𝓞 B) : B) < 0 then
          (γ (absoluteInfinitePlaceArtinNegOne B placePlus)).toAdd else 0) +
        (if embMinus ((u : 𝓞 B) : B) < 0 then
          (γ (absoluteInfinitePlaceArtinNegOne B placeMinus)).toAdd else 0) := by
  rw [sum_localRadicalValueAt_unit B SFin γ
    (fun v hv σ => hγ v (fun h => hv ((mem_SFin_iff v).mpr h)) σ) u, sum_infinitePlace_B,
    embedding_of_isReal_placePlus, embedding_of_isReal_placeMinus]
  rfl

theorem embPlus_neg_one_lt : embPlus (((-1 : (𝓞 B)ˣ) : 𝓞 B) : B) < 0 := by
  have h : (((-1 : (𝓞 B)ˣ) : 𝓞 B) : B) = -1 := by
    rw [Units.val_neg, Units.val_one, coe_neg_one_int]
  rw [h, map_neg, map_one]
  norm_num

theorem embMinus_neg_one_lt : embMinus (((-1 : (𝓞 B)ˣ) : 𝓞 B) : B) < 0 := by
  have h : (((-1 : (𝓞 B)ˣ) : 𝓞 B) : B) = -1 := by
    rw [Units.val_neg, Units.val_one, coe_neg_one_int]
  rw [h, map_neg, map_one]
  norm_num

theorem mNegOne_negOne :
    ∑ v : ↥SFin, localRadicalValueAt B v.1
        (h1OfCharacter (gammaNegOne.comp (finitePlaceAbsoluteDecompositionInclusion B v.1)))
        (radicalUnit B (-1)) = 0 := by
  rw [sum_SFin_localRadicalValueAt gammaNegOne gammaNegOne_inertia, ite_eq_left embPlus_neg_one_lt,
    ite_eq_left embMinus_neg_one_lt,
    multiplicativeZModTwo_toAdd_of_ne_one (gammaNegOne_infinite placePlus placePlus_isReal),
    multiplicativeZModTwo_toAdd_of_ne_one (gammaNegOne_infinite placeMinus placeMinus_isReal)]
  decide

theorem mNegOne_eps :
    ∑ v : ↥SFin, localRadicalValueAt B v.1
        (h1OfCharacter (gammaNegOne.comp (finitePlaceAbsoluteDecompositionInclusion B v.1)))
        (radicalUnit B epsUnit) = 1 := by
  rw [sum_SFin_localRadicalValueAt gammaNegOne gammaNegOne_inertia, coe_epsUnit,
    ite_eq_right (not_lt.mpr embPlus_eps_pos.le), ite_eq_left embMinus_eps_neg,
    multiplicativeZModTwo_toAdd_of_ne_one (gammaNegOne_infinite placeMinus placeMinus_isReal)]
  decide

theorem mEps_negOne :
    ∑ v : ↥SFin, localRadicalValueAt B v.1
        (h1OfCharacter (gammaEps.comp (finitePlaceAbsoluteDecompositionInclusion B v.1)))
        (radicalUnit B (-1)) = 1 := by
  rw [sum_SFin_localRadicalValueAt gammaEps gammaEps_inertia, ite_eq_left embPlus_neg_one_lt,
    ite_eq_left embMinus_neg_one_lt, gammaEps_placePlus,
    multiplicativeZModTwo_toAdd_of_ne_one gammaEps_placeMinus]
  decide

theorem mEps_eps :
    ∑ v : ↥SFin, localRadicalValueAt B v.1
        (h1OfCharacter (gammaEps.comp (finitePlaceAbsoluteDecompositionInclusion B v.1)))
        (radicalUnit B epsUnit) = 1 := by
  rw [sum_SFin_localRadicalValueAt gammaEps gammaEps_inertia, coe_epsUnit,
    ite_eq_right (not_lt.mpr embPlus_eps_pos.le), ite_eq_left embMinus_eps_neg,
    multiplicativeZModTwo_toAdd_of_ne_one gammaEps_placeMinus]
  decide

/-! ## The corrected family and the character -/

theorem zmod_two_correction (p q s t : ZMod 2) :
    p * (s + (t + s) * 0 + s * 1) + q * (t + (t + s) * 1 + s * 1) = 0 := by
  revert p q s t
  decide

/-- **Prescribed quadratic inertia** (via the ideal-square radical). Every finite family
of local quadratic characters of `B` is realized on inertia outside `S` by a global
quadratic character unramified outside the family and `S`. -/
theorem prescribedQuadraticInertia_B : PrescribedQuadraticInertia B S := by
  classical
  intro S' χ
  let U : Finset (HeightOneSpectrum (𝓞 B)) := S' ∪ SFin
  let bχ : ∀ v : HeightOneSpectrum (𝓞 B),
      ContinuousH1ZMod (p := 2) (G := finitePlaceAbsoluteDecompositionGroup B v) :=
    fun v => if hv : v ∈ S' then h1OfCharacter (χ ⟨v, hv⟩) else 0
  let n₁ : ∀ v : HeightOneSpectrum (𝓞 B),
      ContinuousH1ZMod (p := 2) (G := finitePlaceAbsoluteDecompositionGroup B v) :=
    fun v => h1OfCharacter (gammaNegOne.comp (finitePlaceAbsoluteDecompositionInclusion B v))
  let nε : ∀ v : HeightOneSpectrum (𝓞 B),
      ContinuousH1ZMod (p := 2) (G := finitePlaceAbsoluteDecompositionGroup B v) :=
    fun v => h1OfCharacter (gammaEps.comp (finitePlaceAbsoluteDecompositionInclusion B v))
  let c : idealPowerRadicalModP B 2 → ZMod 2 :=
    fun r => ∑ v ∈ U, localRadicalValueAt B v (bχ v) r
  let a : ZMod 2 := c (radicalUnit B epsUnit) + c (radicalUnit B (-1))
  let b : ZMod 2 := c (radicalUnit B (-1))
  let fχ : ∀ v : HeightOneSpectrum (𝓞 B),
      ContinuousH1ZMod (p := 2) (G := finitePlaceAbsoluteDecompositionGroup B v) :=
    fun v => if v ∈ SFin then bχ v + (a • n₁ v + b • nε v) else bχ v
  let ψ : ∀ v : ↥U, finitePlaceAbsoluteDecompositionGroup B v.1 →ₜ*
      Multiplicative (ZMod 2) := fun v => characterOfH1 (fχ v.1)
  have hRoundTrip : ∀ v : ↥U, h1OfCharacter (ψ v) = fχ v.1 := by
    intro v
    ext σ
    rfl
  have hexp : ∀ (v : HeightOneSpectrum (𝓞 B)) (r : idealPowerRadicalModP B 2),
      localRadicalValueAt B v (fχ v) r = localRadicalValueAt B v (bχ v) r +
        if v ∈ SFin then a * localRadicalValueAt B v (n₁ v) r +
          b * localRadicalValueAt B v (nε v) r else 0 := by
    intro v r
    change localRadicalValueAt B v
      (if v ∈ SFin then bχ v + (a • n₁ v + b • nε v) else bχ v) r = _
    split_ifs
    · rw [localRadicalValueAt_add, localRadicalValueAt_add, localRadicalValueAt_smul,
        localRadicalValueAt_smul]
    · rw [add_zero]
  have hsum : ∀ r : idealPowerRadicalModP B 2,
      ∑ v : ↥U, localRadicalValueAt B v.1 (h1OfCharacter (ψ v)) r =
        c r + a * (∑ v : ↥SFin, localRadicalValueAt B v.1 (n₁ v.1) r) +
          b * (∑ v : ↥SFin, localRadicalValueAt B v.1 (nε v.1) r) := by
    intro r
    simp_rw [hRoundTrip]
    rw [Finset.sum_coe_sort U (fun v => localRadicalValueAt B v (fχ v) r)]
    simp_rw [hexp]
    rw [Finset.sum_add_distrib, add_assoc]
    congr 1
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_right,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_coe_sort SFin (fun v => localRadicalValueAt B v (n₁ v) r),
      Finset.sum_coe_sort SFin (fun v => localRadicalValueAt B v (nε v) r)]
  have hψ : absolutePowerClassDualRestriction B 2
      (finiteSupportLocalReciprocityPowerClassFunctional B 2 U
        (fun v => finitePlaceDecompositionH1ToAdic B 2 v.1 (h1OfCharacter (ψ v)))) = 0 := by
    apply LinearMap.ext
    intro x
    obtain ⟨p, q, rfl⟩ := radical_B x
    rw [map_add, map_smul, map_smul, radicalFamily_eq_sum, radicalFamily_eq_sum, hsum, hsum,
      mNegOne_negOne, mNegOne_eps, mEps_negOne, mEps_eps, LinearMap.zero_apply,
      smul_eq_mul, smul_eq_mul]
    exact zmod_two_correction p q _ _
  obtain ⟨γ, hInside, hOutside⟩ :=
    exists_absoluteCharacter_of_finiteSupport_radical_annihilator B (2 : ℕ+) U ψ hψ
  refine ⟨γ, ?_, ?_⟩
  · intro v hvT σ
    have hvU : v.1 ∈ U := Finset.mem_union_left SFin v.2
    have hvS : v.1 ∉ SFin := fun h => hvT ((mem_SFin_iff v.1).mp h)
    have h := hInside ⟨v.1, hvU⟩ σ
    have hψv : ψ ⟨v.1, hvU⟩ = χ v := by
      apply ContinuousMonoidHom.ext
      intro τ
      change Multiplicative.ofAdd ((fχ v.1) (Additive.ofMul τ)) = χ v τ
      have hf : fχ v.1 = h1OfCharacter (χ v) := by
        change (if v.1 ∈ SFin then bχ v.1 + (a • n₁ v.1 + b • nε v.1) else bχ v.1) = _
        rw [ite_eq_right hvS]
        simp only [bχ, dite_eq_left v.2]
      rw [hf]
      rfl
    rw [hψv] at h
    exact h
  · intro v hvS' hvT σ
    have hvU : v ∉ U := by
      rw [Finset.mem_union, not_or]
      exact ⟨hvS', fun h => hvT ((mem_SFin_iff v).mp h)⟩
    exact hOutside v hvU σ

end UnitDistance.Sqrt241.Relation
