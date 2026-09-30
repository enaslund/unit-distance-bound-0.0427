module

public import UnitDistance.RelativeUnitsCapitulation
public import UnitDistance.InvolutionCohomology
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section
set_option backward.privateInPublic true


/-!
# Herbrand's index formula for actual quadratic number-field units

Both cohomology indices are identified with independently defined arithmetic
groups. Finite unramifiedness is needed only for the capitulation identification.
-/

noncomputable section
open scoped NumberField
open NumberField

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- The actual extension map on integral units. -/
def embeddedUnits : (𝓞 F)ˣ →* (𝓞 K)ˣ :=
  Units.map (algebraMap (𝓞 F) (𝓞 K)).toMonoidHom

omit [NumberField F] [NumberField K] [Algebra.IsQuadraticExtension F K] in
theorem embeddedUnits_injective :
    Function.Injective (embeddedUnits (F := F) (K := K)) :=
  Units.map_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))

/-- The abstract norm is the ordinary unit norm followed by extension. -/
theorem embedded_unitNorm (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (u : (𝓞 K)ˣ) :
    embeddedUnits (F := F) (unitNorm (F := F) u) = u * unitInvolution ι u := by
  apply Units.coe_injective K
  exact norm_eq_mul_involution ι hι (u : K)

theorem plus_unitInvolution (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    InvolutionCohomology.plus (unitInvolution ι).toAdditive =
      (embeddedUnits (F := F) (K := K)).toAdditive.range := by
  ext u
  rw [InvolutionCohomology.mem_plus]
  exact unitInvolution_fixed_iff ι hι u.toMul

theorem minus_unitInvolution (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    InvolutionCohomology.minus (unitInvolution ι).toAdditive =
      (normOneUnits (F := F) (K := K)).toAddSubgroup := by
  ext u
  change u.toMul * unitInvolution ι u.toMul = 1 ↔ _
  exact (mem_normOneUnits_iff ι hι u.toMul).symm

theorem additive_norm_unitInvolution (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    InvolutionCohomology.norm (unitInvolution ι).toAdditive =
      (embeddedUnits (F := F) (K := K)).toAdditive.comp
        (unitNorm (F := F) (K := K)).toAdditive := by
  apply AddMonoidHom.ext
  intro u
  exact (embedded_unitNorm ι hι u.toMul).symm

/-- The norm-side cohomology index is precisely the manuscript's `I_U`. -/
theorem norm_index_eq_unitNorm_index (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    (InvolutionCohomology.norm (unitInvolution ι).toAdditive).range.relIndex
      (InvolutionCohomology.plus (unitInvolution ι).toAdditive) =
        (normUnitImage (F := F) (K := K)).index := by
  rw [additive_norm_unitInvolution ι hι, plus_unitInvolution ι hι,
    AddMonoidHom.range_comp]
  conv_lhs => arg 2; rw [AddMonoidHom.range_eq_map]
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ embeddedUnits_injective]
  simp [normUnitImage]

/-- The boundary-side cohomology index is the cardinality of the actual unit quotient. -/
theorem boundary_index_eq_unitH1_card (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    (InvolutionCohomology.boundary (unitInvolution ι).toAdditive).range.relIndex
      (InvolutionCohomology.minus (unitInvolution ι).toAdditive) =
        Nat.card (UnitH1 ι hι) := by
  have hr : (InvolutionCohomology.boundary (unitInvolution ι).toAdditive).range =
      (((unitCoboundary ι hι).range).map
        (normOneUnits (F := F) (K := K)).subtype).toAddSubgroup := by
    change (((normOneUnits (F := F) (K := K)).subtype.comp
      (unitCoboundary ι hι)).range).toAddSubgroup = _
    rw [MonoidHom.range_comp]
  rw [hr, minus_unitInvolution ι hι, Subgroup.relIndex_toAddSubgroup]
  conv_lhs =>
    arg 2
    rw [← Subgroup.range_subtype (normOneUnits (F := F) (K := K)), MonoidHom.range_eq_map]
  rw [Subgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective,
    Subgroup.relIndex_top_right]
  rfl

/-- The fixed-unit rank is the ordinary Dirichlet rank of the base field. -/
theorem plus_unitInvolution_rank (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Module.finrank ℤ (InvolutionCohomology.plus (unitInvolution ι).toAdditive) =
      Units.rank F := by
  rw [plus_unitInvolution ι hι]
  exact ((AddMonoidHom.ofInjective (f := (embeddedUnits (F := F) (K := K)).toAdditive)
    embeddedUnits_injective).symm.toIntLinearEquiv.finrank_eq).trans
    (Units.finrank_eq F)

/-- Herbrand's quotient formula on actual units, with the norm-one rank still
shown explicitly. No rank, norm-index, or cohomology cardinality is an input. -/
theorem unit_herbrand_rank_index (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    (normUnitImage (F := F) (K := K)).index *
        2 ^ Module.finrank ℤ (Additive (normOneUnits (F := F) (K := K))) =
      Nat.card (UnitH1 ι hι) * 2 ^ Units.rank F := by
  have hi : Function.Involutive (unitInvolution ι).toAdditive := unitInvolution_involutive ι hι
  have h := InvolutionCohomology.herbrand_rank_index (unitInvolution ι).toAdditive hi
  rw [norm_index_eq_unitNorm_index ι hι, boundary_index_eq_unitH1_card ι hι,
    plus_unitInvolution_rank ι hι, minus_unitInvolution ι hι] at h
  exact h

omit [NumberField K] in
/-- The actual norm image has the full Dirichlet rank of the base field. -/
theorem normUnitImage_rank :
    Module.finrank ℤ (Additive (normUnitImage (F := F) (K := K))) = Units.rank F := by
  letI : (normUnitImage (F := F) (K := K)).toAddSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_toAddSubgroup_iff.mpr inferInstance
  exact (InvolutionCohomology.finrank_eq_of_finiteIndex
    (normUnitImage (F := F) (K := K)).toAddSubgroup).trans (Units.finrank_eq F)

/-- Dirichlet and actual norm rank-nullity determine the relative-unit rank. -/
theorem normOneUnits_rank_add_base_rank :
    Module.finrank ℤ (Additive (normOneUnits (F := F) (K := K))) + Units.rank F =
      Units.rank K := by
  have h := InvolutionCohomology.rank_range_add_rank_ker
    (unitNorm (F := F) (K := K)).toAdditive
  change Module.finrank ℤ (Additive (normUnitImage (F := F) (K := K))) +
    Module.finrank ℤ (Additive (normOneUnits (F := F) (K := K))) =
      Module.finrank ℤ (Additive (𝓞 K)ˣ) at h
  rw [normUnitImage_rank, Units.finrank_eq] at h
  exact (Nat.add_comm _ _).trans h

/-- The norm-one rank as a difference of ordinary unit ranks. -/
theorem normOneUnits_rank :
    Module.finrank ℤ (Additive (normOneUnits (F := F) (K := K))) =
      Units.rank K - Units.rank F :=
  Nat.eq_sub_of_add_eq normOneUnits_rank_add_base_rank

variable [IsTotallyComplex K]

/-- In the paper's quadratic signature `(0,b+2c)/(b,c)`, the actual norm-one
unit rank is exactly the number `c` of complex places of the base field. -/
theorem normOneUnits_rank_eq_complex_places :
    Module.finrank ℤ (Additive (normOneUnits (F := F) (K := K))) =
      InfinitePlace.nrComplexPlaces F := by
  have he := Module.finrank_mul_finrank ℚ F K
  rw [Algebra.IsQuadraticExtension.finrank_eq_two F K, IsTotallyComplex.finrank K] at he
  have hf := InfinitePlace.card_add_two_mul_card_eq_rank F
  have hn : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  have hr := normOneUnits_rank_add_base_rank (F := F) (K := K)
  simp only [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add] at hr hn
  omega

/-- Herbrand's exact norm-index formula in the actual field signature. -/
theorem unitNorm_index_eq_unitH1_mul_pow_real_places
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < InfinitePlace.nrRealPlaces F) :
    (normUnitImage (F := F) (K := K)).index =
      Nat.card (UnitH1 ι hι) * 2 ^ (InfinitePlace.nrRealPlaces F - 1) := by
  have h := unit_herbrand_rank_index ι hι
  rw [normOneUnits_rank_eq_complex_places] at h
  have hr : Units.rank F =
      InfinitePlace.nrRealPlaces F - 1 + InfinitePlace.nrComplexPlaces F := by
    rw [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  rw [hr, pow_add, ← mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

/-- The exact arithmetic identity `κ = I_U / 2^(b-1)` in `geo:mass`.
Its hypotheses are ordinary finite unramifiedness and actual field signature;
no cohomology, capitulation, or norm-index identity remains assumed. -/
theorem capitulation_index_formula
    (hunr : NumberFieldAnalysis.FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < InfinitePlace.nrRealPlaces F) :
    Nat.card (CapitulationKernel (F := F) (K := K)) =
      (normUnitImage (F := F) (K := K)).index /
        2 ^ (InfinitePlace.nrRealPlaces F - 1) := by
  rw [unitNorm_index_eq_unitH1_mul_pow_real_places ι hι hb,
    Nat.mul_div_cancel _ (by positivity)]
  exact capitulation_card_eq_unitH1_card hunr ι hι

end UnitDistance.RelativeUnits
