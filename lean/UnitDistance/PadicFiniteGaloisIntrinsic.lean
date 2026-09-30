module

public import UnitDistance.PadicFiniteGaloisValuation
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.Padic.NonarchimedeanLocalField

@[expose] public section
set_option backward.privateInPublic true


/-! Compatibility of the actual complete p-adic valuation with intrinsic local-field valuations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ValuativeRel
namespace UnitDistance.PadicFiniteGalois
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable (p : ℕ) [Fact p.Prime]

theorem base_le_one_iff_intrinsic (x : ℚ_[p]) :
    (base p).valuation x≤1 ↔ (ValuativeRel.valuation ℚ_[p]) x≤1 := by
  change (base p).valuation x≤1 ↔ x∈(ValuativeRel.valuation ℚ_[p]).integer
  rw [LocalFieldTheory.Padic.integer_mem_iff_norm_le_one]
  constructor
  · intro hx
    let a : (base p).valuationSubring := ⟨x,hx⟩
    let z := (padicIntEquivValuationSubring p).symm a
    have hz : (z : ℚ_[p])=x := by
      have he := congrArg (fun b : (base p).valuationSubring => (b : ℚ_[p]))
        ((padicIntEquivValuationSubring p).apply_symm_apply a)
      simpa only [padicIntEquivValuationSubring_coe] using he
    rw [←hz]
    exact z.property
  · intro hx
    let z : ℤ_[p] := ⟨x,hx⟩
    have he := (padicIntEquivValuationSubring p z).property
    change (base p).valuation ((padicIntEquivValuationSubring p z :
      (base p).valuationSubring) : ℚ_[p])≤1 at he
    rw [padicIntEquivValuationSubring_coe] at he
    exact he

variable (L : Type) [Field L] [Algebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation ℚ_[p]) (ValuativeRel.valuation L)]

theorem base_hasIntrinsicExtension : (base p).valuation.HasExtension (ValuativeRel.valuation L) := by
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change (ValuativeRel.valuation L) (algebraMap ℚ_[p] L x)≤1 ↔ (base p).valuation x≤1
  rw [Valuation.HasExtension.val_map_le_one_iff
    (ValuativeRel.valuation ℚ_[p]) (ValuativeRel.valuation L)]
  exact (base_le_one_iff_intrinsic p x).symm

/-- Every intrinsic extension valuation agrees with the actual chosen finite p-adic valuation. -/
theorem target_intrinsicCompatible : (target p L).valuation.Compatible := by
  letI := base_hasIntrinsicExtension p L
  have h := valuation_isEquiv_of_finite_separable (base p) (target p L) (ValuativeRel.valuation L)
  refine ⟨fun x y => ?_⟩
  exact (Valuation.Compatible.vle_iff_le (v:=ValuativeRel.valuation L) x y).trans (h x y).symm

end UnitDistance.PadicFiniteGalois
