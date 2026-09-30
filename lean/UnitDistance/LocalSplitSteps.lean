module

public import UnitDistance.LocalQuadraticIntegral
public import UnitDistance.LocalValuedHaar

@[expose] public section
set_option backward.privateInPublic true


/-! # Exhaustion of the actual split norm-one group by reciprocal steps

The integer valuation and its unit factor uniquely decompose every nonzero
local-field element. Consequently the reciprocal steps used in the local
integrals exhaust the split quadratic norm-one locus.
-/

noncomputable section
open WithZero

namespace UnitDistance.Local.ValuedHaar

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

/-- Every nonzero element has a unique uniformizer exponent and valuation-one
unit factor, for the actual uniformizer and unit subtype used in the operator. -/
theorem exists_unique_uniformizer_unit (x : K) (hx : x ≠ 0) :
    ∃! p : ℤ × ValuationOneUnits K,
      x = uniformizer K ^ p.1 * (p.2 : K) := by
  have hvx : intValuation K x ≠ 0 := (intValuation K).ne_zero_iff.mpr hx
  let a := (intValuation K x).log
  have hu : intValuation K (uniformizer K ^ a * x) = 1 := by
    rw [map_mul, intValuation_uniformizer_zpow, ← exp_log hvx]
    change exp (-a) * exp a = 1
    rw [← exp_add, neg_add_cancel, exp_zero]
  refine ⟨(-a, ⟨uniformizer K ^ a * x, hu⟩), ?_, ?_⟩
  · dsimp
    rw [← mul_assoc, ← zpow_add₀ (uniformizer_ne_zero K), neg_add_cancel,
      zpow_zero, one_mul]
  · rintro ⟨n, u⟩ hp
    have hn := congrArg (intValuation K) hp
    simp only [map_mul, intValuation_uniformizer_zpow, u.property, mul_one] at hn
    have hn' : n = -a := by
      have hlog := congrArg WithZero.log hn
      simp only [log_exp] at hlog
      dsimp [a]
      omega
    apply Prod.ext hn'
    apply Subtype.ext
    change (u : K) = uniformizer K ^ a * x
    rw [hp, hn', ← mul_assoc, ← zpow_add₀ (uniformizer_ne_zero K), add_neg_cancel,
      zpow_zero, one_mul]

local instance splitMeasurableSpace : MeasurableSpace K := borel K
local instance splitBorelSpace : BorelSpace K := ⟨rfl⟩

/-- The exact reciprocal steps occurring in the local Haar operator
parametrize the entire split quadratic norm-one locus, with no repetitions. -/
theorem norm_one_iff_exists_unique_reciprocal_step (ι : K) (hι : ι ^ 2 = -1)
    (z : QuadraticAlgebra K (-1) 0) :
    Algebra.norm K z = 1 ↔ ∃! p : ℤ × ValuationOneUnits K,
      QuadraticSplit.coordinates ι z = (reciprocalSteps K).step p.1 p.2 := by
  constructor
  · intro hz
    have hq : z.norm = 1 := by
      rw [QuadraticSplit.norm_eq_product hι]
      exact (QuadraticSplit.algebra_norm_eq_product hι z).symm.trans hz
    obtain ⟨t, ht, hc⟩ := (QuadraticSplit.norm_one_iff_reciprocal hι z).mp hq
    obtain ⟨p, hp, huniq⟩ := exists_unique_uniformizer_unit K t ht
    refine ⟨p, ?_, ?_⟩
    · rw [hc]
      apply Prod.ext hp
      change t⁻¹ = uniformizer K ^ (-p.1) * (p.2 : K)⁻¹
      rw [hp, mul_inv_rev, zpow_neg, mul_comm]
    · intro q hq
      apply huniq q
      have hf := congrArg Prod.fst hq
      rw [hc] at hf
      exact hf
  · rintro ⟨p, hp, _⟩
    rw [QuadraticSplit.algebra_norm_eq_product hι, hp]
    change (uniformizer K ^ p.1 * (p.2 : K)) *
      (uniformizer K ^ (-p.1) * (p.2 : K)⁻¹) = 1
    rw [mul_mul_mul_comm, ← zpow_add₀ (uniformizer_ne_zero K), add_neg_cancel,
      zpow_zero, mul_inv_cancel₀ (valuationOneUnits_ne_zero K p.2), one_mul]

end UnitDistance.Local.ValuedHaar
