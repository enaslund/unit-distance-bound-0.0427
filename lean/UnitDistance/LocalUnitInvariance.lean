module

public import UnitDistance.LocalValuedHaar
public import UnitDistance.LocalShellEnergy
public import Mathlib.Topology.Algebra.Ring.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual valuation-unit transformations preserve normalized additive Haar

Multiplication by a valuation-one element is an additive homeomorphism
preserving the normalization ball. Haar uniqueness therefore proves exact
measure preservation. Equal valuations can be matched by such a map.
-/

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal
namespace UnitDistance.Local.ValuedHaar
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local instance : MeasurableSpace K := borel K
local instance : BorelSpace K := ⟨rfl⟩

def unitMulEquiv (u : ValuationOneUnits K) : K ≃ₜ+ K :=
  ContinuousAddEquiv.mulLeft (Units.mk0 (u : K) (valuationOneUnits_ne_zero K u))

@[simp] theorem unitMulEquiv_apply (u : ValuationOneUnits K) (x : K) :
    unitMulEquiv K u x = (u : K)*x := rfl

theorem unitMulEquiv_preimage_ball (u : ValuationOneUnits K) (a : ℤ) :
    unitMulEquiv K u ⁻¹' (ball K a : Set K) = ball K a := by
  ext x
  exact ball_unit_invariant K a u x

/-- The normalization is the actual additive Haar mass of the valuation ring.
No measure-scaling hypothesis is supplied. -/
theorem unitMulEquiv_measurePreserving (u : ValuationOneUnits K) :
    MeasurePreserving (unitMulEquiv K u) (normalizedHaar K) (normalizedHaar K) := by
  let e := unitMulEquiv K u
  haveI : ((normalizedHaar K).map e).IsAddHaarMeasure := inferInstance
  have hm : (normalizedHaar K).map e (unitBall K) = 1 := by
    change ((normalizedHaar K).map e) (ball K 0 : Set K) = 1
    have he : Measurable (e : K → K) := e.continuous_toFun.measurable
    rw [Measure.map_apply he (ball_clopen K 0).isOpen.measurableSet]
    change (normalizedHaar K) (e ⁻¹' (ball K 0 : Set K)) = 1
    rw [unitMulEquiv_preimage_ball]
    exact Measure.addHaarMeasure_self
  refine ⟨e.continuous_toFun.measurable, ?_⟩
  rw [Measure.addHaarMeasure_unique ((normalizedHaar K).map e) (unitBall K), hm, one_smul]
  rfl

/-- Equal actual integer valuations are related by an actual valuation-one
multiplier. The zero case is included explicitly. -/
theorem exists_unit_mul_of_intValuation_eq {x y : K}
    (h : intValuation K x = intValuation K y) :
    ∃ u : ValuationOneUnits K, (u : K)*x = y := by
  by_cases hx : x = 0
  · have hy : y = 0 := (intValuation K).zero_iff.mp (by simpa only [hx, map_zero] using h.symm)
    exact ⟨⟨1, map_one _⟩, by simp [hx, hy]⟩
  · refine ⟨⟨y/x, ?_⟩, div_mul_cancel₀ y hx⟩
    rw [map_div₀, ← h, div_self ((intValuation K).ne_zero_iff.mpr hx)]

def valuationRotation (x y : K) (h : intValuation K x = intValuation K y) : K ≃ₜ+ K :=
  unitMulEquiv K (exists_unit_mul_of_intValuation_eq K h).choose

@[simp] theorem valuationRotation_apply (x y : K)
    (h : intValuation K x = intValuation K y) : valuationRotation K x y h x = y :=
  (exists_unit_mul_of_intValuation_eq K h).choose_spec

theorem valuationRotation_measurePreserving (x y : K)
    (h : intValuation K x = intValuation K y) :
    MeasurePreserving (valuationRotation K x y h) (normalizedHaar K) (normalizedHaar K) :=
  unitMulEquiv_measurePreserving K _

theorem valuationRotation_preserves_ball (x y : K)
    (h : intValuation K x = intValuation K y) (a : ℤ) (z : K) :
    valuationRotation K x y h z ∈ ball K a ↔ z ∈ ball K a :=
  ball_unit_invariant K a _ z

end UnitDistance.Local.ValuedHaar
