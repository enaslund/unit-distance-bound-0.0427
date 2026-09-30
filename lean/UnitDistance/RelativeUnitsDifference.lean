module

public import UnitDistance.RelativeUnitsPlacePairs

@[expose] public section
set_option backward.privateInPublic true


/-!
# The paper's actual relative logarithmic difference coordinates

At each complex base place the coordinate is exactly one half the difference
of the two chosen actual extension-place logarithms. On norm-one units it is
the first unweighted logarithm. Its kernel is proved to be actual torsion.
-/

noncomputable section
open scoped NumberField Classical
open NumberField NumberField.InfinitePlace NumberField.Units

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- The half-difference coordinates in `geo:mass`, defined from actual places. -/
def unitDifferenceLog (ι : K ≃ₐ[F] K) :
    Additive (𝓞 K)ˣ →+ ({w : InfinitePlace F // IsComplex w} → ℝ) where
  toFun u w := (Real.log (chosenPlaceAbove (K := K) w.val u.toMul) -
    Real.log ((ι • chosenPlaceAbove (K := K) w.val) u.toMul)) / 2
  map_zero' := by ext w; simp
  map_add' u v := by
    ext w
    simp only [toMul_add, Units.coe_mul, map_mul,
      Real.log_mul (Units.pos_at_place _ _).ne' (Units.pos_at_place _ _).ne', Pi.add_apply]
    ring

/-- The ordinary difference logarithm restricted to actual norm-one units. -/
def relativeDifferenceLog (ι : K ≃ₐ[F] K) :
    Additive (normOneUnits (F := F) (K := K)) →+
      ({w : InfinitePlace F // IsComplex w} → ℝ) :=
  (unitDifferenceLog ι).comp (normOneUnits (F := F) (K := K)).subtype.toAdditive

/-- Relative norm one makes the two actual logarithms opposite. -/
theorem log_pair_sum_normOne (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : InfinitePlace K) (u : normOneUnits (F := F) (K := K)) :
    Real.log (v u.val) + Real.log ((ι • v) u.val) = 0 := by
  have h := log_place_norm_eq_add ι hι v u.val
  rw [show unitNorm (F := F) u.val = 1 from u.prop] at h
  simpa only [Units.coe_one, map_one, Real.log_one] using h.symm

/-- On actual norm-one units the half-difference is precisely the first
unweighted place logarithm, with no factor of two remaining. -/
theorem relativeDifferenceLog_apply (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (u : Additive (normOneUnits (F := F) (K := K)))
    (w : {w : InfinitePlace F // IsComplex w}) :
    relativeDifferenceLog ι u w = Real.log (chosenPlaceAbove (K := K) w.val u.toMul.val) := by
  have h := log_pair_sum_normOne ι hι (chosenPlaceAbove w.val) u.toMul
  change (Real.log (chosenPlaceAbove (K := K) w.val u.toMul.val) -
    Real.log ((ι • chosenPlaceAbove (K := K) w.val) u.toMul.val)) / 2 = _
  linarith

variable [IsTotallyComplex K]

/-- The logarithm at every extension of a real place vanishes on relative units. -/
theorem log_real_place_normOne (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (w : {w : InfinitePlace F // IsReal w}) (u : normOneUnits (F := F) (K := K)) :
    Real.log (chosenPlaceAbove (K := K) w.val u.val) = 0 := by
  have h := log_pair_sum_normOne ι hι (chosenPlaceAbove w.val) u
  rw [involution_smul_eq_of_real_comap ι hι _
    (by rw [chosenPlaceAbove_comap]; exact w.prop)] at h
  linarith

/-- The actual difference coordinates have exactly the torsion kernel.
This uses the proved complete classification of extension places and Kronecker. -/
theorem relativeDifferenceLog_eq_zero_iff (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (u : Additive (normOneUnits (F := F) (K := K))) :
    relativeDifferenceLog ι u = 0 ↔ u.toMul.val ∈ torsion K := by
  constructor
  · intro h
    apply (Units.mem_torsion K).mpr
    intro v
    suffices hv : Real.log (v u.toMul.val) = 0 by
      calc
        v u.toMul.val = Real.exp (Real.log (v u.toMul.val)) :=
          (Real.exp_log (Units.pos_at_place _ _)).symm
        _ = 1 := by rw [hv, Real.exp_zero]
    obtain ⟨a, rfl⟩ := pairedPlace_surjective ι hι v
    rcases a with w | ⟨w, b⟩
    · exact log_real_place_normOne ι hι w u.toMul
    · have hz : Real.log (chosenPlaceAbove (K := K) w.val u.toMul.val) = 0 := by
        rw [← relativeDifferenceLog_apply ι hι]
        exact congrFun h w
      cases b
      · exact hz
      · have hp := log_pair_sum_normOne ι hι (chosenPlaceAbove w.val) u.toMul
        change Real.log ((ι • chosenPlaceAbove (K := K) w.val) u.toMul.val) = 0
        linarith
  · intro h
    ext w
    rw [relativeDifferenceLog_apply ι hι,
      (Units.mem_torsion K).mp h (chosenPlaceAbove w.val), Real.log_one]
    rfl

end UnitDistance.RelativeUnits
