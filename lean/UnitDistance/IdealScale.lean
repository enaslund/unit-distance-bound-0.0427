module

public import UnitDistance.EuclideanIdealSeparation

@[expose] public section
set_option backward.privateInPublic true


/-! Exact logarithmic normalization of the ideal-dual separation radius. -/
noncomputable section
open NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors Classical
namespace UnitDistance.EuclideanIdeal
variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- Negative normalized logarithmic norm of the actual fractional ideal. -/
def logarithmicIdealDensity (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  -Real.log (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) /
    (nrComplexPlaces K : ℝ)

/-- The ordinary logarithm of the absolute root discriminant. -/
def logarithmicRootDiscriminant : ℝ :=
  Real.log |(discr K : ℝ)| / (2*(nrComplexPlaces K : ℝ))

/-- The manuscript's scale `2 exp(H/2 - ell)` is exactly the geometric
mean of the proved discriminant product bound, for every actual ideal. -/
theorem dualScale_eq_two_mul_exp (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualScale K I = 2*Real.exp (logarithmicIdealDensity K I/2-
      logarithmicRootDiscriminant K) := by
  have hN : 0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) :=
    Rat.cast_pos.mpr (IdealMinimum.absNorm_pos K I I.ne_zero)
  have hD : 0 < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hd : (nrComplexPlaces K : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast complex_places_pos K)
  unfold dualScale logarithmicIdealDensity logarithmicRootDiscriminant
  rw [Real.rpow_def_of_pos (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_pow, Real.log_sqrt (by positivity), Real.log_mul hN.ne' hD.ne']
  conv_rhs => lhs; rw [← Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

end UnitDistance.EuclideanIdeal
