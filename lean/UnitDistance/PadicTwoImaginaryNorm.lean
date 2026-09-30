module

public import UnitDistance.PadicTwoSumSquares
public import UnitDistance.QuadraticRadicalPresentation
public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant

@[expose] public section
set_option backward.privateInPublic true


/-! The actual norm map of Q₂(i) does not attain minus one. -/
noncomputable section
namespace UnitDistance.PadicTwo
open QuadraticAlgebra KummerInvariant
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

instance neg_one_nonsquare : Fact (Nonsquare (-1 : ℚ_[2])) := ⟨by
  intro x hx
  apply sum_squares_ne_neg_one x 0
  simpa using hx⟩

abbrev ImaginaryField := Extension (-1 : ℚ_[2])

theorem imaginary_norm (z : ImaginaryField) : Algebra.norm ℚ_[2] z=z.re^2+z.im^2 := by
  rw [Algebra.norm_apply]
  change (DistribSMul.toLinearMap ℚ_[2] ImaginaryField z).det=_
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
  simp [QuadraticAlgebra.norm]
  ring

theorem imaginary_norm_ne_neg_one (z : ImaginaryField) : Algebra.norm ℚ_[2] z≠ -1 := by
  rw [imaginary_norm]
  exact sum_squares_ne_neg_one z.re z.im

/-- The obstruction holds for every actual quadratic field with a displayed i. -/
theorem quadratic_norm_ne_neg_one {K : Type*} [Field K] [Algebra ℚ_[2] K]
    (i : K) (hi : i^2= -1) (hd : Module.finrank ℚ_[2] K=2) (z : K) :
    Algebra.norm ℚ_[2] z≠ -1 := by
  let e := QuadraticRadical.equiv (-1 : ℚ_[2]) i (by simpa using hi) hd
  have h := imaginary_norm_ne_neg_one (e.symm z)
  have hn : Algebra.norm ℚ_[2] z=Algebra.norm ℚ_[2] (e.symm z) := by
    simpa only [e.apply_symm_apply] using Algebra.norm_eq_of_algEquiv e (e.symm z)
  rw [hn]
  exact h

end UnitDistance.PadicTwo
