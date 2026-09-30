module

public import UnitDistance.Sqrt241.Witness
public import UnitDistance.PairOverlapCoarseLower

@[expose] public section
set_option backward.privateInPublic true


/-!
# The pair profile of the ℚ(√241) witness is the manuscript's

The witness over `ℚ(√241)` uses the manuscript's `s`, `a` and Bernstein
matrix, so its `pairProfile` and `pairOverlap` are literally the functions of
`UnitDistance.Witness`. This file records these identities and transfers the
verified overlap lower bound `UnitDistance.Witness.pairOverlap_coarse_lower`
(which depends only on `s`, `a` and the Bernstein matrix, not on `p` or `δ`).
It also transfers integrability of real powers of the profile.
-/

noncomputable section
open MeasureTheory

namespace UnitDistance.Sqrt241.Witness

theorem s_eq_manuscript : s = _root_.UnitDistance.Witness.s := rfl

theorem a_eq_manuscript : a = _root_.UnitDistance.Witness.a := rfl

theorem bernsteinCoefficients_eq_manuscript :
    bernsteinCoefficients = _root_.UnitDistance.Witness.bernsteinCoefficients := rfl

theorem bernstein3_eq_manuscript : bernstein3 = _root_.UnitDistance.Witness.bernstein3 := rfl

theorem polynomial_eq_manuscript : polynomial = _root_.UnitDistance.Witness.polynomial := by
  funext t u
  simp only [polynomial, _root_.UnitDistance.Witness.polynomial, bernstein3_eq_manuscript,
    bernsteinCoefficients_eq_manuscript]

theorem pairProfile_eq_manuscript : pairProfile = _root_.UnitDistance.Witness.pairProfile := by
  funext z
  simp only [pairProfile, _root_.UnitDistance.Witness.pairProfile, s_eq_manuscript,
    a_eq_manuscript, polynomial_eq_manuscript]

theorem pairOverlap_eq_manuscript : pairOverlap = _root_.UnitDistance.Witness.pairOverlap := by
  simp only [pairOverlap, _root_.UnitDistance.Witness.pairOverlap, pairProfile_eq_manuscript]

/-- The common `π²/a²` scale of the complex pair mass and overlap. -/
def pairArchScale : ℝ := Real.pi ^ 2 / a ^ 2

theorem pairArchScale_eq_manuscript :
    pairArchScale = _root_.UnitDistance.Witness.pairArchScale := by
  simp only [pairArchScale, _root_.UnitDistance.Witness.pairArchScale, a_eq_manuscript]

theorem pairArchScale_pos : 0 < pairArchScale := by
  rw [pairArchScale_eq_manuscript]
  exact _root_.UnitDistance.Witness.pairArchScale_pos

/-- The normalized overlap lower endpoint of the manuscript,
`348.4186885 ≤ pairOverlap / (π²/a²)`. -/
def pairOverlapNormalizedLower : ℝ := 3484186885 / 10 ^ 7

/-- The verified overlap lower bound of the ℚ development, for the literal
overlap integral of this witness. -/
theorem pairOverlap_lower : pairOverlapNormalizedLower * pairArchScale ≤ pairOverlap := by
  have h := _root_.UnitDistance.Witness.pairOverlap_coarse_lower
  rw [pairOverlap_eq_manuscript, pairArchScale_eq_manuscript]
  simpa [pairOverlapNormalizedLower, _root_.UnitDistance.Witness.coarsePairOverlapLower]
    using h

theorem pairOverlap_pos : 0 < pairOverlap := by
  rw [pairOverlap_eq_manuscript]
  exact _root_.UnitDistance.Witness.pairOverlap_pos

theorem pairProfile_pos (z : ℂ × ℂ) : 0 < pairProfile z := by
  rw [pairProfile_eq_manuscript]
  exact _root_.UnitDistance.Witness.pairProfile_pos z

theorem polynomial_bounds {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 1 ≤ polynomial t u ∧ polynomial t u ≤ 14 := by
  rw [polynomial_eq_manuscript]
  exact _root_.UnitDistance.Witness.polynomial_bounds ht0 ht1 hu0 hu1

theorem exponent_student_integrable : 1 < s * p := by
  norm_num [s, p, increment]

theorem integrable_pairMass : Integrable (fun z : ℂ × ℂ => pairProfile z ^ p) := by
  rw [pairProfile_eq_manuscript]
  exact _root_.UnitDistance.Witness.integrable_pairProfile_rpow witness_basic.2.2.1.le
    exponent_student_integrable

theorem pairMass_pos : 0 < pairMass := by
  unfold pairMass
  apply (integral_pos_iff_support_of_nonneg
    (fun z => (Real.rpow_pos_of_pos (pairProfile_pos z) p).le) integrable_pairMass).mpr
  have hs : Function.support (fun z : ℂ × ℂ => pairProfile z ^ p) = Set.univ := by
    ext z
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (pairProfile_pos z) p).ne'
  rw [hs]
  exact Measure.measure_univ_pos.mpr (NeZero.ne _)

end UnitDistance.Sqrt241.Witness
