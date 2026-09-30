module

public import UnitDistance.PairMassDegree3Certificate
public import UnitDistance.PairMassDegree12ArithmeticCertificate

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace UnitDistance.Witness

def pairMassCellRangeContraction3 (i j : Fin 8) : ℝ :=
  betaMonomialRectangleContraction (6 / 5 : ℝ)
    ((i : ℝ) / 8) (((i : ℕ) + 1 : ℝ) / 8)
    ((j : ℝ) / 8) (((j : ℕ) + 1 : ℝ) / 8)
    (pairNestedRectangleSupport 10)
    (nestedCoeff (pairMassCellBracket3 i j))

theorem pairMassCellContraction3_eq_range (i j : Fin 8) :
    pairMassCellContraction3 i j = pairMassCellRangeContraction3 i j := by
  have hdeg := pairCellBracket_bidegree
    (pairMassCellCenter i j) (pairMassCellRadius i j) 3
  change PairBidegreeLE (pairMassCellBracket3 i j) 9 at hdeg
  have hi : (i : ℝ) / 8 ≤ ((i : ℕ) + 1 : ℝ) / 8 := by
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 8)).2
    norm_num
  have hj : (j : ℝ) / 8 ≤ ((j : ℕ) + 1 : ℝ) / 8 := by
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 8)).2
    norm_num
  have hs := beta_nestedPolynomial_rectangle_integral
    (q := (6 / 5 : ℝ)) (l := (i : ℝ) / 8)
    (r := ((i : ℕ) + 1 : ℝ) / 8) (b := (j : ℝ) / 8)
    (top := ((j : ℕ) + 1 : ℝ) / 8) (by norm_num) (by positivity)
    hi (by positivity) hj (pairMassCellBracket3 i j)
  have hr := beta_bivariate_monomial_rectangle_integral
    (q := (6 / 5 : ℝ)) (l := (i : ℝ) / 8)
    (r := ((i : ℕ) + 1 : ℝ) / 8) (b := (j : ℝ) / 8)
    (top := ((j : ℕ) + 1 : ℝ) / 8) (by norm_num) (by positivity)
    hi (by positivity) hj (pairNestedRectangleSupport 10)
    (nestedCoeff (pairMassCellBracket3 i j))
  have heval := bivariatePolynomial_pairNestedRectangleSupport
    (pairMassCellBracket3 i j) 10
      (hdeg.1.trans_lt (by norm_num))
      (fun k => (hdeg.2 k).trans_lt (by norm_num))
  unfold pairMassCellContraction3 pairMassCellRangeContraction3
  rw [← hs, ← hr]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  change betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
      ((pairMassCellBracket3 i j).eval (Polynomial.C t)).eval u =
    betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
      bivariatePolynomial (pairNestedRectangleSupport 10)
        (nestedCoeff (pairMassCellBracket3 i j)) t u
  rw [heval]

def pairMassCellRangeRationalContraction3 (i j : Fin 8) : ℝ :=
  ∑ ab ∈ pairNestedRectangleSupport 10,
    nestedCoeff (pairMassCellBracket3 i j) ab.1 ab.2 *
      pairMassRationalMoment i ab.1 * pairMassRationalMoment j ab.2

theorem pairMassCellContraction3_eq_rangeRational (i j : Fin 8) :
    pairMassCellContraction3 i j = pairMassCellRangeRationalContraction3 i j := by
  rw [pairMassCellContraction3_eq_range]
  unfold pairMassCellRangeContraction3 pairMassCellRangeRationalContraction3
  apply Finset.sum_congr rfl
  intro ab hab
  rw [pairMass_beta_moment_eq i ab.1, pairMass_beta_moment_eq j ab.2]

end UnitDistance.Witness
