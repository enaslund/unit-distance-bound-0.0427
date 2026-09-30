module

public import UnitDistance.PairMassDegree12Certificate

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact arithmetic reduction of the degree-12 pair-mass certificate

The beta moments on the eighth-grid are bilinear in the nine endpoint
`6/5`-powers.  This module performs that reduction without approximating any
real power.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Set

namespace UnitDistance.Witness

def pairMassEndpointRoot (k : ℕ) : ℝ := ((k : ℝ) / 8) ^ (6 / 5 : ℝ)

def pairMassRationalMoment (i : Fin 8) (n : ℕ) : ℝ :=
  (6 : ℝ) / (6 + 5 * n) *
    (((((i : ℕ) + 1 : ℝ) / 8) ^ n) * pairMassEndpointRoot ((i : ℕ) + 1) -
      (((i : ℕ) : ℝ) / 8) ^ n * pairMassEndpointRoot (i : ℕ))

 theorem pairMass_beta_moment_eq (i : Fin 8) (n : ℕ) :
    (6 / 5 : ℝ) *
        (((((i : ℕ) + 1 : ℝ) / 8) ^ ((6 / 5 : ℝ) + n) -
          (((i : ℕ) : ℝ) / 8) ^ ((6 / 5 : ℝ) + n)) /
          ((6 / 5 : ℝ) + n)) =
      pairMassRationalMoment i n := by
  unfold pairMassRationalMoment pairMassEndpointRoot
  rw [Real.rpow_add_of_nonneg (by positivity) (by norm_num) (by positivity),
    Real.rpow_natCast,
    Real.rpow_add_of_nonneg (by positivity) (by norm_num) (by positivity),
    Real.rpow_natCast]
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

def pairMassCellRationalContraction (i j : Fin 8) : ℝ :=
  ∑ ab ∈ nestedSupport (pairMassCellBracket i j),
    nestedCoeff (pairMassCellBracket i j) ab.1 ab.2 *
      pairMassRationalMoment i ab.1 * pairMassRationalMoment j ab.2

theorem pairMassCellContraction_eq_rational (i j : Fin 8) :
    pairMassCellContraction i j = pairMassCellRationalContraction i j := by
  unfold pairMassCellContraction pairMassCellRationalContraction
  apply Finset.sum_congr rfl
  intro ab hab
  rw [pairMass_beta_moment_eq i ab.1, pairMass_beta_moment_eq j ab.2]

end UnitDistance.Witness

namespace UnitDistance.Witness

/-- Both coordinate degrees of a nested bivariate polynomial are at most `n`. -/
def PairBidegreeLE (P : Polynomial (Polynomial ℝ)) (n : ℕ) : Prop :=
  P.natDegree ≤ n ∧ ∀ i, (P.coeff i).natDegree ≤ n

private theorem pair_natDegree_finset_sum_le {α : Type*} (s : Finset α)
    (f : α → Polynomial ℝ) (n : ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ n) :
    (∑ i ∈ s, f i).natDegree ≤ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le (h a (by simp)) (ih (by aesop)))

private theorem PairBidegreeLE.mono {P : Polynomial (Polynomial ℝ)} {m n : ℕ}
    (h : PairBidegreeLE P m) (hmn : m ≤ n) : PairBidegreeLE P n :=
  ⟨h.1.trans hmn, fun i => (h.2 i).trans hmn⟩

private theorem PairBidegreeLE.add {P Q : Polynomial (Polynomial ℝ)} {n : ℕ}
    (hP : PairBidegreeLE P n) (hQ : PairBidegreeLE Q n) :
    PairBidegreeLE (P + Q) n := by
  constructor
  · exact (Polynomial.natDegree_add_le P Q).trans (max_le hP.1 hQ.1)
  · intro i
    rw [Polynomial.coeff_add]
    exact (Polynomial.natDegree_add_le _ _).trans (max_le (hP.2 i) (hQ.2 i))

private theorem PairBidegreeLE.neg {P : Polynomial (Polynomial ℝ)} {n : ℕ}
    (hP : PairBidegreeLE P n) : PairBidegreeLE (-P) n := by
  constructor
  · simpa using hP.1
  · intro i
    simpa using hP.2 i

private theorem PairBidegreeLE.finset_sum {α : Type*} (s : Finset α)
    (f : α → Polynomial (Polynomial ℝ)) (n : ℕ)
    (h : ∀ i ∈ s, PairBidegreeLE (f i) n) :
    PairBidegreeLE (∑ i ∈ s, f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      constructor <;> simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (by simp)).add (ih (by aesop))

private theorem PairBidegreeLE.mul {P Q : Polynomial (Polynomial ℝ)} {m n : ℕ}
    (hP : PairBidegreeLE P m) (hQ : PairBidegreeLE Q n) :
    PairBidegreeLE (P * Q) (m + n) := by
  constructor
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hP.1 hQ.1)
  · intro k
    rw [Polynomial.coeff_mul]
    apply pair_natDegree_finset_sum_le
    intro ij hij
    exact Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add (hP.2 ij.1) (hQ.2 ij.2))

private theorem PairBidegreeLE.pow {P : Polynomial (Polynomial ℝ)} {n : ℕ}
    (hP : PairBidegreeLE P n) (k : ℕ) : PairBidegreeLE (P ^ k) (k * n) := by
  induction k with
  | zero =>
      constructor
      · simp
      · intro i
        simp only [pow_zero, Polynomial.coeff_one]
        split_ifs <;> simp
  | succ k ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.mul hP

private theorem PairBidegreeLE.C_mul_X_pow {A : Polynomial ℝ} {i n : ℕ}
    (hA : A.natDegree ≤ n) (hi : i ≤ n) :
    PairBidegreeLE (Polynomial.C A * Polynomial.X ^ i) n := by
  constructor
  · exact (Polynomial.natDegree_C_mul_X_pow_le A i).trans hi
  · intro k
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs <;> simp_all

private theorem PairBidegreeLE.const (c : ℝ) (n : ℕ) :
    PairBidegreeLE (Polynomial.C (Polynomial.C c)) n := by
  simpa using PairBidegreeLE.C_mul_X_pow
    (A := Polynomial.C c) (i := 0) (n := n) (by simp) (Nat.zero_le n)

theorem pairNestedPolynomial_bidegree : PairBidegreeLE pairNestedPolynomial 3 := by
  unfold pairNestedPolynomial
  apply PairBidegreeLE.finset_sum
  intro i hi
  apply PairBidegreeLE.C_mul_X_pow
  · apply pair_natDegree_finset_sum_le
    intro j hj
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · omega

theorem centeredPairPolynomial_bidegree (h : ℝ) :
    PairBidegreeLE (centeredPairPolynomial h) 3 := by
  unfold centeredPairPolynomial
  rw [sub_eq_add_neg]
  have hs : PairBidegreeLE (Polynomial.C (Polynomial.C h⁻¹)) 0 :=
    PairBidegreeLE.const _ _
  have hm := pairNestedPolynomial_bidegree.mul hs
  have h1 : PairBidegreeLE (1 : Polynomial (Polynomial ℝ)) 3 := by
    simpa using PairBidegreeLE.const 1 3
  simpa using hm.add h1.neg

theorem pairCellBracket_bidegree (h rho : ℝ) (N : ℕ) :
    PairBidegreeLE (pairCellBracketPolynomial h rho N) (3 * N) := by
  unfold pairCellBracketPolynomial pairBinomialPolynomial
  apply PairBidegreeLE.add
  · apply PairBidegreeLE.finset_sum
    intro k hk
    have hkN : k ≤ N := by simp only [Finset.mem_range] at hk; omega
    have hc : PairBidegreeLE
        (Polynomial.C (Polynomial.C (Ring.choose p k))) 0 :=
      PairBidegreeLE.const _ _
    exact (hc.mul ((centeredPairPolynomial_bidegree h).pow k)).mono (by omega)
  · exact PairBidegreeLE.const _ _

theorem pairMassCellBracket_bidegree (h rho : ℝ) :
    PairBidegreeLE (pairCellBracketPolynomial h rho 12) 36 := by
  simpa using pairCellBracket_bidegree h rho 12

def pairNestedRectangleSupport (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N).product (Finset.range N)

theorem bivariatePolynomial_pairNestedRectangleSupport
    (P : Polynomial (Polynomial ℝ)) (N : ℕ) (hout : P.natDegree < N)
    (hin : ∀ i, (P.coeff i).natDegree < N) (t u : ℝ) :
    bivariatePolynomial (pairNestedRectangleSupport N) (nestedCoeff P) t u =
      (P.eval (Polynomial.C t)).eval u := by
  conv_rhs => rw [P.as_sum_range_C_mul_X_pow' hout]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  unfold bivariatePolynomial pairNestedRectangleSupport nestedCoeff
  rw [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(P.coeff i).as_sum_range_C_mul_X_pow' (hin i)]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

def pairMassCellRangeContraction (i j : Fin 8) : ℝ :=
  betaMonomialRectangleContraction (6 / 5 : ℝ)
    ((i : ℝ) / 8) (((i : ℕ) + 1 : ℝ) / 8)
    ((j : ℝ) / 8) (((j : ℕ) + 1 : ℝ) / 8)
    (pairNestedRectangleSupport 37)
    (nestedCoeff (pairMassCellBracket i j))

theorem pairMassCellContraction_eq_range (i j : Fin 8) :
    pairMassCellContraction i j = pairMassCellRangeContraction i j := by
  have hdeg := pairMassCellBracket_bidegree
    (pairMassCellCenter i j) (pairMassCellRadius i j)
  change PairBidegreeLE (pairMassCellBracket i j) 36 at hdeg
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
    hi (by positivity) hj (pairMassCellBracket i j)
  have hr := beta_bivariate_monomial_rectangle_integral
    (q := (6 / 5 : ℝ)) (l := (i : ℝ) / 8)
    (r := ((i : ℕ) + 1 : ℝ) / 8) (b := (j : ℝ) / 8)
    (top := ((j : ℕ) + 1 : ℝ) / 8) (by norm_num) (by positivity)
    hi (by positivity) hj (pairNestedRectangleSupport 37)
    (nestedCoeff (pairMassCellBracket i j))
  have heval := bivariatePolynomial_pairNestedRectangleSupport
    (pairMassCellBracket i j) 37
      (hdeg.1.trans_lt (by norm_num))
      (fun k => (hdeg.2 k).trans_lt (by norm_num))
  rw [show pairMassCellContraction i j =
      betaMonomialRectangleContraction (6 / 5 : ℝ)
        ((i : ℝ) / 8) (((i : ℕ) + 1 : ℝ) / 8)
        ((j : ℝ) / 8) (((j : ℕ) + 1 : ℝ) / 8)
        (nestedSupport (pairMassCellBracket i j))
        (nestedCoeff (pairMassCellBracket i j)) by rfl]
  rw [show pairMassCellRangeContraction i j =
      betaMonomialRectangleContraction (6 / 5 : ℝ)
        ((i : ℝ) / 8) (((i : ℕ) + 1 : ℝ) / 8)
        ((j : ℝ) / 8) (((j : ℕ) + 1 : ℝ) / 8)
        (pairNestedRectangleSupport 37)
        (nestedCoeff (pairMassCellBracket i j)) by rfl]
  rw [← hs, ← hr]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  change betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
      ((pairMassCellBracket i j).eval (Polynomial.C t)).eval u =
    betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
      bivariatePolynomial (pairNestedRectangleSupport 37)
        (nestedCoeff (pairMassCellBracket i j)) t u
  rw [heval]

def pairMassCellRangeRationalContraction (i j : Fin 8) : ℝ :=
  ∑ ab ∈ pairNestedRectangleSupport 37,
    nestedCoeff (pairMassCellBracket i j) ab.1 ab.2 *
      pairMassRationalMoment i ab.1 * pairMassRationalMoment j ab.2

theorem pairMassCellContraction_eq_rangeRational (i j : Fin 8) :
    pairMassCellContraction i j = pairMassCellRangeRationalContraction i j := by
  rw [pairMassCellContraction_eq_range]
  unfold pairMassCellRangeContraction pairMassCellRangeRationalContraction
  apply Finset.sum_congr rfl
  intro ab hab
  rw [pairMass_beta_moment_eq i ab.1, pairMass_beta_moment_eq j ab.2]

end UnitDistance.Witness
