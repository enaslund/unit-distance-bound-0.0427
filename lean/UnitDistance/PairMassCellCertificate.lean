module

public import UnitDistance.PairBetaMoments
public import UnitDistance.PairBinomialTail
public import UnitDistance.StudentProfiles
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace UnitDistance.Witness

def bernstein2 (i : Fin 3) (t : ℝ) : ℝ :=
  (Nat.choose 2 i : ℝ) * t ^ (i : ℕ) * (1-t) ^ (2 - (i : ℕ))

def bernsteinDerivativeCoefficients : Fin 3 → Fin 4 → ℚ :=
  ![![(14129438977 / 10000000000 : ℚ), 14403544911 / 10000000000,
      18649950909 / 10000000000, 7224685061 / 5000000000],
    ![(3592360233 / 10000000000 : ℚ), 7838766231 / 10000000000,
      1651441793 / 2000000000, 2841095881 / 2000000000],
    ![(39135998851 / 10000000000 : ℚ), 2183463629 / 625000000,
      5110461063 / 1250000000, 21573391511 / 5000000000]]

def polynomialDerivFirst (t u : ℝ) : ℝ :=
  3 * ∑ i : Fin 3, ∑ j : Fin 4,
    (bernsteinDerivativeCoefficients i j : ℝ) *
      bernstein2 i t * bernstein3 j u

theorem bernstein3_hasDerivAt (i : Fin 4) (t : ℝ) :
    HasDerivAt (bernstein3 i) (3 *
      ((if h : (i : ℕ) = 0 then 0 else bernstein2 ⟨(i : ℕ) - 1, by omega⟩ t) -
       (if h : (i : ℕ) = 3 then 0 else bernstein2 ⟨(i : ℕ), by omega⟩ t))) t := by
  fin_cases i
  · norm_num [bernstein3, bernstein2, Nat.choose]
    convert ((hasDerivAt_const t 1).sub (hasDerivAt_id t)).pow 3 using 1
    all_goals first | rfl | (ext y; simp [bernstein3, Function.id_def] <;> ring) |
      (simp [bernstein3, Function.id_def] <;> ring)
  · norm_num [bernstein3, bernstein2, Nat.choose]
    convert ((hasDerivAt_id t).mul (((hasDerivAt_const t 1).sub
      (hasDerivAt_id t)).pow 2)).const_mul 3 using 1
    all_goals first | rfl | (ext y; simp [bernstein3, Function.id_def] <;> ring) |
      (simp [bernstein3, Function.id_def] <;> ring)
  · norm_num [bernstein3, bernstein2, Nat.choose]
    convert (((hasDerivAt_id t).pow 2).mul ((hasDerivAt_const t 1).sub
      (hasDerivAt_id t))).const_mul 3 using 1
    all_goals first | rfl | (ext y; simp [bernstein3, Function.id_def] <;> ring) |
      (simp [bernstein3, Function.id_def] <;> ring)
  · norm_num [bernstein3, bernstein2, Nat.choose]
    convert (hasDerivAt_id t).pow 3 using 1
    all_goals first | rfl | (ext y; simp [bernstein3, Function.id_def] <;> ring) |
      (simp [bernstein3, Function.id_def] <;> ring)

theorem polynomial_hasDerivAt_first (t u : ℝ) :
    HasDerivAt (fun x => polynomial x u) (polynomialDerivFirst t u) t := by
  unfold polynomial
  have h : HasDerivAt
      (fun x => ∑ i : Fin 4, ∑ j : Fin 4,
        (bernsteinCoefficients i j : ℝ) * bernstein3 i x * bernstein3 j u)
      (∑ i : Fin 4, ∑ j : Fin 4,
        (bernsteinCoefficients i j : ℝ) *
          (3 * ((if h : (i : ℕ) = 0 then 0 else
            bernstein2 ⟨(i : ℕ) - 1, by omega⟩ t) -
           (if h : (i : ℕ) = 3 then 0 else
            bernstein2 ⟨(i : ℕ), by omega⟩ t))) * bernstein3 j u) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    apply HasDerivAt.fun_sum
    intro j hj
    exact ((bernstein3_hasDerivAt i t).const_mul
      (bernsteinCoefficients i j : ℝ)).mul_const (bernstein3 j u)
  convert h using 1
  norm_num [polynomialDerivFirst, bernstein2, bernstein3,
    bernsteinDerivativeCoefficients, bernsteinCoefficients, Fin.sum_univ_succ, Nat.choose]
  ring

theorem bernstein2_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin 3) :
    0 ≤ bernstein2 i t := by
  unfold bernstein2
  positivity

theorem polynomialDerivFirst_nonneg {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ polynomialDerivFirst t u := by
  unfold polynomialDerivFirst
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  have hc : (0 : ℝ) ≤ (bernsteinDerivativeCoefficients i j : ℝ) := by
    fin_cases i <;> fin_cases j <;> norm_num [bernsteinDerivativeCoefficients]
  exact mul_nonneg (mul_nonneg hc (bernstein2_nonneg ht0 ht1 i))
    (bernstein3_nonneg hu0 hu1 j)

theorem polynomial_monotone_first {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    MonotoneOn (fun t => polynomial t u) (Icc (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
  · unfold polynomial bernstein3
    fun_prop
  · unfold polynomial bernstein3
    fun_prop
  · intro t ht
    rw [(polynomial_hasDerivAt_first t u).deriv]
    have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    exact polynomialDerivFirst_nonneg ht'.1 ht'.2 hu0 hu1

theorem polynomial_comm (t u : ℝ) : polynomial t u = polynomial u t := by
  norm_num [polynomial, bernstein3, bernsteinCoefficients, Fin.sum_univ_succ, Nat.choose]
  ring

theorem polynomial_monotone_second {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MonotoneOn (fun u => polynomial t u) (Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  change polynomial t u ≤ polynomial t v
  rw [polynomial_comm t u, polynomial_comm t v]
  exact polynomial_monotone_first ht0 ht1 hu hv huv

theorem polynomial_cell_bounds {l r b top x y : ℝ}
    (hl : 0 ≤ l) (hlx : l ≤ x) (hxr : x ≤ r) (hr : r ≤ 1)
    (hb : 0 ≤ b) (hby : b ≤ y) (hyt : y ≤ top) (htop : top ≤ 1) :
    polynomial l b ≤ polynomial x y ∧ polynomial x y ≤ polynomial r top := by
  have hl1 : l ≤ 1 := (hlx.trans hxr).trans hr
  have hx0 : 0 ≤ x := hl.trans hlx
  have hx1 : x ≤ 1 := hxr.trans hr
  have hr0 : 0 ≤ r := hl.trans (hlx.trans hxr)
  have hy0 : 0 ≤ y := hb.trans hby
  have hy1 : y ≤ 1 := hyt.trans htop
  have ht0 : 0 ≤ top := hb.trans (hby.trans hyt)
  constructor
  · exact (polynomial_monotone_second hl hl1 ⟨hb, hby.trans hy1⟩ ⟨hy0, hy1⟩ hby).trans
      (polynomial_monotone_first hy0 hy1 ⟨hl, hl1⟩ ⟨hx0, hx1⟩ hlx)
  · exact (polynomial_monotone_first hy0 hy1 ⟨hx0, hx1⟩ ⟨hr0, hr⟩ hxr).trans
      (polynomial_monotone_second hr0 hr ⟨hy0, hy1⟩ ⟨ht0, htop⟩ hyt)

def nestedSupport (P : Polynomial (Polynomial ℝ)) : Finset (ℕ × ℕ) :=
  (P.support.sigma fun i => (P.coeff i).support).image fun ij => (ij.1, ij.2)

def nestedCoeff (P : Polynomial (Polynomial ℝ)) (i j : ℕ) : ℝ :=
  (P.coeff i).coeff j

theorem bivariatePolynomial_nestedSupport (P : Polynomial (Polynomial ℝ)) (t u : ℝ) :
    bivariatePolynomial (nestedSupport P) (nestedCoeff P) t u =
      (P.eval (Polynomial.C t)).eval u := by
  rw [show P.eval (Polynomial.C t) = P.sum (fun e a => a * Polynomial.C t ^ e) from
    Polynomial.eval_eq_sum]
  simp only [Polynomial.sum, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C]
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  unfold bivariatePolynomial nestedSupport nestedCoeff
  have hinj : Function.Injective
      (fun ij : Sigma (fun _ : ℕ => ℕ) => (ij.1, ij.2)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  rw [Finset.sum_image hinj.injOn]
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact contraction of a monomial polynomial on a rectangle, using the
original coordinates rather than normalized cell coordinates. -/
def betaMonomialRectangleContraction (q l r b top : ℝ)
    (S : Finset (ℕ × ℕ)) (c : ℕ → ℕ → ℝ) : ℝ :=
  ∑ ij ∈ S, c ij.1 ij.2 *
    (q * ((r ^ (q + ij.1) - l ^ (q + ij.1)) / (q + ij.1))) *
    (q * ((top ^ (q + ij.2) - b ^ (q + ij.2)) / (q + ij.2)))

theorem beta_bivariate_monomial_rectangle_integral {q l r b top : ℝ}
    (hq : 0 < q) (hl : 0 ≤ l) (hlr : l ≤ r) (hb : 0 ≤ b) (hbt : b ≤ top)
    (S : Finset (ℕ × ℕ)) (c : ℕ → ℕ → ℝ) :
    (∫ x in Icc l r, ∫ y in Icc b top,
      betaDensity q x * betaDensity q y * bivariatePolynomial S c x y) =
      betaMonomialRectangleContraction q l r b top S c := by
  have hinner (x : ℝ) :
      (∫ y in Icc b top,
        betaDensity q x * betaDensity q y * bivariatePolynomial S c x y) =
      ∑ ij ∈ S, (betaDensity q x * (c ij.1 ij.2 * x ^ ij.1)) *
        (q * ((top ^ (q + ij.2) - b ^ (q + ij.2)) / (q + ij.2))) := by
    rw [show (fun y : ℝ =>
        betaDensity q x * betaDensity q y * bivariatePolynomial S c x y) =
      (fun y : ℝ => ∑ ij ∈ S,
        (betaDensity q x * (c ij.1 ij.2 * x ^ ij.1)) *
          (betaDensity q y * y ^ ij.2)) by
        funext y
        simp only [bivariatePolynomial, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ij hij
        ring]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro ij hij
      rw [integral_const_mul, beta_monomial_interval_moment hq hb hbt]
    · intro ij hij
      exact (integrableOn_beta_monomial_interval hq hbt ij.2).const_mul _
  calc
    (∫ x in Icc l r, ∫ y in Icc b top,
      betaDensity q x * betaDensity q y * bivariatePolynomial S c x y) =
        ∫ x in Icc l r, ∑ ij ∈ S,
          (c ij.1 ij.2 *
            (q * ((top ^ (q + ij.2) - b ^ (q + ij.2)) / (q + ij.2)))) *
            (betaDensity q x * x ^ ij.1) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change (∫ y in Icc b top,
        betaDensity q x * betaDensity q y * bivariatePolynomial S c x y) = _
      rw [hinner]
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ∑ ij ∈ S, ∫ x in Icc l r,
        (c ij.1 ij.2 *
          (q * ((top ^ (q + ij.2) - b ^ (q + ij.2)) / (q + ij.2)))) *
          (betaDensity q x * x ^ ij.1) := by
      rw [integral_finsetSum]
      intro ij hij
      exact (integrableOn_beta_monomial_interval hq hlr ij.1).const_mul _
    _ = betaMonomialRectangleContraction q l r b top S c := by
      unfold betaMonomialRectangleContraction
      apply Finset.sum_congr rfl
      intro ij hij
      rw [integral_const_mul, beta_monomial_interval_moment hq hl hlr]
      ring

theorem beta_nestedPolynomial_rectangle_integral {q l r b top : ℝ}
    (hq : 0 < q) (hl : 0 ≤ l) (hlr : l ≤ r) (hb : 0 ≤ b) (hbt : b ≤ top)
    (P : Polynomial (Polynomial ℝ)) :
    (∫ x in Icc l r, ∫ y in Icc b top,
      betaDensity q x * betaDensity q y * (P.eval (Polynomial.C x)).eval y) =
      betaMonomialRectangleContraction q l r b top
        (nestedSupport P) (nestedCoeff P) := by
  rw [← beta_bivariate_monomial_rectangle_integral hq hl hlr hb hbt]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  change betaDensity q x * betaDensity q y * (P.eval (Polynomial.C x)).eval y =
    betaDensity q x * betaDensity q y *
      bivariatePolynomial (nestedSupport P) (nestedCoeff P) x y
  rw [bivariatePolynomial_nestedSupport]

theorem integrableOn_beta_nestedPolynomial_inner {q b top : ℝ}
    (hq : 0 < q) (hbt : b ≤ top) (P : Polynomial (Polynomial ℝ)) (x : ℝ) :
    IntegrableOn (fun y => betaDensity q x * betaDensity q y *
      (P.eval (Polynomial.C x)).eval y) (Icc b top) := by
  have heq : (fun y => betaDensity q x * betaDensity q y *
      (P.eval (Polynomial.C x)).eval y) =
      (fun y => betaDensity q x * betaDensity q y *
        bivariatePolynomial (nestedSupport P) (nestedCoeff P) x y) := by
    funext y
    rw [bivariatePolynomial_nestedSupport]
  rw [heq]
  unfold bivariatePolynomial
  rw [show (fun y => betaDensity q x * betaDensity q y *
      ∑ ij ∈ nestedSupport P, nestedCoeff P ij.1 ij.2 * x ^ ij.1 * y ^ ij.2) =
      (fun y => ∑ ij ∈ nestedSupport P,
        (betaDensity q x * (nestedCoeff P ij.1 ij.2 * x ^ ij.1)) *
          (betaDensity q y * y ^ ij.2)) by
      funext y
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ij hij
      ring]
  apply integrable_finset_sum
  intro ij hij
  exact (integrableOn_beta_monomial_interval hq hbt ij.2).const_mul _

theorem integrableOn_beta_nestedPolynomial_outer {q l r b top : ℝ}
    (hq : 0 < q) (hlr : l ≤ r) (hb : 0 ≤ b) (hbt : b ≤ top)
    (P : Polynomial (Polynomial ℝ)) :
    IntegrableOn (fun x => ∫ y in Icc b top,
      betaDensity q x * betaDensity q y *
        (P.eval (Polynomial.C x)).eval y) (Icc l r) := by
  have hinner (x : ℝ) :
      (∫ y in Icc b top, betaDensity q x * betaDensity q y *
        (P.eval (Polynomial.C x)).eval y) =
      ∑ ij ∈ nestedSupport P,
        (betaDensity q x * (nestedCoeff P ij.1 ij.2 * x ^ ij.1)) *
          (q * ((top ^ (q + ij.2) - b ^ (q + ij.2)) / (q + ij.2))) := by
    have heq : (fun y => betaDensity q x * betaDensity q y *
        (P.eval (Polynomial.C x)).eval y) =
        (fun y => betaDensity q x * betaDensity q y *
          bivariatePolynomial (nestedSupport P) (nestedCoeff P) x y) := by
      funext y
      rw [bivariatePolynomial_nestedSupport]
    rw [heq]
    unfold bivariatePolynomial
    rw [show (fun y => betaDensity q x * betaDensity q y *
        ∑ ij ∈ nestedSupport P, nestedCoeff P ij.1 ij.2 * x ^ ij.1 * y ^ ij.2) =
      (fun y => ∑ ij ∈ nestedSupport P,
        (betaDensity q x * (nestedCoeff P ij.1 ij.2 * x ^ ij.1)) *
          (betaDensity q y * y ^ ij.2)) by
        funext y
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ij hij
        ring]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro ij hij
      rw [integral_const_mul, beta_monomial_interval_moment hq hb hbt]
    · intro ij hij
      exact (integrableOn_beta_monomial_interval hq hbt ij.2).const_mul _
  simp_rw [hinner]
  apply integrable_finset_sum
  intro ij hij
  refine ((integrableOn_beta_monomial_interval hq hlr ij.1).const_mul
    (nestedCoeff P ij.1 ij.2 *
      (q * ((top ^ (q + ij.2) - b ^ (q + ij.2)) / (q + ij.2))))).congr ?_
  filter_upwards with x
  ring

/-- Power-basis coefficients of the published bivariate cubic. -/
def pairPowerCoefficients : Fin 4 → Fin 4 → ℚ :=
  ![![(1 : ℚ), 42388316931 / 10000000000, -3951404529 / 1250000000,
      23040358681 / 5000000000],
    ![42388316931 / 10000000000, 1233476703 / 5000000000,
      1117209393 / 312500000, -37257860547 / 10000000000],
    ![-3951404529 / 1250000000, 1117209393 / 312500000,
      -2193824061 / 312500000, 65331233457 / 10000000000],
    ![23040358681 / 5000000000, -37257860547 / 10000000000,
      65331233457 / 10000000000, -22484447969 / 5000000000]]

/-- The witness polynomial as a polynomial in `t` whose coefficients are
polynomials in `u`. -/
def pairNestedPolynomial : Polynomial (Polynomial ℝ) :=
  ∑ i : Fin 4, Polynomial.C
    (∑ j : Fin 4, Polynomial.C (pairPowerCoefficients i j : ℝ) *
      Polynomial.X ^ (j : ℕ)) * Polynomial.X ^ (i : ℕ)

theorem pairNestedPolynomial_eval (t u : ℝ) :
    ((pairNestedPolynomial.eval (Polynomial.C t)).eval u) = polynomial t u := by
  norm_num [pairNestedPolynomial, pairPowerCoefficients, polynomial,
    bernsteinCoefficients, bernstein3, Fin.sum_univ_succ, Nat.choose]
  ring

/-- Polynomial in the centered relative fluctuation `polynomial / h - 1`. -/
def centeredPairPolynomial (h : ℝ) : Polynomial (Polynomial ℝ) :=
  pairNestedPolynomial * Polynomial.C (Polynomial.C h⁻¹) - 1

def pairBinomialPolynomial (h : ℝ) (N : ℕ) : Polynomial (Polynomial ℝ) :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.C (Polynomial.C (Ring.choose p k)) * centeredPairPolynomial h ^ k

theorem centeredPairPolynomial_eval {h : ℝ} (hh : h ≠ 0) (t u : ℝ) :
    ((centeredPairPolynomial h).eval (Polynomial.C t)).eval u =
      polynomial t u / h - 1 := by
  simp [centeredPairPolynomial, pairNestedPolynomial_eval, div_eq_mul_inv]

theorem pairBinomialPolynomial_eval {h : ℝ} (hh : h ≠ 0) (N : ℕ) (t u : ℝ) :
    ((pairBinomialPolynomial h N).eval (Polynomial.C t)).eval u =
      ∑ k ∈ Finset.range (N + 1), Ring.choose p k *
        (polynomial t u / h - 1) ^ k := by
  unfold pairBinomialPolynomial
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [centeredPairPolynomial_eval hh]

def pairCellTail (rho : ℝ) (N : ℕ) : ℝ :=
  |Ring.choose p (N + 1)| * rho ^ (N + 1) / (1 - rho)

/-- The rational-coefficient part of the local majorant.  The sole irrational
cell factor `h^p` is kept outside this polynomial for finite evaluation. -/
def pairCellBracketPolynomial (h rho : ℝ) (N : ℕ) :
    Polynomial (Polynomial ℝ) :=
  pairBinomialPolynomial h N +
    Polynomial.C (Polynomial.C (pairCellTail rho N))

theorem pairCellBracketPolynomial_eval {h : ℝ} (hh : h ≠ 0)
    (rho : ℝ) (N : ℕ) (t u : ℝ) :
    ((pairCellBracketPolynomial h rho N).eval (Polynomial.C t)).eval u =
      (∑ k ∈ Finset.range (N + 1), Ring.choose p k *
        (polynomial t u / h - 1) ^ k) + pairCellTail rho N := by
  simp [pairCellBracketPolynomial, pairBinomialPolynomial_eval hh]

/-- The polynomial majorant integrated on one certificate cell. -/
def pairCellMajorantPolynomial (h rho : ℝ) (N : ℕ) :
    Polynomial (Polynomial ℝ) :=
  Polynomial.C (Polynomial.C (h ^ p)) *
    pairCellBracketPolynomial h rho N

theorem pairCellMajorantPolynomial_eval {h : ℝ} (hh : h ≠ 0)
    (rho : ℝ) (N : ℕ) (t u : ℝ) :
    ((pairCellMajorantPolynomial h rho N).eval (Polynomial.C t)).eval u =
      h ^ p * (∑ k ∈ Finset.range (N + 1), Ring.choose p k *
        (polynomial t u / h - 1) ^ k + pairCellTail rho N) := by
  unfold pairCellMajorantPolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [pairCellBracketPolynomial_eval hh]

theorem normalized_center_abs_le {m M z : ℝ} (hm : 0 < m)
    (hmM : m ≤ M) (hmz : m ≤ z) (hzM : z ≤ M) :
    |z / ((m + M) / 2) - 1| ≤ (M - m) / (M + m) := by
  have hsum : 0 < M + m := by linarith
  have hcenter : 0 < (m + M) / 2 := by linarith
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hcenter]
    field_simp [hsum.ne']
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hcenter]
    field_simp [hsum.ne']
    nlinarith

theorem pairCell_pointwise_majorant {h rho t u : ℝ} {N : ℕ}
    (hN : 2 ≤ N) (hh : 0 < h) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hradius : |polynomial t u / h - 1| ≤ rho) :
    (polynomial t u) ^ p ≤
      ((pairCellMajorantPolynomial h rho N).eval (Polynomial.C t)).eval u := by
  let w := polynomial t u / h - 1
  have hP : 0 < polynomial t u := lt_of_lt_of_le (by norm_num)
    (polynomial_bounds ht0 ht1 hu0 hu1).1
  have hw : 1 + w = polynomial t u / h := by simp only [w]; ring
  have h1w : 0 ≤ 1 + w := by rw [hw]; positivity
  have htail := pairPower_binomial_truncation_error hN hrho0 hrho1 hradius
  have hupper : (1 + w) ^ p ≤
      (∑ k ∈ Finset.range (N + 1), Ring.choose p k * w ^ k) +
        pairCellTail rho N := by
    unfold pairCellTail
    linarith [le_abs_self ((1 + w) ^ p -
      ∑ k ∈ Finset.range (N + 1), Ring.choose p k * w ^ k)]
  have hfactor : polynomial t u = h * (1 + w) := by
    rw [hw]
    field_simp
  calc
    (polynomial t u) ^ p = (h * (1 + w)) ^ p := by rw [hfactor]
    _ = h ^ p * (1 + w) ^ p := Real.mul_rpow hh.le h1w
    _ ≤ h ^ p * ((∑ k ∈ Finset.range (N + 1), Ring.choose p k * w ^ k) +
        pairCellTail rho N) :=
      mul_le_mul_of_nonneg_left hupper (Real.rpow_nonneg hh.le p)
    _ = ((pairCellMajorantPolynomial h rho N).eval (Polynomial.C t)).eval u := by
      rw [pairCellMajorantPolynomial_eval hh.ne']

theorem pairCell_integral_le_contraction {l r b top h rho : ℝ} {N : ℕ}
    (hN : 2 ≤ N) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1)
    (hb : 0 ≤ b) (hbt : b ≤ top) (htop : top ≤ 1)
    (hh : 0 < h) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hradius : ∀ t ∈ Icc l r, ∀ u ∈ Icc b top,
      |polynomial t u / h - 1| ≤ rho) :
    (∫ t in Icc l r, ∫ u in Icc b top,
      betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
        (polynomial t u) ^ p) ≤
      betaMonomialRectangleContraction (6 / 5 : ℝ) l r b top
        (nestedSupport (pairCellBracketPolynomial h rho N))
        (nestedCoeff (pairCellBracketPolynomial h rho N)) * h ^ p := by
  let Q := pairCellBracketPolynomial h rho N
  have hq : (0 : ℝ) < 6 / 5 := by norm_num
  have hinner (t : ℝ) (ht : t ∈ Icc l r) :
      (∫ u in Icc b top,
        betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
          (polynomial t u) ^ p) ≤
      ∫ u in Icc b top,
        betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
          (h ^ p * (Q.eval (Polynomial.C t)).eval u) := by
    apply setIntegral_mono_of_nonneg
    · intro u hu
      have hdt : 0 ≤ betaDensity (6 / 5 : ℝ) t := by
        unfold betaDensity
        exact mul_nonneg (by norm_num) (Real.rpow_nonneg (hl.trans ht.1) ((6 / 5 : ℝ) - 1))
      have hdu : 0 ≤ betaDensity (6 / 5 : ℝ) u := by
        unfold betaDensity
        exact mul_nonneg (by norm_num) (Real.rpow_nonneg (hb.trans hu.1) ((6 / 5 : ℝ) - 1))
      have hone : (0 : ℝ) ≤ 1 := by norm_num
      have hPb := polynomial_bounds (t := t) (u := u)
        (hl.trans ht.1) (ht.2.trans hr) (hb.trans hu.1) (hu.2.trans htop)
      have hP : 0 ≤ polynomial t u := hone.trans hPb.1
      change 0 ≤ (betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u) *
        (polynomial t u) ^ p
      exact mul_nonneg (mul_nonneg hdt hdu) (Real.rpow_nonneg hP p)
    · intro u hu
      have hdt : 0 ≤ betaDensity (6 / 5 : ℝ) t := by
        unfold betaDensity
        exact mul_nonneg (by norm_num) (Real.rpow_nonneg (hl.trans ht.1) ((6 / 5 : ℝ) - 1))
      have hdu : 0 ≤ betaDensity (6 / 5 : ℝ) u := by
        unfold betaDensity
        exact mul_nonneg (by norm_num) (Real.rpow_nonneg (hb.trans hu.1) ((6 / 5 : ℝ) - 1))
      apply mul_le_mul_of_nonneg_left
        (show (polynomial t u) ^ p ≤ h ^ p * (Q.eval (Polynomial.C t)).eval u by
          rw [pairCellBracketPolynomial_eval hh.ne']
          let w := polynomial t u / h - 1
          have htail := pairPower_binomial_truncation_error hN hrho0 hrho1
            (hradius t ht u hu)
          have hupper : (1 + w) ^ p ≤
              (∑ k ∈ Finset.range (N + 1), Ring.choose p k * w ^ k) +
                pairCellTail rho N := by
            unfold pairCellTail
            linarith [le_abs_self ((1 + w) ^ p -
              ∑ k ∈ Finset.range (N + 1), Ring.choose p k * w ^ k)]
          have hw : 1 + w = polynomial t u / h := by simp only [w]; ring
          have hP : 0 ≤ polynomial t u := (by norm_num : (0 : ℝ) ≤ 1).trans
            (polynomial_bounds (hl.trans ht.1) (ht.2.trans hr)
              (hb.trans hu.1) (hu.2.trans htop)).1
          have h1w : 0 ≤ 1 + w := by rw [hw]; exact div_nonneg hP hh.le
          have hfactor : polynomial t u = h * (1 + w) := by rw [hw]; field_simp
          calc
            (polynomial t u) ^ p = (h * (1 + w)) ^ p := by rw [hfactor]
            _ = h ^ p * (1 + w) ^ p := Real.mul_rpow hh.le h1w
            _ ≤ h ^ p * ((∑ k ∈ Finset.range (N + 1),
                Ring.choose p k * w ^ k) + pairCellTail rho N) :=
              mul_le_mul_of_nonneg_left hupper (Real.rpow_nonneg hh.le p)
            _ = _ := by simp only [w])
      exact mul_nonneg hdt hdu
    · have hi := integrableOn_beta_nestedPolynomial_inner hq hbt Q t
      refine (hi.const_mul (h ^ p)).congr ?_
      filter_upwards with u
      ring
  calc
    (∫ t in Icc l r, ∫ u in Icc b top,
      betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
        (polynomial t u) ^ p) ≤
      ∫ t in Icc l r, ∫ u in Icc b top,
        betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
          (h ^ p * (Q.eval (Polynomial.C t)).eval u) := by
      apply setIntegral_mono_of_nonneg
      · intro t ht
        apply setIntegral_nonneg measurableSet_Icc
        intro u hu
        have hdt : 0 ≤ betaDensity (6 / 5 : ℝ) t := by
          unfold betaDensity
          exact mul_nonneg (by norm_num) (Real.rpow_nonneg (hl.trans ht.1) ((6 / 5 : ℝ) - 1))
        have hdu : 0 ≤ betaDensity (6 / 5 : ℝ) u := by
          unfold betaDensity
          exact mul_nonneg (by norm_num) (Real.rpow_nonneg (hb.trans hu.1) ((6 / 5 : ℝ) - 1))
        have hone : (0 : ℝ) ≤ 1 := by norm_num
        have hPb := polynomial_bounds (t := t) (u := u)
          (hl.trans ht.1) (ht.2.trans hr) (hb.trans hu.1) (hu.2.trans htop)
        have hP : 0 ≤ polynomial t u := hone.trans hPb.1
        change 0 ≤ (betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u) *
          (polynomial t u) ^ p
        exact mul_nonneg (mul_nonneg hdt hdu) (Real.rpow_nonneg hP p)
      · exact hinner
      · have hi := integrableOn_beta_nestedPolynomial_outer hq hlr hb hbt Q
        refine (hi.const_mul (h ^ p)).congr ?_
        filter_upwards with t
        change h ^ p * (∫ u in Icc b top,
            betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
              (Q.eval (Polynomial.C t)).eval u) =
          (∫ u in Icc b top,
            betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
              (h ^ p * (Q.eval (Polynomial.C t)).eval u))
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Icc
        intro u hu
        ring
    _ = _ := by
      rw [show (∫ t in Icc l r, ∫ u in Icc b top,
          betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
            (h ^ p * (Q.eval (Polynomial.C t)).eval u)) =
          h ^ p * (∫ t in Icc l r, ∫ u in Icc b top,
            betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
              (Q.eval (Polynomial.C t)).eval u) by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        change (∫ u in Icc b top,
            betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
              (h ^ p * (Q.eval (Polynomial.C t)).eval u)) =
          h ^ p * (∫ u in Icc b top,
            betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
              (Q.eval (Polynomial.C t)).eval u)
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Icc
        intro u hu
        ring]
      rw [beta_nestedPolynomial_rectangle_integral hq hl hlr hb hbt Q]
      ring

end UnitDistance.Witness
