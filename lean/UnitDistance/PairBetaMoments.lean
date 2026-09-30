module

public import UnitDistance.PairMassNormalization
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact beta moments for the pair-mass certificate

This file supplies the integration layer used by the finite binomial mass
certificate.  It evaluates beta-weighted monomials on the unit interval and
on rational subintervals, then contracts finite bivariate polynomials on a
rectangle to a finite expression in endpoint real powers.

The 8 by 8 rectangle data and the degree-18 binomial majorants are separate
finite certificate inputs; no numerical mass enclosure is assumed here.
-/

noncomputable section
open MeasureTheory Set

namespace UnitDistance.Witness

/-- The `Beta(q,1)` probability density on `(0,1)`. -/
def betaDensity (q t : ℝ) : ℝ := q * t ^ (q - 1)

theorem beta_monomial_moment {q : ℝ} (hq : 0 < q) (n : ℕ) :
    (∫ t in Icc (0 : ℝ) 1, betaDensity q t * t ^ n) =
      q / (q + n) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  calc
    (∫ t in (0 : ℝ)..1, betaDensity q t * t ^ n) =
        ∫ t in (0 : ℝ)..1, q * t ^ (q + n - 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t
      intro ht
      have ht0 : 0 < t := by
        norm_num [uIoc] at ht
        exact ht.1
      simp only [betaDensity, ← Real.rpow_natCast]
      calc
        q * t ^ (q - 1) * t ^ (n : ℝ) =
            q * (t ^ (q - 1) * t ^ (n : ℝ)) := by ring
        _ = q * t ^ ((q - 1) + n) := by rw [Real.rpow_add ht0]
        _ = _ := by
          congr 2
          ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      have hexp : -1 < q + (n : ℝ) - 1 := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      rw [integral_rpow (Or.inl hexp)]
      have hqn : q + (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
      rw [show q + (n : ℝ) - (1 : ℝ) + 1 = q + (n : ℝ) by ring]
      rw [Real.one_rpow, Real.zero_rpow hqn, sub_zero]
      simp only [one_mul, div_eq_mul_inv]

theorem integrableOn_beta_monomial {q : ℝ} (hq : 0 < q) (n : ℕ) :
    IntegrableOn (fun t : ℝ => betaDensity q t * t ^ n) (Icc 0 1) := by
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hrpow : IntervalIntegrable (fun t : ℝ => t ^ (q - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hmul := hrpow.mul_continuousOn (continuous_pow n).continuousOn
  have hconst := hmul.const_mul q
  convert hconst using 1
  ext t
  simp only [betaDensity]
  ring

theorem beta_monomial_interval_moment {q l r : ℝ} (hq : 0 < q)
    (hl : 0 ≤ l) (hlr : l ≤ r) (n : ℕ) :
    (∫ t in Icc l r, betaDensity q t * t ^ n) =
      q * ((r ^ (q + n) - l ^ (q + n)) / (q + n)) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlr]
  calc
    (∫ t in l..r, betaDensity q t * t ^ n) =
        ∫ t in l..r, q * t ^ (q + n - 1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t
      intro ht
      rw [uIoc_of_le hlr] at ht
      have ht0 : 0 < t := hl.trans_lt ht.1
      simp only [betaDensity, ← Real.rpow_natCast]
      calc
        q * t ^ (q - 1) * t ^ (n : ℝ) =
            q * (t ^ (q - 1) * t ^ (n : ℝ)) := by ring
        _ = q * t ^ ((q - 1) + n) := by rw [Real.rpow_add ht0]
        _ = _ := by
          congr 2
          ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      have hexp : -1 < q + (n : ℝ) - 1 := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      rw [integral_rpow (Or.inl hexp)]
      rw [show q + (n : ℝ) - (1 : ℝ) + 1 = q + (n : ℝ) by ring]

theorem integrableOn_beta_monomial_interval {q l r : ℝ} (hq : 0 < q)
    (hlr : l ≤ r) (n : ℕ) :
    IntegrableOn (fun t : ℝ => betaDensity q t * t ^ n) (Icc l r) := by
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hlr]
  have hrpow : IntervalIntegrable (fun t : ℝ => t ^ (q - 1)) volume l r :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hmul := hrpow.mul_continuousOn (continuous_pow n).continuousOn
  have hconst := hmul.const_mul q
  convert hconst using 1
  ext t
  simp only [betaDensity]
  ring

/-- The exact unnormalized beta moment of a normalized monomial on `[l,r]`. -/
def betaSubintervalMoment (q l r : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    ((Nat.choose n j : ℝ) * (-l) ^ (n - j) / (r - l) ^ n) *
      (q * ((r ^ (q + j) - l ^ (q + j)) / (q + j)))

theorem beta_normalized_monomial_interval_moment {q l r : ℝ} (hq : 0 < q)
    (hl : 0 ≤ l) (hlr : l < r) (n : ℕ) :
    (∫ t in Icc l r, betaDensity q t * ((t - l) / (r - l)) ^ n) =
      betaSubintervalMoment q l r n := by
  have hw : r - l ≠ 0 := ne_of_gt (sub_pos.mpr hlr)
  have hpoly (t : ℝ) : ((t - l) / (r - l)) ^ n =
      ∑ j ∈ Finset.range (n + 1),
        ((Nat.choose n j : ℝ) * (-l) ^ (n - j) / (r - l) ^ n) * t ^ j := by
    rw [div_pow, sub_eq_add_neg, add_pow]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [show (fun t : ℝ => betaDensity q t * ((t - l) / (r - l)) ^ n) =
      (fun t : ℝ => ∑ j ∈ Finset.range (n + 1),
        ((Nat.choose n j : ℝ) * (-l) ^ (n - j) / (r - l) ^ n) *
          (betaDensity q t * t ^ j)) by
      funext t
      rw [hpoly, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring]
  rw [integral_finsetSum]
  · unfold betaSubintervalMoment
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul, beta_monomial_interval_moment hq hl hlr.le]
  · intro j hj
    exact (integrableOn_beta_monomial_interval hq hlr.le j).const_mul _

/-- The manuscript formula with the common density and width factors pulled out. -/
theorem betaSubintervalMoment_eq {q l r : ℝ} (hlr : l < r) (n : ℕ) :
    betaSubintervalMoment q l r n =
      q / (r - l) ^ n * ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : ℝ) * (-l) ^ (n - j) *
          ((r ^ (q + j) - l ^ (q + j)) / (q + j)) := by
  have hw : (r - l) ^ n ≠ 0 := pow_ne_zero n (ne_of_gt (sub_pos.mpr hlr))
  unfold betaSubintervalMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  field_simp

theorem integrableOn_beta_normalized_monomial_interval {q l r : ℝ} (hq : 0 < q)
    (hlr : l < r) (n : ℕ) :
    IntegrableOn (fun t : ℝ => betaDensity q t * ((t - l) / (r - l)) ^ n)
      (Icc l r) := by
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hlr.le]
  have hrpow : IntervalIntegrable (fun t : ℝ => t ^ (q - 1)) volume l r :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hcontinuous : Continuous (fun t : ℝ => ((t - l) / (r - l)) ^ n) := by
    fun_prop
  have hmul := hrpow.mul_continuousOn hcontinuous.continuousOn
  have hconst := hmul.const_mul q
  convert hconst using 1
  ext t
  simp only [betaDensity]
  ring

/-- A finitely supported bivariate polynomial in the monomial basis. -/
def bivariatePolynomial (S : Finset (ℕ × ℕ)) (c : ℕ → ℕ → ℝ) (t u : ℝ) : ℝ :=
  ∑ ij ∈ S, c ij.1 ij.2 * t ^ ij.1 * u ^ ij.2

/-- Exact contraction of a monomial polynomial against two beta densities. -/
def betaPolynomialContraction (q : ℝ) (S : Finset (ℕ × ℕ))
    (c : ℕ → ℕ → ℝ) : ℝ :=
  ∑ ij ∈ S, c ij.1 ij.2 * (q / (q + ij.1)) * (q / (q + ij.2))

theorem beta_bivariate_polynomial_integral {q : ℝ} (hq : 0 < q)
    (S : Finset (ℕ × ℕ)) (c : ℕ → ℕ → ℝ) :
    (∫ t in Icc (0 : ℝ) 1, ∫ u in Icc (0 : ℝ) 1,
      betaDensity q t * betaDensity q u * bivariatePolynomial S c t u) =
        betaPolynomialContraction q S c := by
  have hinner (t : ℝ) :
      (∫ u in Icc (0 : ℝ) 1,
        betaDensity q t * betaDensity q u * bivariatePolynomial S c t u) =
      ∑ ij ∈ S, (betaDensity q t * (c ij.1 ij.2 * t ^ ij.1)) *
        (q / (q + ij.2)) := by
    rw [show (fun u : ℝ =>
        betaDensity q t * betaDensity q u * bivariatePolynomial S c t u) =
      (fun u : ℝ => ∑ ij ∈ S,
        (betaDensity q t * (c ij.1 ij.2 * t ^ ij.1)) *
          (betaDensity q u * u ^ ij.2)) by
        funext u
        simp only [bivariatePolynomial, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ij hij
        ring]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro ij hij
      rw [integral_const_mul, beta_monomial_moment hq]
    · intro ij hij
      exact (integrableOn_beta_monomial hq ij.2).const_mul _
  calc
    (∫ t in Icc (0 : ℝ) 1, ∫ u in Icc (0 : ℝ) 1,
      betaDensity q t * betaDensity q u * bivariatePolynomial S c t u) =
        ∫ t in Icc (0 : ℝ) 1,
          ∑ ij ∈ S, (c ij.1 ij.2 * (q / (q + ij.2))) *
            (betaDensity q t * t ^ ij.1) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      change (∫ u in Icc (0 : ℝ) 1,
        betaDensity q t * betaDensity q u * bivariatePolynomial S c t u) =
          ∑ ij ∈ S, (c ij.1 ij.2 * (q / (q + ij.2))) *
            (betaDensity q t * t ^ ij.1)
      rw [hinner]
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ∑ ij ∈ S, ∫ t in Icc (0 : ℝ) 1,
        (c ij.1 ij.2 * (q / (q + ij.2))) *
          (betaDensity q t * t ^ ij.1) := by
      rw [integral_finsetSum]
      intro ij hij
      exact (integrableOn_beta_monomial hq ij.1).const_mul _
    _ = betaPolynomialContraction q S c := by
      unfold betaPolynomialContraction
      apply Finset.sum_congr rfl
      intro ij hij
      rw [integral_const_mul, beta_monomial_moment hq]
      ring

/-- Exact contraction of a polynomial in normalized rectangle coordinates. -/
def betaRectangleContraction (q l r b t : ℝ) (S : Finset (ℕ × ℕ))
    (c : ℕ → ℕ → ℝ) : ℝ :=
  ∑ ij ∈ S, c ij.1 ij.2 * betaSubintervalMoment q l r ij.1 *
    betaSubintervalMoment q b t ij.2

theorem beta_bivariate_rectangle_polynomial_integral {q l r b t : ℝ} (hq : 0 < q)
    (hl : 0 ≤ l) (hlr : l < r) (hb : 0 ≤ b) (hbt : b < t)
    (S : Finset (ℕ × ℕ)) (c : ℕ → ℕ → ℝ) :
    (∫ x in Icc l r, ∫ y in Icc b t,
      betaDensity q x * betaDensity q y *
        bivariatePolynomial S c ((x - l) / (r - l)) ((y - b) / (t - b))) =
      betaRectangleContraction q l r b t S c := by
  have hinner (x : ℝ) :
      (∫ y in Icc b t,
        betaDensity q x * betaDensity q y *
          bivariatePolynomial S c ((x - l) / (r - l)) ((y - b) / (t - b))) =
      ∑ ij ∈ S,
        (betaDensity q x *
          (c ij.1 ij.2 * ((x - l) / (r - l)) ^ ij.1)) *
            betaSubintervalMoment q b t ij.2 := by
    rw [show (fun y : ℝ => betaDensity q x * betaDensity q y *
        bivariatePolynomial S c ((x - l) / (r - l)) ((y - b) / (t - b))) =
      (fun y : ℝ => ∑ ij ∈ S,
        (betaDensity q x *
          (c ij.1 ij.2 * ((x - l) / (r - l)) ^ ij.1)) *
            (betaDensity q y * ((y - b) / (t - b)) ^ ij.2)) by
        funext y
        simp only [bivariatePolynomial, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ij hij
        ring]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro ij hij
      rw [integral_const_mul,
        beta_normalized_monomial_interval_moment hq hb hbt]
    · intro ij hij
      exact (integrableOn_beta_normalized_monomial_interval hq hbt ij.2).const_mul _
  calc
    (∫ x in Icc l r, ∫ y in Icc b t,
      betaDensity q x * betaDensity q y *
        bivariatePolynomial S c ((x - l) / (r - l)) ((y - b) / (t - b))) =
      ∫ x in Icc l r, ∑ ij ∈ S,
        (c ij.1 ij.2 * betaSubintervalMoment q b t ij.2) *
          (betaDensity q x * ((x - l) / (r - l)) ^ ij.1) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change (∫ y in Icc b t,
        betaDensity q x * betaDensity q y *
          bivariatePolynomial S c ((x - l) / (r - l)) ((y - b) / (t - b))) =
        ∑ ij ∈ S,
          (c ij.1 ij.2 * betaSubintervalMoment q b t ij.2) *
            (betaDensity q x * ((x - l) / (r - l)) ^ ij.1)
      rw [hinner]
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ∑ ij ∈ S, ∫ x in Icc l r,
        (c ij.1 ij.2 * betaSubintervalMoment q b t ij.2) *
          (betaDensity q x * ((x - l) / (r - l)) ^ ij.1) := by
      rw [integral_finsetSum]
      intro ij hij
      exact (integrableOn_beta_normalized_monomial_interval hq hlr ij.1).const_mul _
    _ = betaRectangleContraction q l r b t S c := by
      unfold betaRectangleContraction
      apply Finset.sum_congr rfl
      intro ij hij
      rw [integral_const_mul,
        beta_normalized_monomial_interval_moment hq hl hlr]
      ring

end UnitDistance.Witness
