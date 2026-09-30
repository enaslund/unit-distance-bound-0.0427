module

public import UnitDistance.PairOverlapFiniteCertificate
public import UnitDistance.PairMassNormalization
public import UnitDistance.StudentMoments

@[expose] public section
set_option backward.privateInPublic true


/-!
# Finite monomial expansion of the literal pair overlap

This module connects the exact witness integral to the rational power-basis
data in `PairOverlapFiniteCertificate`.  In particular, the nonlinear
Bernstein factors are replaced by a finite sum of Student monomial overlaps.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace UnitDistance.Witness

def pairOverlapMonomialProfile (i j : Fin 4) (z : ℂ × ℂ) : ℝ :=
  studentCoordinate z.1 ^ (s + (i : ℕ)) *
    studentCoordinate z.2 ^ (s + (j : ℕ))

def pairOverlapMonomialIntegrand (i j k l : Fin 4)
    (w : ℝ × (ℂ × ℂ)) : ℝ :=
  pairOverlapMonomialProfile i j w.2 *
    pairOverlapMonomialProfile k l (w.2 + reciprocalPairStep w.1)

def pairOverlapMonomial (i j k l : Fin 4) : ℝ :=
  ∫ w : ℝ × (ℂ × ℂ), pairOverlapMonomialIntegrand i j k l w

private theorem studentCoordinate_pos (z : ℂ) : 0 < studentCoordinate z := by
  unfold studentCoordinate
  exact (student_coordinate_bounds z).1

theorem pairOverlapMonomialProfile_eq (i j : Fin 4) (z : ℂ × ℂ) :
    pairOverlapMonomialProfile i j z =
      studentCoordinate z.1 ^ s * studentCoordinate z.2 ^ s *
        (studentCoordinate z.1 ^ (i : ℕ) * studentCoordinate z.2 ^ (j : ℕ)) := by
  unfold pairOverlapMonomialProfile
  rw [Real.rpow_add (studentCoordinate_pos z.1),
    Real.rpow_add (studentCoordinate_pos z.2),
    Real.rpow_natCast, Real.rpow_natCast]
  ring

theorem pairProfile_eq_sum_monomials (z : ℂ × ℂ) :
    pairProfile z =
      ∑ i : Fin 4, ∑ j : Fin 4,
        (pairOverlapPowerCoefficient i j : ℝ) *
          pairOverlapMonomialProfile i j z := by
  rw [pairProfile, polynomial_eq_pairOverlapPowerBasis]
  simp_rw [pairOverlapMonomialProfile_eq]
  simp only [studentCoordinate]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem pairOverlapIntegrand_eq_sum_monomials (w : ℝ × (ℂ × ℂ)) :
    pairOverlapIntegrand w =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        ((pairOverlapPowerCoefficient i j : ℝ) *
          (pairOverlapPowerCoefficient k l : ℝ)) *
            pairOverlapMonomialIntegrand i j k l w := by
  rw [pairOverlapIntegrand, pairProfile_eq_sum_monomials,
    pairProfile_eq_sum_monomials]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  unfold pairOverlapMonomialIntegrand
  ring

theorem pairOverlapMonomialProfile_nonneg (i j : Fin 4) (z : ℂ × ℂ) :
    0 ≤ pairOverlapMonomialProfile i j z := by
  unfold pairOverlapMonomialProfile
  exact mul_nonneg (Real.rpow_nonneg (studentCoordinate_pos z.1).le _)
    (Real.rpow_nonneg (studentCoordinate_pos z.2).le _)

theorem pairOverlapMonomialProfile_le_student (i j : Fin 4) (z : ℂ × ℂ) :
    pairOverlapMonomialProfile i j z ≤
      studentWeight a s z.1 * studentWeight a s z.2 := by
  have hcoord (x : ℂ) (n : Fin 4) :
      studentCoordinate x ^ (s + (n : ℕ)) ≤ studentCoordinate x ^ s := by
    have hx := student_coordinate_bounds x
    have hn : (0 : ℝ) ≤ (n : ℕ) := Nat.cast_nonneg _
    exact Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2
      (by linarith)
  have hnonneg (x : ℂ) (q : ℝ) : 0 ≤ studentCoordinate x ^ q :=
    Real.rpow_nonneg (studentCoordinate_pos x).le q
  rw [pairOverlapMonomialProfile]
  have hmul := mul_le_mul (hcoord z.1 i) (hcoord z.2 j)
    (hnonneg z.2 _) (hnonneg z.1 _)
  have heq (x : ℂ) : studentWeight a s x = studentCoordinate x ^ s := by
    have hb : 0 ≤ 1 + a * ‖x‖ ^ 2 := by positivity [witness_basic.2.1]
    unfold studentWeight studentCoordinate
    rw [Real.inv_rpow hb, Real.rpow_neg hb]
  rw [heq, heq]
  exact hmul

theorem measurable_pairOverlapMonomialIntegrand (i j k l : Fin 4) :
    Measurable (pairOverlapMonomialIntegrand i j k l) := by
  unfold pairOverlapMonomialIntegrand pairOverlapMonomialProfile studentCoordinate
  fun_prop

theorem integrable_pairOverlapMonomialIntegrand (i j k l : Fin 4) :
    Integrable (pairOverlapMonomialIntegrand i j k l) := by
  have hbase := integrable_studentPairOverlap witness_basic.2.1
    (show 1 < s by norm_num [s])
  apply hbase.mono' (measurable_pairOverlapMonomialIntegrand i j k l).aestronglyMeasurable
  filter_upwards with w
  unfold pairOverlapMonomialIntegrand
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (pairOverlapMonomialProfile_nonneg i j w.2)
    (pairOverlapMonomialProfile_nonneg k l (w.2 + reciprocalPairStep w.1)))]
  have h1 := pairOverlapMonomialProfile_le_student i j w.2
  have h2 := pairOverlapMonomialProfile_le_student k l
    (w.2 + reciprocalPairStep w.1)
  have hm := mul_le_mul h1 h2
    (pairOverlapMonomialProfile_nonneg k l (w.2 + reciprocalPairStep w.1))
    (mul_nonneg (studentWeight_nonneg witness_basic.2.1.le s w.2.1)
      (studentWeight_nonneg witness_basic.2.1.le s w.2.2))
  calc
    pairOverlapMonomialProfile i j w.2 *
        pairOverlapMonomialProfile k l (w.2 + reciprocalPairStep w.1) ≤
      (studentWeight a s w.2.1 * studentWeight a s w.2.2) *
        (studentWeight a s (w.2 + reciprocalPairStep w.1).1 *
          studentWeight a s (w.2 + reciprocalPairStep w.1).2) := hm
    _ = studentPairOverlap a s w := by
      simp only [studentPairOverlap, reciprocalPairStep, Prod.fst_add, Prod.snd_add]
      ring

/-- Exact finite expansion of the original literal overlap integral. -/
theorem pairOverlap_eq_sum_monomialOverlaps :
    pairOverlap =
      ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
        ((pairOverlapPowerCoefficient i j : ℝ) *
          (pairOverlapPowerCoefficient k l : ℝ)) *
            pairOverlapMonomial i j k l := by
  rw [pairOverlap_eq_integral]
  simp_rw [pairOverlapIntegrand_eq_sum_monomials]
  rw [integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun l _ =>
        (integrable_pairOverlapMonomialIntegrand i j k l).const_mul _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_sum _ (fun j _ =>
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ =>
      (integrable_pairOverlapMonomialIntegrand i j k l).const_mul _)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun l _ =>
    (integrable_pairOverlapMonomialIntegrand i j k l).const_mul _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_finset_sum _ (fun l _ =>
    (integrable_pairOverlapMonomialIntegrand i j k l).const_mul _)]
  apply Finset.sum_congr rfl
  intro l hl
  rw [integral_const_mul]
  rfl

end UnitDistance.Witness
