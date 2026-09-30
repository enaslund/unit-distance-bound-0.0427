module

public import UnitDistance.Witness
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual Bernstein-Student pair profile

The exact positive Bernstein coefficients bound the polynomial between 1 and 14
on the unit square. This supplies a product Student envelope for the published
profile. Its Lp mass is integrable because the exact exponent s*p exceeds 1
in each complex coordinate. These are analytic facts about the actual witness,
not numerical-certificate assumptions.
-/

open MeasureTheory
open scoped BigOperators

namespace UnitDistance

/-- A complex Student weight, with ordinary Lebesgue measure used below. -/
noncomputable def studentWeight (a r : ℝ) (z : ℂ) : ℝ :=
  (1+a*‖z‖^2)^(-r)

theorem integrable_studentWeight {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    Integrable (studentWeight a r) := by
  have hbase : Integrable (fun z : ℂ => (1+‖z‖^2)^(-(2*r)/2)) :=
    integrable_rpow_neg_one_add_norm_sq (by rw [Complex.finrank_real_complex]; norm_num; linarith)
  have h := hbase.comp_smul (Real.sqrt_ne_zero'.mpr ha)
  convert h using 1
  funext z
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt ha.le]
  unfold studentWeight
  congr 1
  ring

namespace Witness

theorem bernstein3_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin 4) :
    0 ≤ bernstein3 i t := by
  unfold bernstein3
  positivity

theorem bernstein3_sum (t : ℝ) : (∑ i : Fin 4, bernstein3 i t) = 1 := by
  norm_num [bernstein3, Fin.sum_univ_succ, Nat.choose]
  ring

theorem bernsteinCoefficients_bounds (i j : Fin 4) :
    1 ≤ bernsteinCoefficients i j ∧ bernsteinCoefficients i j ≤ 14 := by
  fin_cases i <;> fin_cases j <;> norm_num [bernsteinCoefficients]

theorem polynomial_bounds {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 1 ≤ polynomial t u ∧ polynomial t u ≤ 14 := by
  have hweight (i j : Fin 4) : 0 ≤ bernstein3 i t * bernstein3 j u :=
    mul_nonneg (bernstein3_nonneg ht0 ht1 i) (bernstein3_nonneg hu0 hu1 j)
  have hsum : (∑ i : Fin 4, ∑ j : Fin 4, bernstein3 i t * bernstein3 j u) = 1 := by
    simp_rw [← Finset.mul_sum, bernstein3_sum, mul_one]
    exact bernstein3_sum t
  constructor
  · rw [← hsum]
    unfold polynomial
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hcoef : (1:ℝ) ≤ (bernsteinCoefficients i j : ℝ) := by
      exact_mod_cast (bernsteinCoefficients_bounds i j).1
    simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hcoef (hweight i j)
  · calc
      polynomial t u ≤ ∑ i : Fin 4, ∑ j : Fin 4, 14 * (bernstein3 i t * bernstein3 j u) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have hcoef : (bernsteinCoefficients i j : ℝ) ≤ (14:ℝ) := by
          exact_mod_cast (bernsteinCoefficients_bounds i j).2
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef (hweight i j)
      _ = 14 := by
        simp_rw [← Finset.mul_sum, bernstein3_sum, mul_one]
        rw [bernstein3_sum]; ring

theorem student_coordinate_bounds (z : ℂ) : 0 < (1+a*‖z‖^2)⁻¹ ∧ (1+a*‖z‖^2)⁻¹ ≤ 1 := by
  have ha : 0 < a := witness_basic.2.1
  have hb : 1 ≤ 1+a*‖z‖^2 := by nlinarith [mul_nonneg ha.le (sq_nonneg ‖z‖)]
  exact ⟨inv_pos.mpr (by linarith), (inv_le_one₀ (by linarith)).mpr hb⟩

theorem pairProfile_pos (z : ℂ × ℂ) : 0 < pairProfile z := by
  obtain ⟨ht, ht1⟩ := student_coordinate_bounds z.1
  obtain ⟨hu, hu1⟩ := student_coordinate_bounds z.2
  have hP := (polynomial_bounds ht.le ht1 hu.le hu1).1
  unfold pairProfile
  positivity

@[simp] theorem pairProfile_neg (z : ℂ × ℂ) : pairProfile (-z) = pairProfile z := by
  simp [pairProfile]

theorem exponent_student_integrable : 1 < s*p := by
  norm_num [s, p, increment]

theorem pairProfile_student_identity (z : ℂ × ℂ) :
    pairProfile z = studentWeight a s z.1 * studentWeight a s z.2 *
      polynomial (1+a*‖z.1‖^2)⁻¹ (1+a*‖z.2‖^2)⁻¹ := by
  have hbase (x : ℂ) : 0 ≤ 1+a*‖x‖^2 := by
    have ha := witness_basic.2.1
    positivity
  simp only [pairProfile, studentWeight, Real.inv_rpow (hbase _), Real.rpow_neg (hbase _)]

theorem pairProfile_rpow_le (z : ℂ × ℂ) {q : ℝ} (hq : 0 ≤ q) :
    pairProfile z ^ q ≤
      (studentWeight a (s*q) z.1 * studentWeight a (s*q) z.2) * 14^q := by
  have hbase (x : ℂ) : 0 < 1+a*‖x‖^2 := by
    have ha := witness_basic.2.1
    positivity
  have hw (x : ℂ) : 0 ≤ studentWeight a s x := Real.rpow_nonneg (hbase x).le _
  obtain ⟨ht, ht1⟩ := student_coordinate_bounds z.1
  obtain ⟨hu, hu1⟩ := student_coordinate_bounds z.2
  have hP := polynomial_bounds ht.le ht1 hu.le hu1
  rw [pairProfile_student_identity,
    Real.mul_rpow (mul_nonneg (hw _) (hw _)) (by linarith : 0 ≤ polynomial _ _),
    Real.mul_rpow (hw _) (hw _)]
  have hid (x : ℂ) : studentWeight a s x ^ q = studentWeight a (s*q) x := by
    simp only [studentWeight, ← Real.rpow_mul (hbase x).le, neg_mul]
  rw [hid, hid]
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hP.2 hq)
  exact mul_nonneg (Real.rpow_nonneg (hbase _).le _) (Real.rpow_nonneg (hbase _).le _)

theorem measurable_pairProfile : Measurable pairProfile := by
  unfold pairProfile polynomial bernstein3
  fun_prop

/-- The exact published Bernstein-Student profile has an integrable q-th
power whenever its coordinate Student exponent exceeds the complex threshold. -/
theorem integrable_pairProfile_rpow {q : ℝ} (hq : 0 ≤ q) (hscale : 1 < s*q) :
    Integrable (fun z : ℂ × ℂ => pairProfile z ^ q) := by
  have h := integrable_studentWeight witness_basic.2.1 hscale
  have hm : Measurable (fun z : ℂ × ℂ => pairProfile z ^ q) :=
    measurable_pairProfile.pow_const q
  apply ((h.mul_prod h).mul_const (14^q)).mono' hm.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (pairProfile_pos z) q)]
  exact pairProfile_rpow_le z hq

theorem integrable_pairMass : Integrable (fun z : ℂ × ℂ => pairProfile z ^ p) :=
  integrable_pairProfile_rpow witness_basic.2.2.1.le exponent_student_integrable

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

theorem pairProfile_le_fourteen (z : ℂ × ℂ) : pairProfile z ≤ 14 := by
  obtain ⟨ht, ht1⟩ := student_coordinate_bounds z.1
  obtain ⟨hu, hu1⟩ := student_coordinate_bounds z.2
  have hP := polynomial_bounds ht.le ht1 hu.le hu1
  have ht' := Real.rpow_le_one ht.le ht1 witness_basic.1.le
  have hu' := Real.rpow_le_one hu.le hu1 witness_basic.1.le
  have hmul : (1+a*‖z.1‖^2)⁻¹^s * (1+a*‖z.2‖^2)⁻¹^s ≤ 1 :=
    mul_le_one₀ ht' (Real.rpow_nonneg hu.le s) hu'
  unfold pairProfile
  exact (mul_le_mul_of_nonneg_right hmul (by linarith : 0 ≤ polynomial _ _)).trans
    (by simpa only [one_mul] using hP.2)

theorem integrable_pairProfile : Integrable pairProfile := by
  have h : 1 < s*1 := by norm_num [s]
  simpa only [Real.rpow_one] using integrable_pairProfile_rpow (by norm_num : (0:ℝ)≤1) h

/-- The spatial overlap integral is finite for every actual displacement.
Integrability of the further logarithmic displacement integral remains a
separate analytic obligation. -/
theorem integrable_pairProfile_overlap (β : ℂ × ℂ) :
    Integrable (fun z : ℂ × ℂ => pairProfile z * pairProfile (z + β)) := by
  have hm : Measurable (fun z : ℂ × ℂ => pairProfile z * pairProfile (z+β)) :=
    measurable_pairProfile.mul (measurable_pairProfile.comp (measurable_add_const β))
  apply (integrable_pairProfile.mul_const 14).mono' hm.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (pairProfile_pos z) (pairProfile_pos (z+β)))]
  exact mul_le_mul_of_nonneg_left (pairProfile_le_fourteen (z+β)) (pairProfile_pos z).le

/-- The everywhere-finite ordinary logarithmic energy of the positive pair profile. -/
noncomputable def pairEnergy (z : ℂ × ℂ) : ℝ := -Real.log (pairProfile z)

theorem measurable_pairEnergy : Measurable pairEnergy := measurable_pairProfile.log.neg

@[simp] theorem pairEnergy_neg (z : ℂ × ℂ) : pairEnergy (-z) = pairEnergy z := by
  simp only [pairEnergy, pairProfile_neg]

theorem pairEnergy_weight (q : ℝ) (z : ℂ × ℂ) :
    Real.exp (-q*pairEnergy z) = pairProfile z ^ q := by
  rw [Real.rpow_def_of_pos (pairProfile_pos z)]
  unfold pairEnergy
  congr 1
  ring

theorem integrable_pairEnergy_weight :
    Integrable (fun z : ℂ × ℂ => Real.exp (-p*pairEnergy z)) := by
  simpa only [pairEnergy_weight] using integrable_pairMass

theorem pairEnergy_mass : (∫ z : ℂ × ℂ, Real.exp (-p*pairEnergy z)) = pairMass := by
  simp only [pairEnergy_weight, pairMass]

end Witness
end UnitDistance
