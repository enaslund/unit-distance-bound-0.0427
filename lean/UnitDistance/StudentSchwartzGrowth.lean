module

public import UnitDistance.StudentProfiles
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section
set_option backward.privateInPublic true


/-!
# Temperate growth of the actual polynomial Student weight

All derivatives of the exact published weight have polynomial growth. Real
powers are handled on their actual positive range, including the Bernstein
polynomial whose lower bound is one. No smoothness or derivative-growth
hypothesis is imposed on the witness.
-/

open scoped BigOperators ContDiff

namespace UnitDistance

/-- Taking an arbitrary real power preserves temperate growth for a real
function bounded below by one. The derivative estimates use the descending
Pochhammer formula on the actual range `[1,∞)`. -/
theorem temperateGrowth_rpow_of_one_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} (hf : f.HasTemperateGrowth)
    (hpos : ∀ x, 1 ≤ f x) (r : ℝ) :
    (fun x => f x ^ r).HasTemperateGrowth := by
  have ht : Set.range f ⊆ Set.Ici (1 : ℝ) := by rintro _ ⟨x, rfl⟩; exact hpos x
  have hu : UniqueDiffOn ℝ (Set.Ici (1 : ℝ)) := uniqueDiffOn_Ici 1
  have hd : ContDiffOn ℝ ∞ (fun x : ℝ => x ^ r) (Set.Ici 1) :=
    contDiffOn_fun_id.rpow_const_of_ne (fun x hx => (lt_of_lt_of_le zero_lt_one hx).ne')
  apply Function.HasTemperateGrowth.comp' ht hu hd _ hf
  intro N
  obtain ⟨k, hk⟩ := exists_nat_ge r
  refine ⟨k, ∑ j ∈ Finset.range (N+1), ‖Polynomial.eval r (descPochhammer ℝ j)‖,
    by positivity, ?_⟩
  intro n hn x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hdiff : ContDiffAt ℝ n (fun x : ℝ => x ^ r) x :=
    Real.contDiffAt_rpow_const (Or.inl hx0.ne')
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv hu hdiff hx, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, norm_mul]
  apply mul_le_mul
  · exact Finset.single_le_sum (f := fun j => ‖Polynomial.eval r (descPochhammer ℝ j)‖) (fun _ _ => norm_nonneg _) (show n ∈ Finset.range (N+1) by simpa using hn)
  · rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    calc
      x ^ (r - n) ≤ x ^ (k : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith [Nat.cast_nonneg (α := ℝ) n])
      _ = x ^ k := Real.rpow_natCast x k
      _ ≤ (1 + ‖x‖) ^ k := by gcongr; rw [Real.norm_eq_abs, abs_of_pos hx0]; linarith
  · exact norm_nonneg _
  · positivity

/-- The coordinate Student factor has temperate growth at every real exponent. -/
theorem temperateGrowth_studentWeight {a : ℝ} (ha : 0 < a) (r : ℝ) :
    (studentWeight a r).HasTemperateGrowth := by
  have hbase := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℂ (-r)
  have hscale : (fun z : ℂ => Real.sqrt a • z).HasTemperateGrowth := by fun_prop
  convert! hbase.comp hscale using 1
  funext z
  simp only [Function.comp_apply, studentWeight, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg a), mul_pow, Real.sq_sqrt ha.le]

namespace Witness

/-- The two-coordinate Bernstein correction as an ordinary real function. -/
noncomputable def studentPolynomial (z : ℂ × ℂ) : ℝ :=
  polynomial (1+a*‖z.1‖^2)⁻¹ (1+a*‖z.2‖^2)⁻¹

theorem studentPolynomial_one_le (z : ℂ × ℂ) : 1 ≤ studentPolynomial z :=
  (polynomial_bounds (student_coordinate_bounds z.1).1.le (student_coordinate_bounds z.1).2
    (student_coordinate_bounds z.2).1.le (student_coordinate_bounds z.2).2).1

theorem temperateGrowth_studentPolynomial : studentPolynomial.HasTemperateGrowth := by
  have hcoord : (fun z : ℂ => (1+a*‖z‖^2)⁻¹).HasTemperateGrowth := by
    have h := temperateGrowth_studentWeight witness_basic.2.1 1
    change (fun z : ℂ => (1+a*‖z‖^2)^(-(1 : ℝ))).HasTemperateGrowth at h
    simpa only [Real.rpow_neg_one] using h
  have hf : (fun z : ℂ × ℂ => z.1).HasTemperateGrowth :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasTemperateGrowth
  have hs : (fun z : ℂ × ℂ => z.2).HasTemperateGrowth :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasTemperateGrowth
  have ht := hcoord.comp hf
  have hu := hcoord.comp hs
  change (fun z : ℂ × ℂ => polynomial _ _).HasTemperateGrowth
  unfold polynomial bernstein3
  fun_prop

/-- The exact published profile raised to any real power is a temperate
multiplier. Positivity and the polynomial lower bound are proved from its
actual rational coefficients. -/
theorem temperateGrowth_pairProfile_rpow (q : ℝ) :
    (fun z : ℂ × ℂ => pairProfile z ^ q).HasTemperateGrowth := by
  have hpoly := temperateGrowth_rpow_of_one_le temperateGrowth_studentPolynomial
    studentPolynomial_one_le q
  have hw := temperateGrowth_studentWeight witness_basic.2.1 (s*q)
  have hf := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasTemperateGrowth
  have hs := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasTemperateGrowth
  have hprod := ((hw.comp hf).mul (hw.comp hs)).mul hpoly
  convert! hprod using 1
  funext z
  have hbase (x : ℂ) : 0 < 1+a*‖x‖^2 := by have := witness_basic.2.1; positivity
  have hpolypos : 0 < studentPolynomial z := lt_of_lt_of_le zero_lt_one (studentPolynomial_one_le z)
  rw [pairProfile_student_identity]
  change (studentWeight a s z.1 * studentWeight a s z.2 * studentPolynomial z)^q = _
  unfold studentWeight
  rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (hbase _).le _) (Real.rpow_nonneg (hbase _).le _)) hpolypos.le,
    Real.mul_rpow (Real.rpow_nonneg (hbase _).le _) (Real.rpow_nonneg (hbase _).le _)]
  simp only [Function.comp_apply, Pi.mul_apply,
    ← Real.rpow_mul (hbase _).le, neg_mul, studentPolynomial]
  rfl

end Witness
end UnitDistance
