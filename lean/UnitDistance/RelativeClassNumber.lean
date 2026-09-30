module

public import UnitDistance.RelativeZeta
public import UnitDistance.RelativeDiscriminant
public import UnitDistance.RelativeUnits
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual relative analytic class-number formula

This derives the normalization in `analytic.tex`, equation (an:class-formula),
from Mathlib's analytic class-number formula and the actual unramified
discriminant identity. Class numbers, regulators and torsion orders below are
the ordinary number-field invariants. The relative regulator/capitulation
covolume identities are separate obligations.
-/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.Units

namespace UnitDistance.NumberFieldAnalysis

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

/-- The genuine class-number and ordinary-regulator ratio. -/
def relativeClassRegulator : ℝ :=
  (classNumber K : ℝ) * regulator K / ((classNumber F : ℝ) * regulator F)

theorem relativeClassRegulator_pos : 0 < relativeClassRegulator K F := by
  unfold relativeClassRegulator
  exact div_pos (mul_pos (by exact_mod_cast classNumber_pos K) (regulator_pos K))
    (mul_pos (by exact_mod_cast classNumber_pos F) (regulator_pos F))

variable [Algebra F K] [IsTotallyComplex K]

theorem nrComplexPlaces_eq_base_degree (hdegree : Module.finrank F K = 2) :
    nrComplexPlaces K = Module.finrank ℚ F := by
  have h := Module.finrank_mul_finrank ℚ F K
  rw [hdegree, IsTotallyComplex.finrank K] at h
  omega

omit [IsTotallyComplex K] in
theorem sqrt_absoluteDiscriminant_eq_base (hdegree : Module.finrank F K = 2)
    (hu : FiniteUnramified F K) :
    Real.sqrt (absoluteDiscriminant K) = absoluteDiscriminant F := by
  rw [absoluteDiscriminant_eq_pow_of_finiteUnramified F K hu, hdegree,
    Real.sqrt_sq (absoluteDiscriminant_pos F).le]

/-- The residue quotient, with the full angular, torsion, discriminant and
signature factors of the manuscript. No relative mass identity is an input. -/
theorem relativeResidue_eq_class_formula (hdegree : Module.finrank F K = 2)
    (hu : FiniteUnramified F K) :
    relativeResidue K F =
      (2 : ℝ) ^ nrComplexPlaces F * Real.pi ^ (nrRealPlaces F + nrComplexPlaces F) /
        Real.sqrt (absoluteDiscriminant F) *
        ((classNumber K : ℝ) * regulator K * torsionOrder F) /
        ((classNumber F : ℝ) * regulator F * torsionOrder K) := by
  have hs : nrComplexPlaces K = nrRealPlaces F + 2 * nrComplexPlaces F := by
    rw [nrComplexPlaces_eq_base_degree K F hdegree]
    exact (card_add_two_mul_card_eq_rank F).symm
  have hrK : regulator K ≠ 0 := (regulator_pos K).ne'
  have hrF : regulator F ≠ 0 := (regulator_pos F).ne'
  have hhF : (classNumber F : ℝ) ≠ 0 := by exact_mod_cast (classNumber_pos F).ne'
  have hwK : (torsionOrder K : ℝ) ≠ 0 := by exact_mod_cast (torsionOrder_pos K).ne'
  have hwF : (torsionOrder F : ℝ) ≠ 0 := by exact_mod_cast (torsionOrder_pos F).ne'
  have hD : absoluteDiscriminant F ≠ 0 := (absoluteDiscriminant_pos F).ne'
  have hsqrt : Real.sqrt (absoluteDiscriminant F) ≠ 0 :=
    (Real.sqrt_pos.mpr (absoluteDiscriminant_pos F)).ne'
  have hsq := Real.sq_sqrt (absoluteDiscriminant_pos F).le
  have hpi := Real.pi_ne_zero
  unfold relativeResidue dedekindZeta_residue
  rw [← absoluteDiscriminant_eq_abs K, ← absoluteDiscriminant_eq_abs F,
    sqrt_absoluteDiscriminant_eq_base K F hdegree hu,
    IsTotallyComplex.nrRealPlaces_eq_zero K, hs]
  simp only [pow_zero, one_mul, pow_add, pow_mul, mul_pow]
  field_simp
  simp only [← pow_mul, Nat.mul_comm 2]
  rw [hsq]
  ring

/-- The same formula in the paper's exact root-discriminant real powers. -/
theorem relativeResidue_eq_rootDiscriminant_class_formula
    (hdegree : Module.finrank F K = 2) (hu : FiniteUnramified F K) :
    relativeResidue K F =
      (2 : ℝ) ^ nrComplexPlaces F * Real.pi ^ (nrRealPlaces F + nrComplexPlaces F) *
        rootDiscriminant F ^ (-((Module.finrank ℚ F : ℝ) / 2)) *
        ((classNumber K : ℝ) * regulator K * torsionOrder F) /
        ((classNumber F : ℝ) * regulator F * torsionOrder K) := by
  rw [relativeResidue_eq_class_formula K F hdegree hu,
    sqrt_absoluteDiscriminant_eq_rootDiscriminant_rpow F,
    Real.rpow_neg (rootDiscriminant_pos F).le]
  rfl

/-- The class/regulator normalization used immediately before `geo:mass-density`.
The torsion order of the base is derived from its actual real embedding. -/
theorem relativeClassRegulator_eq (hdegree : Module.finrank F K = 2)
    (hu : FiniteUnramified F K) (ρ : F →+* ℝ) :
    relativeClassRegulator K F =
      (torsionOrder K : ℝ) * Real.sqrt (absoluteDiscriminant F) * relativeResidue K F /
        ((2 : ℝ) ^ (nrComplexPlaces F + 1) *
          Real.pi ^ (nrRealPlaces F + nrComplexPlaces F)) := by
  rw [relativeResidue_eq_class_formula K F hdegree hu,
    RelativeUnits.torsionOrder_eq_two ρ]
  have hrF : regulator F ≠ 0 := (regulator_pos F).ne'
  have hhF : (classNumber F : ℝ) ≠ 0 := by exact_mod_cast (classNumber_pos F).ne'
  have hwK : (torsionOrder K : ℝ) ≠ 0 := by exact_mod_cast (torsionOrder_pos K).ne'
  have hsqrt : Real.sqrt (absoluteDiscriminant F) ≠ 0 :=
    (Real.sqrt_pos.mpr (absoluteDiscriminant_pos F)).ne'
  have hpi := Real.pi_ne_zero
  unfold relativeClassRegulator
  simp only [pow_succ, Nat.cast_ofNat]
  field_simp

end UnitDistance.NumberFieldAnalysis
