module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Discriminants of actual finite-unramified extensions

These results use the different ideal of the rings of integers. They prove
the discriminant power identity and equality of the actual root discriminants
from unramifiedness at every finite prime. They neither postulate a tower nor
assign an arbitrary constant to a field's root discriminant.
-/

noncomputable section
open NumberField

namespace UnitDistance.NumberFieldAnalysis

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]

/-- The ordinary absolute field discriminant, as a positive real number. -/
def absoluteDiscriminant : ℝ := (discr F).natAbs

theorem absoluteDiscriminant_pos : 0 < absoluteDiscriminant F := by
  unfold absoluteDiscriminant
  exact_mod_cast (Int.natAbs_pos.mpr (discr_ne_zero F))

theorem absoluteDiscriminant_eq_abs : absoluteDiscriminant F = |(discr F : ℝ)| := by
  simp [absoluteDiscriminant]

/-- The exact real power defining the root discriminant of a number field. -/
def rootDiscriminant : ℝ :=
  absoluteDiscriminant F ^ (1 / (Module.finrank ℚ F : ℝ))

theorem rootDiscriminant_pos : 0 < rootDiscriminant F :=
  Real.rpow_pos_of_pos (absoluteDiscriminant_pos F) _

theorem rootDiscriminant_rpow_degree :
    rootDiscriminant F ^ (Module.finrank ℚ F : ℝ) = absoluteDiscriminant F := by
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  rw [rootDiscriminant, ← Real.rpow_mul (absoluteDiscriminant_pos F).le,
    one_div_mul_cancel hn, Real.rpow_one]

theorem sqrt_absoluteDiscriminant_eq_rootDiscriminant_rpow :
    Real.sqrt (absoluteDiscriminant F) =
      rootDiscriminant F ^ ((Module.finrank ℚ F : ℝ) / 2) := by
  rw [div_eq_mul_inv, Real.rpow_mul (rootDiscriminant_pos F).le,
    rootDiscriminant_rpow_degree F, Real.sqrt_eq_rpow]
  norm_num

variable [Algebra F K]

/-- Unramifiedness of the actual rings of integers at all finite primes. -/
def FiniteUnramified : Prop :=
  ∀ (P : Ideal (𝓞 K)) (_ : P.IsMaximal), Algebra.IsUnramifiedAt (𝓞 F) P

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

theorem differentIdeal_eq_top_of_finiteUnramified (h : FiniteUnramified F K) :
    differentIdeal (𝓞 F) (𝓞 K) = ⊤ := by
  by_contra hn
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hn
  letI := hP
  exact (not_dvd_differentIdeal_iff.mpr (h P hP)) (Ideal.dvd_iff_le.mpr hle)

theorem finiteUnramified_iff_differentIdeal_eq_top :
    FiniteUnramified F K ↔ differentIdeal (𝓞 F) (𝓞 K) = ⊤ := by
  refine ⟨differentIdeal_eq_top_of_finiteUnramified F K, ?_⟩
  intro h P hP
  letI := hP
  apply not_dvd_differentIdeal_iff.mp
  rw [h, Ideal.dvd_iff_le]
  exact fun hh => hP.ne_top (top_unique hh)

theorem natAbs_discr_eq_pow_of_finiteUnramified (h : FiniteUnramified F K) :
    (discr K).natAbs = (discr F).natAbs ^ Module.finrank F K := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) K (𝓞 K),
    differentIdeal_eq_top_of_finiteUnramified F K h, Ideal.absNorm_top, one_mul]

theorem absoluteDiscriminant_eq_pow_of_finiteUnramified (h : FiniteUnramified F K) :
    absoluteDiscriminant K = absoluteDiscriminant F ^ Module.finrank F K := by
  unfold absoluteDiscriminant
  exact_mod_cast natAbs_discr_eq_pow_of_finiteUnramified F K h

theorem rootDiscriminant_eq_of_finiteUnramified (h : FiniteUnramified F K) :
    rootDiscriminant K = rootDiscriminant F := by
  have hdeg : (Module.finrank ℚ K : ℝ) =
      (Module.finrank ℚ F : ℝ) * (Module.finrank F K : ℝ) := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F K).symm
  have hn : (Module.finrank F K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := F) (M := K)).ne'
  rw [rootDiscriminant, rootDiscriminant,
    absoluteDiscriminant_eq_pow_of_finiteUnramified F K h,
    ← Real.rpow_natCast_mul (absoluteDiscriminant_pos F).le, hdeg]
  congr 1
  field_simp

end UnitDistance.NumberFieldAnalysis
