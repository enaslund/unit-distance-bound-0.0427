module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! The actual absolute norm minimum in a nonzero fractional ideal. -/
noncomputable section
open NumberField
open scoped nonZeroDivisors
namespace UnitDistance.IdealMinimum
variable (K : Type*) [Field K] [NumberField K]

theorem absNorm_pos (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    0 < FractionalIdeal.absNorm I :=
  lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I)
    (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hI))

/-- Every nonzero element of a fractional ideal has absolute field norm at
least the ideal norm. The quotient of its principal ideal by the given ideal
is an actual nonzero integral ideal. -/
theorem absNorm_le_abs_norm (I : FractionalIdeal (𝓞 K)⁰ K)
    (x : K) (hx : x ∈ I) (hx0 : x ≠ 0) :
    FractionalIdeal.absNorm I ≤ |Algebra.norm ℚ x| := by
  have hI : I ≠ 0 := by
    intro h
    exact hx0 (by simpa [h] using hx)
  have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ I :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hx
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x * I⁻¹ ≤ 1 := by
    calc
      _ ≤ I * I⁻¹ := mul_le_mul_left hs _
      _ = 1 := mul_inv_cancel₀ hI
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hJ0 : J ≠ 0 := by
    intro h
    have hh := hJ
    simp only [h] at hh
    have hsp : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx0
    exact (mul_ne_zero hsp (inv_ne_zero hI)) hh.symm
  have hnorm : 1 ≤ (Ideal.absNorm J : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ0)
  rw [← FractionalIdeal.coeIdeal_absNorm (K := K) J, hJ, map_mul,
    FractionalIdeal.absNorm_span_singleton, map_inv₀] at hnorm
  have hh : (1 : ℚ) * FractionalIdeal.absNorm I ≤ |Algebra.norm ℚ x| :=
    (le_div_iff₀ (absNorm_pos K I hI)).mp (by simpa only [div_eq_mul_inv] using hnorm)
  rwa [one_mul] at hh

end UnitDistance.IdealMinimum
