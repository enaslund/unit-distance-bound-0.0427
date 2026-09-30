module

public import UnitDistance.SIntegerLocalMeasure
public import UnitDistance.RelativeIdealCosetsNorm
public import Mathlib.Topology.Algebra.UniformRing

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual involution transport of prime valuations -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain WithZero

namespace UnitDistance.RelativeCompletion

open RelativeIdealCosets

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- Integer valuation values below one are determined by all prime-power
membership cuts. -/
theorem integerValue_eq_of_cuts {x y : ℤᵐ⁰} (hx : x ≠ 0) (hy : y ≠ 0)
    (hx1 : x ≤ 1) (hy1 : y ≤ 1)
    (h : ∀ n : ℕ, x ≤ WithZero.exp (-(n : ℤ)) ↔ y ≤ WithZero.exp (-(n : ℤ))) : x = y := by
  have radius (z : ℤᵐ⁰) (hz : z ≠ 0) (hz1 : z ≤ 1) :
      WithZero.exp (-(((-WithZero.log z).toNat : ℕ) : ℤ)) = z := by
    have hl : WithZero.log z ≤ 0 := by
      rw [← WithZero.exp_le_exp, WithZero.exp_log hz, WithZero.exp_zero]
      exact hz1
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hz]
  apply le_antisymm
  · have hh := (h ((-WithZero.log y).toNat)).mpr (by rw [radius y hy hy1])
    simpa only [radius y hy hy1] using hh
  · have hh := (h ((-WithZero.log x).toNat)).mp (by rw [radius x hx hx1])
    simpa only [radius x hx hx1] using hh

/-- The actual involution carries membership in prime powers to membership
in the partner's powers. -/
theorem integer_primePower_iff (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = conjugateIdeal ι v.asIdeal)
    (a : 𝓞 K) (n : ℕ) :
    RingOfIntegers.mapRingEquiv ι.toRingEquiv a ∈ w.asIdeal ^ n ↔ a ∈ v.asIdeal ^ n := by
  rw [hw, ← map_pow]
  change RingOfIntegers.mapRingEquiv ι.toRingEquiv a ∈
    Ideal.map (RingOfIntegers.mapRingEquiv ι.toRingEquiv).toRingHom (v.asIdeal ^ n) ↔ _
  rw [Ideal.mem_map_iff_of_surjective (RingOfIntegers.mapRingEquiv ι.toRingEquiv).toRingHom
    (RingOfIntegers.mapRingEquiv ι.toRingEquiv).surjective]
  constructor
  · rintro ⟨b, hb, he⟩
    have hba : b = a := (RingOfIntegers.mapRingEquiv ι.toRingEquiv).injective he
    simpa only [hba] using hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- The actual integer valuations agree under the involution. -/
theorem intValuation_involution (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = conjugateIdeal ι v.asIdeal)
    (a : 𝓞 K) :
    w.intValuation (RingOfIntegers.mapRingEquiv ι.toRingEquiv a) = v.intValuation a := by
  by_cases ha : a = 0
  · simp [ha]
  apply integerValue_eq_of_cuts
  · exact w.intValuation_ne_zero _ (by simpa only [map_zero] using
      (RingOfIntegers.mapRingEquiv ι.toRingEquiv).injective.ne ha)
  · exact v.intValuation_ne_zero _ ha
  · exact w.intValuation_le_one _
  · exact v.intValuation_le_one _
  · intro n
    rw [w.intValuation_le_pow_iff_mem, v.intValuation_le_pow_iff_mem]
    exact integer_primePower_iff ι v w hw a n

/-- The actual field valuations agree under the involution. -/
theorem valuation_involution (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = conjugateIdeal ι v.asIdeal)
    (x : K) : w.valuation K (ι x) = v.valuation K x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 K) x
  rw [map_div₀, map_div₀, map_div₀]
  congr 1
  · change w.valuation K (algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv ι.toRingEquiv a)) = _
    rw [w.valuation_of_algebraMap, v.valuation_of_algebraMap, intValuation_involution ι v w hw]
  · change w.valuation K (algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv ι.toRingEquiv b)) = _
    rw [w.valuation_of_algebraMap, v.valuation_of_algebraMap, intValuation_involution ι v w hw]

end UnitDistance.RelativeCompletion
