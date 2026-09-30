module

public import UnitDistance.SIntegerCRTBasic

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual fractional-ideal membership characterized by all finite valuations -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain

namespace UnitDistance.SIntegerCRT

open RelativeIdealCosets

variable {K : Type} [Field K] [NumberField K]

/-- A nonzero fractional ideal with nonnegative actual prime multiplicities
is the extension of an ordinary integral ideal. -/
theorem exists_integralIdeal_of_count_nonnegative (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) (h : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ FractionalIdeal.count K v I) :
    ∃ J : Ideal (𝓞 K), (J : FractionalIdeal (𝓞 K)⁰ K) = I := by
  refine ⟨∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ (FractionalIdeal.count K v I).toNat, ?_⟩
  rw [FractionalIdeal.coeIdeal_finprod (S := (𝓞 K)⁰) (P := K)
    (f := fun v : HeightOneSpectrum (𝓞 K) ↦ v.asIdeal ^ (FractionalIdeal.count K v I).toNat) le_rfl]
  calc
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v I := by
      apply finprod_congr
      intro v
      rw [FractionalIdeal.coeIdeal_pow, ← zpow_natCast, Int.toNat_of_nonneg (h v)]
    _ = I := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI

/-- Inclusion of actual nonzero fractional ideals is equivalent to the
reverse inequalities for all ordinary prime multiplicities. -/
theorem fractionalIdeal_le_iff_counts (I J : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K v J ≤
      FractionalIdeal.count K v I := by
  constructor
  · exact fun h v ↦ FractionalIdeal.count_mono K v hI h
  · intro h
    have hn : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ FractionalIdeal.count K v (I * J⁻¹) := by
      intro v
      rw [FractionalIdeal.count_mul K v hI (inv_ne_zero hJ), FractionalIdeal.count_inv]
      linarith [h v]
    obtain ⟨A, hA⟩ := exists_integralIdeal_of_count_nonnegative (I * J⁻¹)
      (mul_ne_zero hI (inv_ne_zero hJ)) hn
    have hle : I * J⁻¹ ≤ 1 := hA ▸ FractionalIdeal.coeIdeal_le_one
    have hh := mul_le_mul_left hle J
    simpa only [mul_assoc, inv_mul_cancel₀ hJ, mul_one, one_mul] using hh

/-- An actual nonzero field element belongs to a nonzero fractional ideal
exactly when each of its local valuations satisfies that ideal's prime bound. -/
theorem mem_fractionalIdeal_iff_valuations (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) (x : K) :
    x ∈ I ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      v.valuation K x ≤ WithZero.exp (-FractionalIdeal.count K v I) := by
  by_cases hx : x = 0
  · subst x
    constructor
    · intro _ v
      simp
    · intro _
      exact I.val.zero_mem
  rw [← FractionalIdeal.spanSingleton_le_iff_mem,
    fractionalIdeal_le_iff_counts _ _ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) hI]
  apply forall_congr'
  intro v
  have hv := valuation_eq_exp_neg_principal_count v (Units.mk0 x hx)
  change v.valuation K x = WithZero.exp
    (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) at hv
  rw [hv, WithZero.exp_le_exp, neg_le_neg_iff]

end UnitDistance.SIntegerCRT
