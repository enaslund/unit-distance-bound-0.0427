module

public import UnitDistance.Sqrt241.Discriminant.Generic
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.QuadraticFieldDiscriminant
public import Mathlib.FieldTheory.KummerPolynomial

@[expose] public section
set_option backward.privateInPublic true


/-!
# Tame primes exposed by a quadratic subfield

Let `K` be a number field containing `x` with `x² = d`, where `d ≡ 1 (mod 4)`
is a squarefree non-square integer, and let `p ∣ d`. The quadratic field
`F = ℚ(x) ⊆ K` has discriminant `d`, so `v_p |disc F| = 1`, and every prime of
`F` above `p` has ramification index at least `2` (it contains `x`, and
`x² = p · (d/p)` with `d/p` prime to `p`). If every prime of `K` above `p` has
ramification index at most `2`, then `K/F` is unramified above `p` and

    2 · v_p |disc K| = [K : ℚ],

i.e. the `p`-part of the root discriminant of `K` is exactly `p^{1/2}`.
-/

noncomputable section
open NumberField Polynomial IntermediateField

namespace UnitDistance.Sqrt241.Discriminant

open UnitDistance.NumberFieldAnalysis

variable (K : Type*) [Field K] [NumberField K]

section QuadraticSubfield

variable {K} (d : ℤ) (x : K) (hx : x ^ 2 = (d : K))

include hx in
theorem isIntegral_sqrt : IsIntegral ℚ x := by
  refine ⟨X ^ 2 - C (d : ℚ), monic_X_pow_sub_C _ (by decide), ?_⟩
  rw [← aeval_def, map_sub, map_pow, aeval_X, aeval_C, hx]
  simp

include hx in
theorem minpoly_sqrt (hns : ¬ IsSquare (d : ℚ)) : minpoly ℚ x = X ^ 2 - C (d : ℚ) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro b hb
    exact hns ((isSquare_iff_exists_sq _).mpr ⟨b, hb.symm⟩)
  · simp [hx]
  · exact monic_X_pow_sub_C _ (by decide)

include hx in
theorem finrank_adjoin_sqrt (hns : ¬ IsSquare (d : ℚ)) :
    Module.finrank ℚ ℚ⟮x⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank (isIntegral_sqrt d x hx), minpoly_sqrt d x hx hns,
    natDegree_X_pow_sub_C]

/-- The square root inside `ℚ(x)`. -/
def sqrtGen : ℚ⟮x⟯ := IntermediateField.AdjoinSimple.gen ℚ x

include hx in
theorem sqrtGen_sq : sqrtGen x ^ 2 = algebraMap ℚ ℚ⟮x⟯ (d : ℚ) := by
  apply Subtype.ext
  simp [sqrtGen, hx]

include hx in
theorem sqrtGen_adjoin : IntermediateField.adjoin ℚ ({sqrtGen x} : Set ℚ⟮x⟯) = ⊤ := by
  apply IntermediateField.adjoin_eq_top_of_algebra
  have h := (IntermediateField.adjoin.powerBasis (isIntegral_sqrt d x hx)).adjoin_gen_eq_top
  rw [IntermediateField.adjoin.powerBasis_gen] at h
  exact h

include hx in
/-- The discriminant of `ℚ(x)` is `d`. -/
theorem discr_adjoin_sqrt (hsf : Squarefree d.natAbs) (hns : ¬ IsSquare (d : ℚ))
    (hd4 : d % 4 = 1) : discr ℚ⟮x⟯ = d := by
  have : Algebra.IsQuadraticExtension ℚ ℚ⟮x⟯ := ⟨finrank_adjoin_sqrt d x hx hns⟩
  exact ClassFieldTower.Sawin.numberField_discr_of_mod_four_eq_one ℚ⟮x⟯ d hsf (sqrtGen x)
    (by simpa using sqrtGen_sq d x hx) (sqrtGen_adjoin d x hx) hd4

include hx in
theorem isIntegral_sqrtGen : IsIntegral ℤ (sqrtGen x) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  rw [sqrtGen_sq d x hx]
  have : algebraMap ℚ ℚ⟮x⟯ (d : ℚ) = algebraMap ℤ ℚ⟮x⟯ d := by simp
  rw [this]
  exact isIntegral_algebraMap

/-- The square root as an algebraic integer of `ℚ(x)`. -/
def sqrtInt (hx : x ^ 2 = (d : K)) : 𝓞 ℚ⟮x⟯ := ⟨sqrtGen x, isIntegral_sqrtGen d x hx⟩

theorem sqrtInt_sq : sqrtInt d x hx ^ 2 = (d : 𝓞 ℚ⟮x⟯) := by
  apply RingOfIntegers.coe_injective
  change sqrtGen x ^ 2 = ((d : 𝓞 ℚ⟮x⟯) : ℚ⟮x⟯)
  rw [sqrtGen_sq d x hx]
  simp

include hx in
/-- Every prime of `ℚ(x)` above `p ∣ d` has ramification index at least two. -/
theorem two_le_ramificationIdx_adjoin_sqrt (hsf : Squarefree d.natAbs) {p : ℕ} (hp : p.Prime)
    (hpd : (p : ℤ) ∣ d) (Q : Ideal (𝓞 ℚ⟮x⟯)) [hQ : Q.IsPrime] (hpQ : (p : 𝓞 ℚ⟮x⟯) ∈ Q) :
    2 ≤ Q.ramificationIdx ℤ := by
  obtain ⟨m, hm⟩ := hpd
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  -- `p` and `m` are coprime since `d = p m` is squarefree
  have hcop : IsCoprime (p : ℤ) m := by
    rw [(Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
    rintro ⟨k, rfl⟩
    have hq2 : p * p ∣ d.natAbs := by
      rw [hm, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, ← mul_assoc]
      exact dvd_mul_right _ _
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsf p hq2))
  obtain ⟨a, b, hab⟩ := hcop
  have hmQ : (m : 𝓞 ℚ⟮x⟯) ∉ Q := by
    intro hmQ
    apply hQ.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : ((a * p + b * m : ℤ) : 𝓞 ℚ⟮x⟯) ∈ Q := by
      push_cast
      exact Q.add_mem (Q.mul_mem_left _ hpQ) (Q.mul_mem_left _ hmQ)
    rwa [hab, Int.cast_one] at h1
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpQ
    exact hp.ne_zero (by exact_mod_cast hpQ)
  have hQprime : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
  set r := sqrtInt d x hx
  have hr2 : r ^ 2 = (p : 𝓞 ℚ⟮x⟯) * (m : 𝓞 ℚ⟮x⟯) := by
    rw [sqrtInt_sq d x hx, hm]
    push_cast
    ring
  have hrQ : r ∈ Q := by
    apply hQ.mem_of_pow_mem 2
    rw [hr2]
    exact Q.mul_mem_right _ hpQ
  -- `Q² ∣ (p)`
  have hdiv : Q ^ 2 ∣ Ideal.span {(p : 𝓞 ℚ⟮x⟯)} := by
    have h1 : Q ^ 2 ∣ Ideal.span {r} ^ 2 :=
      pow_dvd_pow_of_dvd (Ideal.dvd_span_singleton.mpr hrQ) 2
    rw [Ideal.span_singleton_pow, hr2, ← Ideal.span_singleton_mul_span_singleton] at h1
    have hnd : ¬ Q ∣ Ideal.span {(m : 𝓞 ℚ⟮x⟯)} := by
      rw [Ideal.dvd_span_singleton]
      exact hmQ
    exact hQprime.pow_dvd_of_dvd_mul_right 2 hnd h1
  -- ramification index as a multiplicity
  have hlies : Q.LiesOver (rationalPrimeIdeal p) := by
    constructor
    have hle : rationalPrimeIdeal p ≤ Q.under ℤ := by
      rw [rationalPrimeIdeal, Ideal.span_le, Set.singleton_subset_iff]
      change algebraMap ℤ (𝓞 ℚ⟮x⟯) (p : ℤ) ∈ Q
      simpa only [map_natCast] using hpQ
    have hmax : (rationalPrimeIdeal p).IsMaximal :=
      ((Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp)).isMaximal
        (by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hp0)
    exact hmax.eq_of_le (Ideal.comap_ne_top _ hQ.ne_top) hle
  have hmap : (rationalPrimeIdeal p).map (algebraMap ℤ (𝓞 ℚ⟮x⟯)) =
      Ideal.span {(p : 𝓞 ℚ⟮x⟯)} := by
    rw [rationalPrimeIdeal, Ideal.map_span, Set.image_singleton, map_natCast]
  have hmap0 : (rationalPrimeIdeal p).map (algebraMap ℤ (𝓞 ℚ⟮x⟯)) ≠ ⊥ := by
    rw [hmap, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (rationalPrimeIdeal p) Q hmap0,
    hmap]
  have hfin : FiniteMultiplicity Q (Ideal.span {(p : 𝓞 ℚ⟮x⟯)}) := by
    apply FiniteMultiplicity.of_prime_left hQprime
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  exact hfin.le_multiplicity_of_pow_dvd hdiv

end QuadraticSubfield

variable {K}

/-- **Tame primes.** If `K` contains a square root of a squarefree non-square
`d ≡ 1 (mod 4)`, `p ∣ d`, and every prime of `K` above `p` has ramification
index at most `2`, then `2 · v_p |disc K| = [K : ℚ]`. -/
theorem two_mul_factorization_discr_eq_of_sqrt (d : ℤ) (hsf : Squarefree d.natAbs)
    (hns : ¬ IsSquare (d : ℚ)) (hd4 : d % 4 = 1) (x : K) (hx : x ^ 2 = (d : K))
    {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d)
    (hK : ∀ P : Ideal (𝓞 K), P.IsPrime → (p : 𝓞 K) ∈ P → P.ramificationIdx ℤ ≤ 2) :
    (discr K).natAbs.factorization p * 2 = Module.finrank ℚ K := by
  have hF := factorization_discr_mul_finrank_eq_of_unramifiedAbove (ℚ⟮x⟯) K hp
    (isUnramifiedAt_of_ramificationIdx_le (ℚ⟮x⟯) K 2
      (fun Q hQ hpQ => two_le_ramificationIdx_adjoin_sqrt d x hx hsf hp hpd Q hpQ) hK)
  rw [finrank_adjoin_sqrt d x hx hns, discr_adjoin_sqrt d x hx hsf hns hd4] at hF
  have hv : d.natAbs.factorization p = 1 := by
    apply le_antisymm
    · exact hsf.natFactorization_le_one p
    · rw [← Nat.Prime.dvd_iff_one_le_factorization hp (by
        rw [ne_eq, Int.natAbs_eq_zero]
        rintro rfl
        exact hns ⟨0, by simp⟩)]
      exact Int.natCast_dvd.mp hpd
  rw [hv, one_mul] at hF
  exact hF

/-- Galois form of the tame statement: ramification index `2` at `p`. -/
theorem two_mul_factorization_discr_eq_of_sqrt_of_ramificationIdxIn [IsGalois ℚ K] (d : ℤ)
    (hsf : Squarefree d.natAbs) (hns : ¬ IsSquare (d : ℚ)) (hd4 : d % 4 = 1) (x : K)
    (hx : x ^ 2 = (d : K)) {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d)
    (he : (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) = 2) :
    (discr K).natAbs.factorization p * 2 = Module.finrank ℚ K :=
  two_mul_factorization_discr_eq_of_sqrt d hsf hns hd4 x hx hp hpd fun P _ hpP => by
    rw [ramificationIdx_eq_ramificationIdxIn K hp P hpP, he]

end UnitDistance.Sqrt241.Discriminant
