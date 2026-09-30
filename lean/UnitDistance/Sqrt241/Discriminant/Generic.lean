module

public import UnitDistance.RelativeDiscriminant
public import UnitDistance.GaloisPrimeNormCounts
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Prime-by-prime discriminant exponents

For number fields `F → K` and a rational prime `p`:

* (`factorization_discr_eq_of_unramifiedAbove`) if every prime of `𝓞 K` above `p`
  is unramified over `𝓞 F`, then `v_p |disc K| = [K : F] · v_p |disc F|`;
* (`isUnramifiedAt_of_ramificationIdx_le`) this holds as soon as every prime of
  `𝓞 F` above `p` has ramification index over `ℤ` at least the ramification
  index of every prime of `𝓞 K` above `p`;
* (`factorization_discr_mul_finrank_eq_of_ramificationIdxIn_eq`) for `F`, `K`
  Galois over `ℚ` with the same ramification index at `p`,
  `v_p |disc K| / [K : ℚ] = v_p |disc F| / [F : ℚ]`;
* (`log_rootDiscriminant_le_sum`) `log rd(K) ≤ Σ_{p ∈ T} c_p log p` as soon as
  every prime divisor of `disc K` lies in `T` and `v_p |disc K| ≤ c_p [K : ℚ]`.

No tame different formula and no Galois invariance of the different is used:
the `p`-part of the discriminant is transported along extensions that are
unramified above `p`.
-/

noncomputable section
open NumberField

namespace UnitDistance.Sqrt241.Discriminant

open UnitDistance.NumberFieldAnalysis

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section Transfer

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

omit [NumberField K] in
/-- A prime ideal lying over `p` contains `p`. -/
theorem natCast_mem_of_under_eq {p : ℕ} (P : Ideal (𝓞 K))
    (h : P.under ℤ = Ideal.span {(p : ℤ)}) : (p : 𝓞 K) ∈ P := by
  have hmem : (p : ℤ) ∈ P.under ℤ := by
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton _)
  change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P at hmem
  simpa only [map_natCast] using hmem

/-- **D1.** If `K/F` is unramified at every prime above `p`, the `p`-adic
valuation of the absolute discriminant scales with the relative degree. -/
theorem factorization_discr_eq_of_unramifiedAbove {p : ℕ} (hp : p.Prime)
    (h : ∀ (P : Ideal (𝓞 K)) (_ : P.IsMaximal), (p : 𝓞 K) ∈ P → Algebra.IsUnramifiedAt (𝓞 F) P) :
    (discr K).natAbs.factorization p =
      Module.finrank F K * (discr F).natAbs.factorization p := by
  have hd := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) K (𝓞 K)
  have hD0 : Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]
    exact differentIdeal_ne_bot
  have hF0 : (discr F).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero F)
  have hndvd : ¬ p ∣ Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 K)) := by
    intro hdiv
    obtain ⟨P, hPmax, hPunder, hPdvd⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp _ hdiv
    have : P.IsMaximal := hPmax
    exact (not_dvd_differentIdeal_iff.mpr (h P hPmax (natCast_mem_of_under_eq K P hPunder)))
      hPdvd
  rw [hd, Nat.factorization_mul hD0 (pow_ne_zero _ hF0), Nat.factorization_pow,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hndvd, zero_add,
    Finsupp.smul_apply, smul_eq_mul]

/-- **D2.** Relative unramifiedness above `p` from a comparison of absolute
ramification indices: every prime of `F` above `p` is at least as ramified as
every prime of `K` above `p`. -/
theorem isUnramifiedAt_of_ramificationIdx_le {p : ℕ} (e : ℕ)
    (hF : ∀ Q : Ideal (𝓞 F), Q.IsPrime → (p : 𝓞 F) ∈ Q → e ≤ Q.ramificationIdx ℤ)
    (hK : ∀ P : Ideal (𝓞 K), P.IsPrime → (p : 𝓞 K) ∈ P → P.ramificationIdx ℤ ≤ e) :
    ∀ (P : Ideal (𝓞 K)) (_ : P.IsMaximal), (p : 𝓞 K) ∈ P → Algebra.IsUnramifiedAt (𝓞 F) P := by
  intro P hP hpP
  have := hP
  let Q : Ideal (𝓞 F) := P.under (𝓞 F)
  have : Q.IsPrime := Ideal.comap_isPrime _ P
  have : P.LiesOver Q := ⟨rfl⟩
  have hpQ : (p : 𝓞 F) ∈ Q := by
    change algebraMap (𝓞 F) (𝓞 K) (p : 𝓞 F) ∈ P
    simpa only [map_natCast] using hpP
  have ht := Ideal.ramificationIdx_tower (R := ℤ) Q P
  have hQpos : 0 < Q.ramificationIdx ℤ := Ideal.ramificationIdx_pos Q ℤ
  have hPpos : 0 < P.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos P (𝓞 F)
  have h1 := hF Q inferInstance hpQ
  have h2 := hK P inferInstance hpP
  have hrel : P.ramificationIdx (𝓞 F) = 1 := by
    rw [ht] at h2
    by_contra hne
    have h2le : 2 ≤ P.ramificationIdx (𝓞 F) := by omega
    have : Q.ramificationIdx ℤ * 2 ≤ Q.ramificationIdx ℤ * P.ramificationIdx (𝓞 F) :=
      Nat.mul_le_mul_left _ h2le
    omega
  exact Ideal.ramificationIdx_eq_one_iff.mp hrel

/-- Degree bookkeeping: `[K : ℚ] = [K : F] [F : ℚ]`. -/
theorem finrank_rat_eq_mul : Module.finrank ℚ K = Module.finrank F K * Module.finrank ℚ F := by
  rw [← Module.finrank_mul_finrank ℚ F K, mul_comm]

/-- D1 in normalized form: `v_p(disc K) [F:ℚ] = v_p(disc F) [K:ℚ]`. -/
theorem factorization_discr_mul_finrank_eq_of_unramifiedAbove {p : ℕ} (hp : p.Prime)
    (h : ∀ (P : Ideal (𝓞 K)) (_ : P.IsMaximal), (p : 𝓞 K) ∈ P → Algebra.IsUnramifiedAt (𝓞 F) P) :
    (discr K).natAbs.factorization p * Module.finrank ℚ F =
      (discr F).natAbs.factorization p * Module.finrank ℚ K := by
  rw [factorization_discr_eq_of_unramifiedAbove F K hp h, finrank_rat_eq_mul F K]
  ring

end Transfer

section Galois

variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

/-- In a Galois number field every prime above `p` has ramification index
`ramificationIdxIn`. -/
theorem ramificationIdx_eq_ramificationIdxIn {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 K))
    [hP : P.IsPrime] (hpP : (p : 𝓞 K) ∈ P) :
    P.ramificationIdx ℤ = (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : (rationalPrimeIdeal p) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have : (rationalPrimeIdeal p).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal hp0
  have : P.LiesOver (rationalPrimeIdeal p) := by
    constructor
    have hle : rationalPrimeIdeal p ≤ P.under ℤ := by
      rw [rationalPrimeIdeal, Ideal.span_le, Set.singleton_subset_iff]
      change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P
      simpa only [map_natCast] using hpP
    exact (this.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) hle)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (rationalPrimeIdeal p) P Gal(K/ℚ)]

variable {K}
variable (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F] [Algebra F K]

/-- **(a)** For Galois number fields `F → K` with the same ramification index at
`p`, the normalized `p`-adic discriminant exponents agree:
`v_p |disc K| · [F:ℚ] = v_p |disc F| · [K:ℚ]`. -/
theorem factorization_discr_mul_finrank_eq_of_ramificationIdxIn_eq {p : ℕ} (hp : p.Prime)
    (he : (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) =
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 F)) :
    (discr K).natAbs.factorization p * Module.finrank ℚ F =
      (discr F).natAbs.factorization p * Module.finrank ℚ K := by
  apply factorization_discr_mul_finrank_eq_of_unramifiedAbove F K hp
  apply isUnramifiedAt_of_ramificationIdx_le F K ((rationalPrimeIdeal p).ramificationIdxIn (𝓞 K))
  · intro Q hQ hpQ
    rw [he, ramificationIdx_eq_ramificationIdxIn F hp Q hpQ]
  · intro P hP hpP
    rw [ramificationIdx_eq_ramificationIdxIn K hp P hpP]

end Galois

section Unramified

variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

/-- A rational prime with ramification index one in a Galois number field does
not divide its discriminant. -/
theorem not_dvd_natAbs_discr_of_ramificationIdxIn_eq_one {p : ℕ} (hp : p.Prime)
    (he : (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) = 1) :
    ¬ p ∣ (discr K).natAbs := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h := (NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) hpZ).mpr
  rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs, dvd_abs]
  apply h
  intro P hP hpP
  have hpP' : (p : 𝓞 K) ∈ P := by
    have : ((p : ℤ) : 𝓞 K) ∈ P := hpP
    simpa using this
  apply Ideal.ramificationIdx_eq_one_iff.mp
  rw [ramificationIdx_eq_ramificationIdxIn K hp P hpP', he]

end Unramified

section RootDiscriminant

variable (K : Type*) [Field K] [NumberField K]

/-- **D4.** The logarithmic root discriminant as a weighted sum over the prime
divisors of the discriminant. -/
theorem log_rootDiscriminant_eq_sum (T : Finset ℕ)
    (hT : ∀ p, p.Prime → p ∣ (discr K).natAbs → p ∈ T) :
    Real.log (rootDiscriminant K) =
      ∑ p ∈ T, ((discr K).natAbs.factorization p : ℝ) / Module.finrank ℚ K * Real.log p := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hsupp : (discr K).natAbs.factorization.support ⊆ T := by
    intro p hp
    rw [Nat.support_factorization] at hp
    exact hT p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  rw [rootDiscriminant, Real.log_rpow (absoluteDiscriminant_pos K), absoluteDiscriminant,
    Real.log_nat_eq_sum_factorization,
    Finsupp.sum_of_support_subset _ hsupp _ (fun p _ => by simp), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  field_simp

/-- Root-discriminant bound from per-prime normalized exponents. -/
theorem log_rootDiscriminant_le_sum (T : Finset ℕ) (c : ℕ → ℝ)
    (hT : ∀ p, p.Prime → p ∣ (discr K).natAbs → p ∈ T)
    (hc : ∀ p ∈ T, ((discr K).natAbs.factorization p : ℝ) ≤ c p * Module.finrank ℚ K) :
    Real.log (rootDiscriminant K) ≤ ∑ p ∈ T, c p * Real.log p := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [log_rootDiscriminant_eq_sum K T hT]
  refine Finset.sum_le_sum fun p hp => ?_
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  apply mul_le_mul_of_nonneg_right _ hlog
  rw [div_le_iff₀ hn]
  exact hc p hp

end RootDiscriminant

end UnitDistance.Sqrt241.Discriminant
