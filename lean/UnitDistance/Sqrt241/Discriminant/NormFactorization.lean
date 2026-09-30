module

public import UnitDistance.Sqrt241.Discriminant.Generic
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

@[expose] public section
set_option backward.privateInPublic true


/-!
# The `p`-adic valuation of an ideal norm

For a nonzero ideal `J` of `𝓞 K` and a rational prime `p`,

    v_p (N J) = Σ_{P | p} f(P|p) · mult_P J,

the sum running over the primes of `𝓞 K` above `p` (`factorization_absNorm_eq_sum`).
Together with `Σ_{P | p} e(P|p) f(P|p) = [K : ℚ]` this gives: if all primes above `p`
have ramification index `e` and `P^{d+1} ∤ J` for each of them, then
`e · v_p (N J) ≤ d · [K : ℚ]` (`mul_factorization_absNorm_le`).
-/

noncomputable section
open NumberField

namespace UnitDistance.Sqrt241.Discriminant

open UnitDistance.NumberFieldAnalysis

variable {K : Type*} [Field K] [NumberField K]

theorem rationalPrimeIdeal_ne_bot {p : ℕ} (hp : p.Prime) : rationalPrimeIdeal p ≠ ⊥ := by
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

theorem rationalPrimeIdeal_isMaximal {p : ℕ} (hp : p.Prime) :
    (rationalPrimeIdeal p).IsMaximal :=
  ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)).isMaximal (rationalPrimeIdeal_ne_bot hp)

omit [NumberField K] in
/-- A prime ideal contains `p` if and only if it lies over `p`. -/
theorem liesOver_rationalPrimeIdeal_iff {p : ℕ} (hp : p.Prime) (Q : Ideal (𝓞 K)) [hQ : Q.IsPrime] :
    Q.LiesOver (rationalPrimeIdeal p) ↔ (p : 𝓞 K) ∈ Q := by
  constructor
  · intro h
    have hmem : (p : ℤ) ∈ Q.under ℤ := by
      rw [← h.over]
      exact Ideal.subset_span (Set.mem_singleton _)
    change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ Q at hmem
    simpa only [map_natCast] using hmem
  · intro hpQ
    constructor
    have hle : rationalPrimeIdeal p ≤ Q.under ℤ := by
      rw [rationalPrimeIdeal, Ideal.span_le, Set.singleton_subset_iff]
      change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ Q
      simpa only [map_natCast] using hpQ
    exact (rationalPrimeIdeal_isMaximal hp).eq_of_le (Ideal.comap_ne_top _ hQ.ne_top) hle

omit [NumberField K] in
theorem mem_primesOver_iff {p : ℕ} (hp : p.Prime) (Q : Ideal (𝓞 K)) :
    Q ∈ (rationalPrimeIdeal p).primesOver (𝓞 K) ↔ Q.IsPrime ∧ (p : 𝓞 K) ∈ Q := by
  constructor
  · rintro ⟨hQ, hl⟩
    exact ⟨hQ, (liesOver_rationalPrimeIdeal_iff hp Q).mp hl⟩
  · rintro ⟨hQ, hpQ⟩
    exact ⟨hQ, (liesOver_rationalPrimeIdeal_iff hp Q).mpr hpQ⟩

/-- Multiplicity of a nonzero prime in another nonzero prime. -/
theorem multiplicity_prime_prime (q Q : Ideal (𝓞 K)) (hq : Prime q) (hQ : Prime Q) :
    multiplicity q Q = if q = Q then 1 else 0 := by
  have hQ0 : Q ≠ ⊥ := hQ.ne_zero
  have hfin : FiniteMultiplicity q Q := FiniteMultiplicity.of_prime_left hq hQ0
  split_ifs with h
  · subst h
    exact multiplicity_self hfin
  · rw [multiplicity_eq_zero hfin]
    intro hdvd
    have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
    have hqp : q.IsPrime := Ideal.isPrime_of_prime hq
    have hQmax : Q.IsMaximal := hQp.isMaximal hQ0
    have hle : Q ≤ q := Ideal.le_of_dvd hdvd
    exact h ((hQmax.eq_of_le hqp.ne_top hle).symm)

open Classical in
/-- The `p`-adic valuation of the norm of a nonzero prime ideal. -/
theorem factorization_absNorm_prime {p : ℕ} (hp : p.Prime) (Q : Ideal (𝓞 K)) (hQ : Prime Q) :
    (Ideal.absNorm Q).factorization p =
      if (p : 𝓞 K) ∈ Q then Q.inertiaDeg ℤ else 0 := by
  have hQ0 : Q ≠ ⊥ := hQ.ne_zero
  have hQp : Q.IsPrime := Ideal.isPrime_of_prime hQ
  split_ifs with hpQ
  · have : Q.LiesOver (rationalPrimeIdeal p) := (liesOver_rationalPrimeIdeal_iff hp Q).mpr hpQ
    have : (rationalPrimeIdeal p).IsMaximal := rationalPrimeIdeal_isMaximal hp
    have : Q.IsMaximal := hQp.isMaximal hQ0
    rw [← Ideal.natAbs_pow_inertiaDeg (p : ℤ) Q, Int.natAbs_natCast, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.Prime.factorization_self hp, smul_eq_mul, mul_one]
  · apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    obtain ⟨P, hPmax, hPunder, hPdvd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp Q hdvd
    have hPQ : P = Q := by
      have hle : Q ≤ P := Ideal.le_of_dvd hPdvd
      exact ((hQp.isMaximal hQ0).eq_of_le hPmax.ne_top hle).symm
    subst hPQ
    exact hpQ (natCast_mem_of_under_eq K P hPunder)

/-- **Norm factorization.** `v_p (N J) = Σ_{Q | p} f(Q|p) · mult_Q J` for `J ≠ 0`. -/
theorem factorization_absNorm_eq_sum {p : ℕ} (hp : p.Prime)
    [(rationalPrimeIdeal p).IsMaximal] (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    (Ideal.absNorm J).factorization p =
      ∑ q : (rationalPrimeIdeal p).primesOver (𝓞 K),
        q.1.inertiaDeg ℤ * multiplicity q.1 J := by
  have hprime : ∀ q : (rationalPrimeIdeal p).primesOver (𝓞 K), Prime q.1 := fun q => by
    have hq : q.1.IsPrime := q.2.1
    have : q.1.LiesOver (rationalPrimeIdeal p) := q.2.2
    exact Ideal.prime_of_isPrime
      (Ideal.ne_bot_of_liesOver_of_ne_bot (rationalPrimeIdeal_ne_bot hp) q.1) hq
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ
  | h₂ x hx =>
    rw [Ideal.isUnit_iff] at hx
    subst hx
    rw [Ideal.absNorm_top, Nat.factorization_one, Finsupp.zero_apply]
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [multiplicity_eq_zero_of_not_dvd, mul_zero]
    intro hdvd
    exact (hprime q).not_dvd_one (by simpa [Ideal.one_eq_top] using hdvd)
  | h₃ a Q ha hQ ih =>
    have hQ0 : Q ≠ ⊥ := hQ.ne_zero
    have hNQ : Ideal.absNorm Q ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact hQ0
    have hNa : Ideal.absNorm a ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact ha
    rw [map_mul, Nat.factorization_mul hNQ hNa, Finsupp.add_apply, ih ha,
      factorization_absNorm_prime hp Q hQ]
    have hmul : ∀ q : (rationalPrimeIdeal p).primesOver (𝓞 K),
        multiplicity q.1 (Q * a) = multiplicity q.1 Q + multiplicity q.1 a := fun q =>
      multiplicity_mul (hprime q)
        (FiniteMultiplicity.of_prime_left (hprime q) (mul_ne_zero hQ0 ha))
    simp_rw [hmul, mul_add, Finset.sum_add_distrib]
    congr 1
    simp_rw [multiplicity_prime_prime _ Q (hprime _) hQ]
    split_ifs with hpQ
    · have hQmem : Q ∈ (rationalPrimeIdeal p).primesOver (𝓞 K) :=
        (mem_primesOver_iff hp Q).mpr ⟨Ideal.isPrime_of_prime hQ, hpQ⟩
      rw [Finset.sum_eq_single ⟨Q, hQmem⟩]
      · simp
      · intro q _ hq
        rw [ite_eq_right (fun h => hq (Subtype.ext h)), mul_zero]
      · simp
    · symm
      apply Finset.sum_eq_zero
      intro q _
      rw [ite_eq_right, mul_zero]
      rintro rfl
      exact hpQ ((mem_primesOver_iff hp q.1).mp q.2).2

/-- **Norm bound.** If every prime above `p` has ramification index `e` and does not
divide `J` to the power `d + 1`, then `e · v_p (N J) ≤ d · [K : ℚ]`. -/
theorem mul_factorization_absNorm_le {p : ℕ} (hp : p.Prime) (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥)
    (e d : ℕ)
    (he : ∀ Q : Ideal (𝓞 K), Q.IsPrime → (p : 𝓞 K) ∈ Q → Q.ramificationIdx ℤ = e)
    (hd : ∀ Q : Ideal (𝓞 K), Q.IsPrime → (p : 𝓞 K) ∈ Q → ¬ Q ^ (d + 1) ∣ J) :
    e * (Ideal.absNorm J).factorization p ≤ d * Module.finrank ℚ K := by
  have := rationalPrimeIdeal_isMaximal hp
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (rationalPrimeIdeal p) (𝓞 K)
  rw [RingOfIntegers.rank] at hsum
  have hmem : ∀ q : (rationalPrimeIdeal p).primesOver (𝓞 K),
      q.1.IsPrime ∧ (p : 𝓞 K) ∈ q.1 := fun q => (mem_primesOver_iff hp q.1).mp q.2
  have hmult : ∀ q : (rationalPrimeIdeal p).primesOver (𝓞 K), multiplicity q.1 J ≤ d := by
    intro q
    obtain ⟨hq, hpq⟩ := hmem q
    have hq0 : q.1 ≠ ⊥ := by
      intro h
      rw [h, Ideal.mem_bot] at hpq
      exact hp.ne_zero (by exact_mod_cast hpq)
    have hfin : FiniteMultiplicity q.1 J :=
      FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hq0 hq) hJ
    by_contra hlt
    push Not at hlt
    exact hd q.1 hq hpq (hfin.pow_dvd_iff_le_multiplicity.mpr hlt)
  rw [factorization_absNorm_eq_sum hp J hJ, ← hsum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  obtain ⟨hq, hpq⟩ := hmem q
  rw [he q.1 hq hpq]
  calc e * (q.1.inertiaDeg ℤ * multiplicity q.1 J)
      ≤ e * (q.1.inertiaDeg ℤ * d) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hmult q))
    _ = d * (e * q.1.inertiaDeg ℤ) := by ring

end UnitDistance.Sqrt241.Discriminant
