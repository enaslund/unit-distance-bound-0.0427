module

public import UnitDistance.Sqrt241.Genus.Local
public import UnitDistance.Sqrt241.Analytic.Bridge

@[expose] public section
set_option backward.privateInPublic true


/-!
# Local types of the canonical genus field used by the analytic bridge

* at 2: `f ∣ 2` and `e f ≤ 8`;
* at every prime `p ∉ {2, 3, 5, 241}`: `e = 1` and `f ∣ 4`;
* if moreover `241` is a square mod `p`: `f ∣ 2`.

This gives `Analytic.GenusLocalTypes CanonicalGenus.Carrier` (29 and the nine
census primes split in `ℚ(√241)`, 7 is inert).
-/

noncomputable section
open NumberField

namespace UnitDistance.Sqrt241.Genus

open CanonicalGenus UnitDistance.NumberFieldAnalysis

/-- `e = 1` away from `2, 3, 5, 241`. -/
theorem ramificationIdxIn_eq_one (p : ℕ) [Fact p.Prime] (h964 : ¬ (p : ℤ) ∣ 964)
    (hN : ∀ i, ¬ (p : ℤ) ∣ 4 * normValue i) :
    (rationalPrimeIdeal p).ramificationIdxIn (𝓞 Carrier) = 1 := by
  obtain ⟨P, hP1, hP2⟩ := exists_prime_liesOver Carrier p
  exact ramificationIdxIn_eq_one_of_inertia P (inertia_trivial P h964 hN)

/-- `f ∣ 4` at every rational prime. -/
theorem inertiaDegIn_dvd_four (p : ℕ) [Fact p.Prime] :
    (rationalPrimeIdeal p).inertiaDegIn (𝓞 Carrier) ∣ 4 := by
  obtain ⟨P, hP1, hP2⟩ := exists_prime_liesOver Carrier p
  exact inertiaDegIn_dvd_of_stab_pow P 4 fun σ _ => aut_pow_four σ

/-- `f ∣ 2` when `241` is a square mod `p ∤ 964`. -/
theorem inertiaDegIn_dvd_two_of_sqrt (p : ℕ) [Fact p.Prime] (h964 : ¬ (p : ℤ) ∣ 964) (c : ℤ)
    (hc : (p : ℤ) ∣ c ^ 2 - 241) :
    (rationalPrimeIdeal p).inertiaDegIn (𝓞 Carrier) ∣ 2 := by
  obtain ⟨P, hP1, hP2⟩ := exists_prime_liesOver Carrier p
  refine inertiaDegIn_dvd_of_stab_pow P 2 fun σ hσ => ?_
  rw [sq]
  exact aut_sq_eq_one σ (stab_fix_bE_of_sqrt P h964 c hc hσ)

instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- `f ∣ 2` at 2. -/
theorem inertiaDegIn_two_dvd : (rationalPrimeIdeal 2).inertiaDegIn (𝓞 Carrier) ∣ 2 := by
  obtain ⟨P, hP1, hP2⟩ := exists_prime_liesOver Carrier 2
  refine inertiaDegIn_dvd_of_stab_pow P 2 fun σ hσ => ?_
  rw [sq]
  exact aut_sq_eq_one σ (stab_fix_bE_two P rfl hσ)

/-- `e f ≤ 8` at 2. -/
theorem ramification_mul_inertia_two_le :
    (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 Carrier) *
      (rationalPrimeIdeal 2).inertiaDegIn (𝓞 Carrier) ≤ 8 := by
  obtain ⟨P, hP1, hP2⟩ := exists_prime_liesOver Carrier 2
  exact ramificationIdxIn_mul_inertiaDegIn_le P 8 (card_stab_two_le P rfl)

/-- A square root of `241` modulo each prime used below. -/
def sqrt241Mod (p : ℕ) : ℤ :=
  if p = 29 then 3 else if p = 41 then 6 else if p = 47 then 10 else if p = 53 then 20
  else if p = 59 then 8 else if p = 61 then 27 else if p = 67 then 24 else if p = 79 then 2
  else if p = 83 then 18 else 12

theorem splitData : ∀ p ∈ ({29} : Finset ℕ) ∪ Analytic.censusPrimes,
    p.Prime ∧ ¬ (p : ℤ) ∣ 964 ∧ (∀ i, ¬ (p : ℤ) ∣ 4 * normValue i) ∧
      (p : ℤ) ∣ sqrt241Mod p ^ 2 - 241 := by
  decide +kernel

theorem sevenData : ¬ ((7 : ℕ) : ℤ) ∣ 964 ∧ (∀ i, ¬ ((7 : ℕ) : ℤ) ∣ 4 * normValue i) := by
  decide +kernel

/-- The local types of the canonical genus field required by the analytic bridge. -/
theorem genusLocalTypes : Analytic.GenusLocalTypes Carrier where
  two_dvd := inertiaDegIn_two_dvd
  two_le := ramification_mul_inertia_two_le
  twentyNine_e := by
    obtain ⟨hp, h964, hN, -⟩ := splitData 29 (by decide)
    have : Fact (Nat.Prime 29) := ⟨hp⟩
    exact ramificationIdxIn_eq_one 29 h964 hN
  twentyNine_f := by
    obtain ⟨hp, h964, -, hc⟩ := splitData 29 (by decide)
    have : Fact (Nat.Prime 29) := ⟨hp⟩
    exact inertiaDegIn_dvd_two_of_sqrt 29 h964 _ hc
  seven_e := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact ramificationIdxIn_eq_one 7 sevenData.1 sevenData.2
  seven_f := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact inertiaDegIn_dvd_four 7
  census_e := fun p hp => by
    obtain ⟨hpp, h964, hN, -⟩ := splitData p (Finset.mem_union_right _ hp)
    have : Fact p.Prime := ⟨hpp⟩
    exact ramificationIdxIn_eq_one p h964 hN
  census_f := fun p hp => by
    obtain ⟨hpp, h964, -, hc⟩ := splitData p (Finset.mem_union_right _ hp)
    have : Fact p.Prime := ⟨hpp⟩
    exact inertiaDegIn_dvd_two_of_sqrt p h964 _ hc

end UnitDistance.Sqrt241.Genus
