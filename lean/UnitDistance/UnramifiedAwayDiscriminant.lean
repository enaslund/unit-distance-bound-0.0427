module

public import UnitDistance.QuadraticUnramifiedOutside

@[expose] public section
set_option backward.privateInPublic true


/-! Rational prime and actual discriminant consequences of finite ramification support. -/
noncomputable section
open NumberField
namespace UnitDistance.QuadraticRamification
variable {F : Type*} [Field F] [NumberField F] {N : ℤ}

theorem UnramifiedAway.at_prime (hF : UnramifiedAway F N)
    (p : ℤ) (P : Ideal (𝓞 F)) [P.IsPrime] [P.LiesOver (Ideal.span {p})]
    (hp : ¬ p ∣ N) : Algebra.IsUnramifiedAt ℤ P := by
  apply hF P
  intro hN
  apply hp
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.mem_of_liesOver P (Ideal.span {p}) N).mpr
  rw [algebraMap_int_eq]
  change (N : 𝓞 F) ∈ P
  exact hN

/-- The independently defined field discriminant has no prime factors outside N. -/
theorem UnramifiedAway.not_dvd_discr (hF : UnramifiedAway F N)
    {p : ℤ} (hp : Prime p) (hpN : ¬ p ∣ N) : ¬ p ∣ discr F := by
  apply (NumberField.not_dvd_discr_iff_forall_liesOver F (𝓞 F) hp).mpr
  intro P hP hOver
  letI := hP
  letI := hOver
  exact hF.at_prime p P hpN

theorem UnramifiedAway.prime_dvd_of_dvd_discr (hF : UnramifiedAway F N)
    {p : ℤ} (hp : Prime p) (hpd : p ∣ discr F) : p ∣ N := by
  by_contra hN
  exact hF.not_dvd_discr hp hN hpd

end UnitDistance.QuadraticRamification
