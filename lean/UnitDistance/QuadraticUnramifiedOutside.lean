module

public import UnitDistance.QuadraticRamification

@[expose] public section
set_option backward.privateInPublic true


/-! Closure of actual finite ramification support under integral quadratic
norm extensions. The property is stated on actual prime ideals and actual
unramified local algebras. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField
namespace UnitDistance.QuadraticRamification
open UnitDistance.KummerInvariant

/-- Every actual prime away from the integer `N` is unramified over ℤ. -/
def UnramifiedAway (F : Type*) [Field F] [NumberField F] (N : ℤ) : Prop :=
  ∀ (P : Ideal (𝓞 F)) [P.IsPrime], (N : 𝓞 F) ∉ P → Algebra.IsUnramifiedAt ℤ P

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The rational field is unramified at all finite primes. -/
theorem unramifiedAway_rat (N : ℤ) : UnramifiedAway ℚ N := by
  intro P hP _
  apply not_dvd_differentIdeal_iff.mp
  have hd : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
    apply Ideal.absNorm_eq_one_iff.mp
    rw [absNorm_differentIdeal ℚ (𝓞 ℚ), discr_rat]
    norm_num
  rw [hd, Ideal.dvd_iff_le, top_le_iff]
  exact hP.ne_top

/-- Excluding `N` from a prime excludes every divisor of every power of `N`. -/
theorem not_mem_of_dvd_pow {A : Type*} [CommRing A]
    (P : Ideal A) [P.IsPrime] {N n : ℤ} (hN : (N:A) ∉ P)
    (hdiv : ∃ m : ℕ, n ∣ N^m) : (n:A) ∉ P := by
  intro hn
  obtain ⟨m,c,hc⟩ := hdiv
  have hpow : (N:A)^m ∈ P := by
    rw [← Int.cast_pow, hc, Int.cast_mul]
    exact P.mul_mem_right (c:A) hn
  have hmem : (N:A) ∈ P := (Ideal.IsPrime.mem_of_pow_mem inferInstance m hpow)
  exact hN hmem

variable [Algebra F K]

/-- Ramification support is preserved by an actual quadratic extension whose
integral radicand has an integral complementary factor supported on `N`. -/
theorem unramifiedAway_of_integral_product {N : ℤ}
    (hF : UnramifiedAway F N) (h2 : 2 ∣ N)
    (a b : 𝓞 F) (n : ℤ) (hab : a*b = n)
    (hn : ∃ m : ℕ, n ∣ N^m) (ha : Nonsquare (a:F))
    (x : 𝓞 K) (hx : x^2 = algebraMap (𝓞 F) (𝓞 K) a)
    (hgen : Algebra.adjoin F {(x:K)} = ⊤) : UnramifiedAway K N := by
  intro P hP hNP
  let p : Ideal (𝓞 F) := P.under (𝓞 F)
  haveI : p.IsPrime := inferInstanceAs (P.under (𝓞 F)).IsPrime
  haveI : P.LiesOver p := inferInstanceAs (P.LiesOver (P.under (𝓞 F)))
  have hpN : (N:𝓞 F) ∉ p := by
    intro h
    apply hNP
    have hm := (Ideal.mem_under (𝓞 F) P).mp h
    simpa only [map_intCast] using hm
  haveI : Algebra.IsUnramifiedAt ℤ p := hF p hpN
  haveI : Algebra.IsUnramifiedAt (𝓞 F) P :=
    isUnramifiedAt_of_integral_product F K a b n hab ha x hx hgen P
      (by
        rw [← Int.cast_two (R := 𝓞 K)]
        exact not_mem_of_dvd_pow P hNP ⟨1, by simpa using h2⟩)
      (not_mem_of_dvd_pow P hNP hn)
  exact Algebra.IsUnramifiedAt.comp p P

/-- Closure on the actual independently defined quadratic carrier. -/
theorem extension_unramifiedAway {N : ℤ} (hF : UnramifiedAway F N) (h2 : 2 ∣ N)
    (a b : 𝓞 F) (n : ℤ) (hab : a*b = n)
    (hn : ∃ m : ℕ, n ∣ N^m) [Fact (Nonsquare (a:F))] :
    UnramifiedAway (Extension (a:F)) N :=
  unramifiedAway_of_integral_product F (Extension (a:F)) hF h2 a b n hab hn Fact.out
    (integralSqrt F a) (integralSqrt_sq F a) (integralSqrt_adjoin F a)

/-- Integer radicands are a special case of the actual norm-extension closure. -/
theorem int_extension_unramifiedAway {N : ℤ} (hF : UnramifiedAway F N) (h2 : 2 ∣ N)
    (d : ℤ) (hd : ∃ m : ℕ, d ∣ N^m) [Fact (Nonsquare (d:F))] :
    UnramifiedAway (Extension (d:F)) N := by
  let L := Extension (d:F)
  let x : 𝓞 L := ⟨QuadraticAlgebra.omega, by
    apply IsIntegral.of_pow (n := 2) (by decide)
    have hs : (QuadraticAlgebra.omega : L)^2 = (d:L) := by
      ext <;> simp [L, pow_two]
    rw [hs]
    exact isIntegral_intCast d⟩
  have ha : Nonsquare ((d:𝓞 F):F) := by
    simpa using (Fact.out : Nonsquare (d:F))
  apply unramifiedAway_of_integral_product F L hF h2 (d:𝓞 F) 1 d (by simp) hd ha x
  · apply RingOfIntegers.coe_injective
    change (QuadraticAlgebra.omega : L)^2 = algebraMap (𝓞 F) L (d:𝓞 F)
    rw [map_intCast]
    ext <;> simp [L, pow_two]
  · apply top_unique
    intro z _
    have he : z = algebraMap F L z.re + algebraMap F L z.im*(x:L) := by
      ext <;> simp [x, L]
    rw [he]
    exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
        (Algebra.subset_adjoin (Set.mem_singleton _)))

end UnitDistance.QuadraticRamification
