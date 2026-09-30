module

public import UnitDistance.PrimeNormCounts
public import Mathlib.NumberTheory.RamificationInertia.Galois

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true


/-! Exact prime-norm counts from actual Galois ramification and residue degrees. -/
noncomputable section
open NumberField IsDedekindDomain
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
variable (p : ℕ) (hp : p.Prime)

abbrev rationalPrimeIdeal : Ideal ℤ := Ideal.span {(p : ℤ)}

/-- A norm fiber is the actual set of primes over `p` when the actual common
residue degree is `f`. -/
def primeNormFiberEquivPrimesOver (f : ℕ) (hf : 0 < f)
    (hres : (rationalPrimeIdeal p).inertiaDegIn (𝓞 K) = f) :
    PrimeNormFiber K (p^f) ≃ (rationalPrimeIdeal p).primesOver (𝓞 K) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : rationalPrimeIdeal p ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hpf : 1 < p^f := Nat.one_lt_pow hf.ne' hp.one_lt
  refine {
    toFun := fun P => ⟨P.1.asIdeal, P.1.isPrime, ?_⟩
    invFun := fun Q => ⟨⟨Q.1,Q.2.1,Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q.1⟩,?_⟩
    left_inv := fun P => by apply Subtype.ext; rfl
    right_inv := fun Q => rfl }
  · have h := primeNormFiber_liesOver K hpf P
    simpa only [hp.pow_minFac hf.ne'] using h
  · letI := Q.2.1
    letI := Q.2.2
    letI : Q.1.IsMaximal := Q.2.1.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q.1)
    rw [Ideal.absNorm_eq_pow_inertiaDeg' Q.1 hp]
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (rationalPrimeIdeal p) Q.1 Gal(K/ℚ), hres]

include hp in
/-- The exact Galois `efg=[K:Q]` identity, expressed using actual norm counts. -/
theorem primeNormCount_mul_ramification_residue (e f : ℕ) (hf : 0 < f)
    (he : (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) = e)
    (hres : (rationalPrimeIdeal p).inertiaDegIn (𝓞 K) = f) :
    primeNormCount K (p^f) * (e*f) = Module.finrank ℚ K := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (rationalPrimeIdeal p) (𝓞 K) Gal(K/ℚ)
  rw [he,hres,IsGalois.card_aut_eq_finrank] at h
  rw [primeNormCount,Nat.card_congr (primeNormFiberEquivPrimesOver K p hp f hf hres),
    Nat.card_coe_set_eq]
  exact h

end UnitDistance.NumberFieldAnalysis
