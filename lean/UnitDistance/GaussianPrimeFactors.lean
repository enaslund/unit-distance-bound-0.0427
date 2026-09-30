module

public import UnitDistance.GaussianQuadraticOrder
public import UnitDistance.QuotientPolynomialCorrespondence
public import UnitDistance.FiniteGaussianEuler
public import UnitDistance.HeckeNormCharacter
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

@[expose] public section
set_option backward.privateInPublic true


/-! Exact Euler factors of the actual quadratic extension adjoining sqrt(-1), away from 2. -/
noncomputable section
namespace UnitDistance.GaussianQuadraticOrder
open NumberField Polynomial UniqueFactorizationMonoid
open scoped Classical BigOperators
attribute [local instance] Ideal.Quotient.field
set_option backward.isDefEq.respectTransparency false
variable (F : Type*) [Field F] [NumberField F] [Fact (KummerInvariant.Nonsquare (-1:F))]
variable (P : Ideal (𝓞 F)) [P.IsMaximal]

abbrev primeMap : Ideal (𝓞 (GaussianField F)) :=
  P.map (algebraMap (𝓞 F) (𝓞 (GaussianField F)))

abbrev residuePolynomial : (𝓞 F ⧸ P)[X] := X^2-C (-1:𝓞 F ⧸ P)

theorem primeMap_ne_bot (hP : P ≠ ⊥) : primeMap F P ≠ ⊥ := by
  rwa [primeMap, ne_eq, Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 (GaussianField F)))]

theorem residuePolynomial_ne_zero : residuePolynomial F P ≠ 0 :=
  (monic_X_pow_sub_C (-1:𝓞 F ⧸ P) (by decide)).ne_zero

/-- Correspondence with actual monic factors of the quadratic residue polynomial. -/
def oddPrimeFactorEquiv (hP : P ≠ ⊥) (h2 : (2:𝓞 F) ∉ P) :
    {Q : Ideal (𝓞 (GaussianField F)) // Q ∈ normalizedFactors (primeMap F P)} ≃
      {g : (𝓞 F ⧸ P)[X] // g ∈ normalizedFactors (residuePolynomial F P)} :=
  QuotientPolynomialCorrespondence.factorEquiv (oddPrimeQuotientEquiv F P h2)
    (primeMap_ne_bot F P hP) (residuePolynomial_ne_zero F P)

theorem oddPrimeFactor_norm (hP : P ≠ ⊥) (h2 : (2:𝓞 F) ∉ P)
    (Q : {Q : Ideal (𝓞 (GaussianField F)) // Q ∈ normalizedFactors (primeMap F P)}) :
    Ideal.absNorm Q.val = Ideal.absNorm P ^ (oddPrimeFactorEquiv F P hP h2 Q).val.natDegree := by
  exact QuotientPolynomialCorrespondence.residue_natCard (oddPrimeQuotientEquiv F P h2)
    (primeMap_ne_bot F P hP) (residuePolynomial_ne_zero F P) Q

theorem residue_ringChar_ne_two (h2 : (2:𝓞 F) ∉ P) : ringChar (𝓞 F ⧸ P) ≠ 2 := by
  intro hc
  have hh := CharP.cast_eq_zero (𝓞 F ⧸ P) (ringChar (𝓞 F ⧸ P))
  rw [hc] at hh
  apply h2
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  norm_num only [map_ofNat, Nat.cast_ofNat] at hh ⊢
  exact hh

/-- Finite-prime Euler factor equality with the actual norm character. -/
theorem oddPrime_factor_product (hP : P ≠ ⊥) (h2 : (2:𝓞 F) ∉ P) (s : ℂ) :
    (∏ Q ∈ (normalizedFactors (primeMap F P)).toFinset,
      (1-(Ideal.absNorm Q:ℂ)^(-s))) =
      (1-(Ideal.absNorm P:ℂ)^(-s)) *
        (1-NumberFieldAnalysis.chiFourComplex (Ideal.absNorm P)*(Ideal.absNorm P:ℂ)^(-s)) := by
  let k := 𝓞 F ⧸ P
  letI : Fintype k := Fintype.ofFinite k
  let e : ↥(normalizedFactors (primeMap F P)).toFinset ≃
      ↥(normalizedFactors (residuePolynomial F P)).toFinset :=
    (Equiv.subtypeEquivRight (fun Q => Multiset.mem_toFinset)).trans
      ((oddPrimeFactorEquiv F P hP h2).trans
        (Equiv.subtypeEquivRight (fun g => Multiset.mem_toFinset.symm)))
  have hnorm (Q : ↥(normalizedFactors (primeMap F P)).toFinset) :
      Ideal.absNorm Q.val = Ideal.absNorm P ^ (e Q).val.natDegree :=
    oddPrimeFactor_norm F P hP h2 ⟨Q.val,Multiset.mem_toFinset.mp Q.prop⟩
  calc
    _ = ∏ Q : ↥(normalizedFactors (primeMap F P)).toFinset,
        (1-(Ideal.absNorm Q.val:ℂ)^(-s)) := (Finset.prod_coe_sort _ _).symm
    _ = ∏ Q : ↥(normalizedFactors (primeMap F P)).toFinset,
        (1-((Ideal.absNorm P:ℂ)^(-s))^(e Q).val.natDegree) := by
      apply Finset.prod_congr rfl
      intro Q _
      rw [hnorm Q, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
        Complex.cpow_nat_mul]
    _ = ∏ g : ↥(normalizedFactors (residuePolynomial F P)).toFinset,
        (1-((Ideal.absNorm P:ℂ)^(-s))^g.val.natDegree) :=
      e.prod_comp (fun g => 1-((Ideal.absNorm P:ℂ)^(-s))^g.val.natDegree)
    _ = ∏ g ∈ (normalizedFactors (residuePolynomial F P)).toFinset,
        (1-((Ideal.absNorm P:ℂ)^(-s))^g.natDegree) :=
      Finset.prod_coe_sort (normalizedFactors (residuePolynomial F P)).toFinset
        (fun g : (𝓞 F ⧸ P)[X] => 1-((Ideal.absNorm P:ℂ)^(-s))^g.natDegree)
    _ = _ := by
      have h := FiniteGaussianEuler.factor_product k (residue_ringChar_ne_two F P h2)
        ((Ideal.absNorm P:ℂ)^(-s))
      have hcard : Fintype.card k = Ideal.absNorm P := by
        rw [← Nat.card_eq_fintype_card]
        rfl
      rw [hcard] at h
      exact h

end UnitDistance.GaussianQuadraticOrder
