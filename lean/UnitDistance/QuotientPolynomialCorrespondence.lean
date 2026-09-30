module

public import UnitDistance.QuotientPrimeCorrespondence
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Finiteness

@[expose] public section
set_option backward.privateInPublic true


/-! The actual residue cardinalities in polynomial factor correspondence. -/
noncomputable section
namespace UnitDistance.QuotientPolynomialCorrespondence
open Ideal IsDedekindDomain Polynomial UniqueFactorizationMonoid
open scoped Classical
variable {R k : Type*} [CommRing R] [IsDedekindDomain R] [Field k]
  {I : Ideal R} {f : k[X]}

def factorEquiv (e : R ⧸ I ≃+* k[X] ⧸ Ideal.span {f}) (hI : I ≠ ⊥) (hf : f ≠ 0) :
    {P : Ideal R // P ∈ normalizedFactors I} ≃ {g : k[X] // g ∈ normalizedFactors f} :=
  (IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv e hI
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hf)).trans
      (Ideal.normalizedFactorsEquivSpanNormalizedFactors hf).symm

theorem span_factorEquiv (e : R ⧸ I ≃+* k[X] ⧸ Ideal.span {f})
    (hI : I ≠ ⊥) (hf : f ≠ 0) (P : {P : Ideal R // P ∈ normalizedFactors I}) :
    Ideal.span {(factorEquiv e hI hf P).val} =
      (IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv e hI
        (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hf) P).val := by
  exact congrArg Subtype.val ((Ideal.normalizedFactorsEquivSpanNormalizedFactors hf).apply_symm_apply _)

def residueEquiv (e : R ⧸ I ≃+* k[X] ⧸ Ideal.span {f})
    (hI : I ≠ ⊥) (hf : f ≠ 0) (P : {P : Ideal R // P ∈ normalizedFactors I}) :
    R ⧸ P.val ≃+* k[X] ⧸ Ideal.span {(factorEquiv e hI hf P).val} :=
  (QuotientPrimeCorrespondence.quotientEquivNormalizedFactor e hI
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hf) P).trans
      (Ideal.quotEquivOfEq (span_factorEquiv e hI hf P).symm)

theorem residue_natCard [Finite k] (e : R ⧸ I ≃+* k[X] ⧸ Ideal.span {f})
    (hI : I ≠ ⊥) (hf : f ≠ 0) (P : {P : Ideal R // P ∈ normalizedFactors I}) :
    Nat.card (R ⧸ P.val) = Nat.card k ^ (factorEquiv e hI hf P).val.natDegree := by
  let g := factorEquiv e hI hf P
  have hmonic : g.val.Monic := ((Polynomial.mem_normalizedFactors_iff hf).mp g.prop).2.1
  letI : Module.Finite k (k[X] ⧸ Ideal.span {g.val}) := hmonic.finite_quotient
  rw [Nat.card_congr (residueEquiv e hI hf P).toEquiv,
    Module.natCard_eq_pow_finrank (K := k), finrank_quotient_span_eq_natDegree]

end UnitDistance.QuotientPolynomialCorrespondence
