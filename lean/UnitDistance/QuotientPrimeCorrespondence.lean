module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
set_option backward.privateInPublic true


/-! Residue ring equivalences under the actual ideal correspondence. -/
noncomputable section
namespace UnitDistance.QuotientPrimeCorrespondence
open Ideal IsDedekindDomain
variable {R A : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing A] [IsDedekindDomain A] {I : Ideal R} {J : Ideal A}

/-- An equivalence of quotients by two ideals induces equivalences of
residue rings for the ideals in their divisor correspondence. -/
def quotientEquivIdealFactor (e : R ⧸ I ≃+* A ⧸ J) (L : Ideal R) (hL : L ∣ I) :
    R ⧸ L ≃+* A ⧸ (IsDedekindDomain.idealFactorsEquivOfQuotEquiv e ⟨L,hL⟩ : Ideal A) := by
  let M := (L.map (Ideal.Quotient.mk I)).map e.toRingHom
  let q := Ideal.quotientMap M (Ideal.Quotient.mk J) le_rfl
  have hq : Function.Bijective q :=
    ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩
  exact (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.dvd_iff_le.mp hL)).symm.trans
    ((Ideal.quotientEquiv (L.map (Ideal.Quotient.mk I)) M e rfl).trans
      (RingEquiv.ofBijective q hq).symm)


def quotientEquivNormalizedFactor (e : R ⧸ I ≃+* A ⧸ J) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (L : {L : Ideal R // L ∈ UniqueFactorizationMonoid.normalizedFactors I}) :
    R ⧸ L.val ≃+* A ⧸ (IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv e hI hJ L).val :=
  quotientEquivIdealFactor e L.val
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors L.prop)

end UnitDistance.QuotientPrimeCorrespondence
