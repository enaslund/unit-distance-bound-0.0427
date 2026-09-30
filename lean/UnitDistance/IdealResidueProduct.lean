module

public import UnitDistance.QuotientPrimeCorrespondence

@[expose] public section
set_option backward.privateInPublic true


/-! Products of residue-cardinality factors are invariant under quotient equivalence. -/
noncomputable section
namespace UnitDistance.QuotientPrimeCorrespondence
open UniqueFactorizationMonoid
open scoped Classical BigOperators
variable {R A M : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing A] [IsDedekindDomain A] [CommMonoid M] {I : Ideal R} {J : Ideal A}

theorem prod_residue_natCard (e : R ⧸ I ≃+* A ⧸ J) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (g : ℕ → M) :
    (∏ P ∈ (normalizedFactors I).toFinset, g (Nat.card (R ⧸ P))) =
      ∏ Q ∈ (normalizedFactors J).toFinset, g (Nat.card (A ⧸ Q)) := by
  let e' : ↥(normalizedFactors I).toFinset ≃ ↥(normalizedFactors J).toFinset :=
    (Equiv.subtypeEquivRight (fun P => Multiset.mem_toFinset)).trans
      ((IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv e hI hJ).trans
        (Equiv.subtypeEquivRight (fun Q => Multiset.mem_toFinset.symm)))
  have hcard (P : ↥(normalizedFactors I).toFinset) :
      Nat.card (R ⧸ P.val) = Nat.card (A ⧸ (e' P).val) :=
    Nat.card_congr (quotientEquivNormalizedFactor e hI hJ
      ⟨P.val,Multiset.mem_toFinset.mp P.prop⟩).toEquiv
  calc
    _ = ∏ P : ↥(normalizedFactors I).toFinset, g (Nat.card (R ⧸ P.val)) :=
      (Finset.prod_coe_sort (normalizedFactors I).toFinset (fun P => g (Nat.card (R ⧸ P)))).symm
    _ = ∏ P : ↥(normalizedFactors I).toFinset, g (Nat.card (A ⧸ (e' P).val)) := by
      apply Finset.prod_congr rfl
      exact fun P _ => congrArg g (hcard P)
    _ = ∏ Q : ↥(normalizedFactors J).toFinset, g (Nat.card (A ⧸ Q.val)) :=
      e'.prod_comp (fun Q => g (Nat.card (A ⧸ Q.val)))
    _ = _ := Finset.prod_coe_sort (normalizedFactors J).toFinset (fun Q => g (Nat.card (A ⧸ Q)))

end UnitDistance.QuotientPrimeCorrespondence
