module

public import UnitDistance.SigmaGenusGenerators
public import UnitDistance.GaloisEmbeddingConjugation
public import UnitDistance.ArithmeticGenusConjugation

@[expose] public section
set_option backward.privateInPublic true


/-! An actual complex conjugation of the maximal six-prime pro-two extension,
and its exact action on the actual genus field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP
open NumberField.ComplexEmbedding ArithmeticChosenGenus ArithmeticGenusFrattini

def sigmaComplexEmbedding : maximalSigmaProTwo →+* ℂ :=
  (IsAlgClosed.lift : maximalSigmaProTwo →ₐ[ℚ] ℂ).toRingHom

theorem exists_sigmaComplexConjugation :
    ∃ c : Gal(maximalSigmaProTwo/ℚ), IsConj sigmaComplexEmbedding c := by
  obtain ⟨ν,hν⟩ := exists_comp_symm_eq_of_comp_eq (k := ℚ)
    sigmaComplexEmbedding (conjugate sigmaComplexEmbedding) (RingHom.ext_rat _ _)
  exact ⟨ν.symm,hν.symm⟩

def sigmaComplexConjugation : Gal(maximalSigmaProTwo/ℚ) :=
  Classical.choose exists_sigmaComplexConjugation

theorem sigmaComplexConjugation_isConj : IsConj sigmaComplexEmbedding sigmaComplexConjugation :=
  Classical.choose_spec exists_sigmaComplexConjugation

theorem sigmaComplexConjugation_square : sigmaComplexConjugation^2=1 := by
  apply AlgEquiv.ext
  intro x
  change sigmaComplexConjugation (sigmaComplexConjugation x)=x
  exact isConj_apply_apply sigmaComplexConjugation_isConj x

/-- Complex conjugation has the specified imaginary genus coordinate and
zero in every positive-radical coordinate. -/
theorem sigmaComplexConjugation_genus :
    sigmaGenusRestriction sigmaComplexConjugation = genusBasis 0 := by
  let e : GenusField →ₐ[ℚ] maximalSigmaProTwo :=
    genusInMaximal.val.comp genusInMaximalEquiv.symm.toAlgHom
  have hc := GaloisEmbedding.restriction_isConj e sigmaComplexEmbedding
    sigmaComplexConjugation sigmaComplexConjugation_isConj
  have hs := conjugation_eq_sign (sigmaComplexEmbedding.comp e.toRingHom)
    (GaloisEmbedding.restriction e sigmaComplexConjugation) hc
  apply genusGaloisEquiv.injective
  change genusGaloisEquiv (genusGaloisEquiv.symm
    (AlgEquiv.autCongr genusInMaximalEquiv
      (sigmaComplexConjugation.restrictNormal genusInMaximal))) =
        signAutomorphism (Pi.single 0 1)
  rw [genusGaloisEquiv.apply_symm_apply, ← GaloisEmbedding.restriction_subfield]
  exact hs

theorem sigmaComplexConjugation_ne_one : sigmaComplexConjugation≠1 := by
  intro hc
  have h := sigmaComplexConjugation_genus
  rw [hc,map_one] at h
  have hv := congrArg (fun v : VectorGroup ↦ v.toAdd 0) h
  norm_num [genusBasis] at hv

theorem sigmaComplexConjugation_order : orderOf sigmaComplexConjugation=2 :=
  orderOf_eq_prime_iff.mpr ⟨sigmaComplexConjugation_square,sigmaComplexConjugation_ne_one⟩

end UnitDistance.ArithmeticProP
