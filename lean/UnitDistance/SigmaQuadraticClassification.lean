module

public import UnitDistance.SigmaFiniteFieldInclusion
public import UnitDistance.ProPOpenNormalStage
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.RationalRamificationSupport
public import UnitDistance.ArithmeticQuadraticClassification

@[expose] public section
set_option backward.privateInPublic true


/-! All actual quadratic layers of the maximal six-prime pro-two extension
are contained in the actual seven-root genus field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain
open scoped NumberField
namespace UnitDistance.ArithmeticProP
open ArithmeticChosenGenus

private instance finiteLayerNumberField
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) : NumberField E :=
  NumberField.of_module_finite ℚ E

/-- The actual finite-place condition gives the signed discriminant
classification, with no real-place restriction. -/
theorem admissible_quadratic_le_genusImage
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hdegree : Module.finrank ℚ E = 2)
    (hE : IsAdmissibleFiniteLayer 2 sigmaPrimeSupport E) :
    E.toIntermediateField ≤ (finiteGaloisImage GenusField).toIntermediateField := by
  apply quadratic_le_genusImage_of_discriminant_support E hdegree
  intro p hp hpd
  have hq := (ClassFieldTower.Sawin.isUnramifiedAtFinitePlacesOutside_rat_iff_discr
    E sigmaPrimeSupport).mp hE.2 ⟨p, hp⟩ hpd
  change (Rat.HeightOneSpectrum.primesEquiv
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩) : ℕ) ∈
      sigmaRationalPrimes at hq
  simpa only [Equiv.apply_symm_apply, sigmaRationalPrimes, finitePrimeSupport] using hq

/-- The actual genus-field image is itself in the maximal pro-two extension. -/
theorem genusImage_le_maximalSigmaProTwo :
    (finiteGaloisImage GenusField).toIntermediateField ≤ maximalSigmaProTwo := by
  apply finiteGaloisImage_le_maximalSigmaProTwo GenusField
  · exact IsPGroup.of_card (n := 7) genusField_galoisGroup_card
  · exact genusField_unramifiedAway

/-- The actual genus field considered as a subfield of the maximal extension. -/
def genusInMaximal : IntermediateField ℚ maximalSigmaProTwo :=
  IntermediateField.restrict genusImage_le_maximalSigmaProTwo

/-- This subfield is equivalent to the actual seven-root genus field. -/
def genusInMaximalEquiv : genusInMaximal ≃ₐ[ℚ] GenusField :=
  (IntermediateField.restrict_algEquiv genusImage_le_maximalSigmaProTwo).symm.trans
    (finiteGaloisImageEquiv GenusField).symm

instance genusInMaximal_finite : Module.Finite ℚ genusInMaximal := by
  exact genusInMaximalEquiv.symm.toLinearEquiv.finiteDimensional

instance genusInMaximal_galois : IsGalois ℚ genusInMaximal :=
  IsGalois.of_algEquiv genusInMaximalEquiv.symm

/-- Every actual quadratic fixed field of the maximal Galois group lies in
its actual genus subfield. Neither generation nor Frattini finiteness is assumed. -/
theorem indexTwo_fixedField_le_genusInMaximal
    (U : OpenNormalSubgroup Gal(maximalSigmaProTwo/ℚ))
    (hindex : (U : Subgroup Gal(maximalSigmaProTwo/ℚ)).index = 2) :
    IntermediateField.fixedField (U : Subgroup Gal(maximalSigmaProTwo/ℚ)) ≤ genusInMaximal := by
  let S := proPOpenNormalStage 2 sigmaPrimeSupport U
  have hdegree : Module.finrank ℚ S.val = 2 := by
    letI : IsGalois ℚ S.val.toIntermediateField := S.val.isGalois
    calc
      Module.finrank ℚ S.val = Nat.card Gal(S.val/ℚ) :=
        (IsGalois.card_aut_eq_finrank ℚ S.val).symm
      _ = Nat.card (Gal(maximalSigmaProTwo/ℚ) ⧸ (U : Subgroup Gal(maximalSigmaProTwo/ℚ))) :=
        (Nat.card_congr (proPOpenNormalQuotientEquivStage 2 sigmaPrimeSupport U).toEquiv).symm
      _ = (U : Subgroup Gal(maximalSigmaProTwo/ℚ)).index := (Subgroup.index_eq_card _).symm
      _ = 2 := hindex
  have hclass := admissible_quadratic_le_genusImage S.val hdegree S.property
  have hlift : IntermediateField.lift
      (IntermediateField.fixedField (U : Subgroup Gal(maximalSigmaProTwo/ℚ))) ≤
        (finiteGaloisImage GenusField).toIntermediateField := by
    rw [← proPOpenNormalStage_field 2 sigmaPrimeSupport U]
    exact hclass
  intro x hx
  apply (IntermediateField.mem_restrict genusImage_le_maximalSigmaProTwo x).mpr
  exact hlift ⟨x, hx, rfl⟩

end UnitDistance.ArithmeticProP
