module

public import UnitDistance.RationalFiniteFieldUnitsH2Reduction
public import UnitDistance.FiniteCyclicFinitePlaceH2

@[expose] public section
set_option backward.privateInPublic true


/-! Finite places jointly detect field-unit H² for every finite rational
Galois 2-extension. The proof uses the checked complete global norm closure. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
namespace UnitDistance.ArithmeticProP

local instance rationalFinalAdicAlgebra (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (v.adicCompletion ℚ) :=
  HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v

variable (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]

/-- Global reciprocity and cyclic Hasse norm detection discharge the only
remaining cyclic input for the actual Q(i)-compositum reduction. -/
theorem imaginaryFieldUnitsFiniteDetection : ImaginaryFieldUnitsFiniteDetection := by
  intro x hx
  exact finiteCyclicFieldUnitsH2_eq_zero_of_finiteTensor_eq_zero
    ℚ ImaginaryQuadratic.Carrier x hx

/-- A displayed imaginary root permits direct restriction to Q(i). -/
theorem rationalFieldUnitsH2_eq_zero_of_finite_localizations_of_root
    (hP : IsPGroup 2 Gal(L/ℚ)) (i : L) (hi : i^2 = -1)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2)
    (hx : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (fieldUnitsTensorH2 ℚ L (v.adicCompletion ℚ)).hom x = 0) : x = 0 :=
  rationalFieldUnitsH2_detection_of_root_of_imaginary_detection L
    imaginaryFieldUnitsFiniteDetection hP i hi x hx

/-- Actual finite tensor localizations jointly detect all degree-two
field-unit classes in every finite rational Galois 2-extension. -/
theorem rationalFieldUnitsH2_eq_zero_of_finite_localizations
    (hP : IsPGroup 2 Gal(L/ℚ))
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2)
    (hx : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (fieldUnitsTensorH2 ℚ L (v.adicCompletion ℚ)).hom x = 0) : x = 0 :=
  rationalFieldUnitsH2_detection_of_imaginary_detection L
    imaginaryFieldUnitsFiniteDetection hP x hx

end UnitDistance.ArithmeticProP
