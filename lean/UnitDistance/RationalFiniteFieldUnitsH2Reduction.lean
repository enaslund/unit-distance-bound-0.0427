module

public import UnitDistance.TotallyComplexFieldUnitsH2
public import UnitDistance.FiniteTensorTowerDetection
public import UnitDistance.ImaginaryGaloisEnlargement

@[expose] public section
set_option backward.privateInPublic true


/-! Actual rational 2-extensions reduce finite-place H² detection to the
single cyclic field Q(i). The cyclic detection premise is explicit here;
the separate global Artin/norm argument will discharge it. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
namespace UnitDistance.ArithmeticProP

-- Fix the actual completion algebra, which differs definitionally from the
-- generic rational algebra on a characteristic-zero field.
local instance rationalAdicAlgebra (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (v.adicCompletion ℚ) :=
  HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
open ClassFieldTower.Cohomology

variable (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]

/-- The remaining cyclic detection assertion for the actual field Q(i). -/
def ImaginaryFieldUnitsFiniteDetection : Prop :=
  ∀ x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ ImaginaryQuadratic.Carrier) 2,
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
      (fieldUnitsTensorH2 ℚ ImaginaryQuadratic.Carrier (v.adicCompletion ℚ)).hom x = 0) →
    x = 0

set_option maxHeartbeats 300000 in
/-- The actual totally-complex detector and tower exactness reduce a displayed
imaginary-root extension to its actual cyclic Q(i) subfield. -/
theorem rationalFieldUnitsH2_detection_of_root_of_imaginary_detection
    (hcyc : ImaginaryFieldUnitsFiniteDetection)
    (hP : IsPGroup 2 Gal(L/ℚ)) (i : L) (hi : i^2 = -1)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2)
    (hx : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (fieldUnitsTensorH2 ℚ L (v.adicCompletion ℚ)).hom x = 0) : x = 0 := by
  let F := ImaginaryQuadratic.Carrier
  let e : F →ₐ[ℚ] L := ImaginaryQuadratic.embedding i hi
  letI : Algebra F L := e.toRingHom.toAlgebra
  letI : IsScalarTower ℚ F L := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (e.commutes a).symm)
  letI : IsGalois F L := IsGalois.tower_top_of_isGalois ℚ F L
  have hPF : IsPGroup 2 Gal(L/F) := hP.of_injective
    (AlgEquiv.restrictScalarsHom ℚ) (AlgEquiv.restrictScalars_injective ℚ)
  exact fieldUnitsH2_finite_detection_tower ℚ F L
    (fieldUnitsH2_eq_zero_of_finite_localizations F L (p := 2) hPF) hcyc x hx

/-- Actual inflation into the literal compositum with Q(i), followed by
actual local vanishing reflection, handles every rational Galois 2-extension. -/
theorem rationalFieldUnitsH2_detection_of_imaginary_detection
    (hcyc : ImaginaryFieldUnitsFiniteDetection)
    (hP : IsPGroup 2 Gal(L/ℚ))
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits ℚ L) 2)
    (hx : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (fieldUnitsTensorH2 ℚ L (v.adicCompletion ℚ)).hom x = 0) : x = 0 := by
  let N := imaginaryGaloisEnlargement L
  letI : IsGalois ℚ N := N.isGalois
  let e : L →ₐ[ℚ] N := imaginaryGaloisEnlargementEmbedding L
  letI : Algebra L N := e.toRingHom.toAlgebra
  letI : IsScalarTower ℚ L N := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (e.commutes a).symm)
  obtain ⟨i,hi⟩ := imaginaryGaloisEnlargement_has_root L
  have hN : (finiteGaloisTowerUnitsH2Inflation ℚ L N).hom x = 0 := by
    apply rationalFieldUnitsH2_detection_of_root_of_imaginary_detection N hcyc
      (imaginaryGaloisEnlargement_isPGroup L hP) i hi
    intro v
    exact (finiteFieldUnitsTensor_inflation_eq_zero_iff ℚ L N v x).mpr (hx v)
  apply finiteGaloisTowerUnitsH2Inflation_injective ℚ L N
  simpa only [map_zero] using hN

end UnitDistance.ArithmeticProP
