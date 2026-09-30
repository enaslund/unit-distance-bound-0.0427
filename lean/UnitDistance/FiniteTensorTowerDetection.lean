module

public import UnitDistance.FiniteTensorBaseChangeH2
public import UnitDistance.FiniteTensorGaloisInflationH2

@[expose] public section
set_option backward.privateInPublic true


/-! Closure of actual finite-place H² detection under a finite Galois tower.
The two displayed detection premises are explicit; this lemma alone is not a
global arithmetic detection theorem. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.Cohomology

variable (K F L : Type) [Field K] [NumberField K] [Field F] [NumberField F]
variable [Field L] [NumberField L]
variable [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
variable [FiniteDimensional K F] [FiniteDimensional K L]
variable [IsGalois K F] [IsGalois K L]

/-- Actual tower exactness and the proved local restriction/inflation maps
combine finite-place detection for the two successive field extensions. -/
theorem fieldUnitsH2_finite_detection_tower
    (hrelative : ∀ y : groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2,
      (∀ w : HeightOneSpectrum (𝓞 F),
        (fieldUnitsTensorH2 F L (w.adicCompletion F)).hom y = 0) → y = 0)
    (hlower : ∀ y : groupCohomology (Rep.ofAlgebraAutOnUnits K F) 2,
      (∀ v : HeightOneSpectrum (𝓞 K),
        (fieldUnitsTensorH2 K F (v.adicCompletion K)).hom y = 0) → y = 0)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K),
      (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom x = 0) : x = 0 := by
  have hres : (finiteGaloisTowerUnitsH2Restriction K F L).hom x = 0 := by
    apply hrelative
    intro w
    exact finiteFieldUnitsTensorRestriction_eq_zero_of_eq_zero K F L
      (finitePlaceBelow (K := K) w) ⟨w,rfl⟩ x (hx _)
  obtain ⟨y,hy⟩ := finiteGaloisTowerUnitsH2Restriction_ker_le_inflation_range
    K F L hres
  have hy0 : y = 0 := by
    apply hlower
    intro v
    apply (finiteFieldUnitsTensor_inflation_eq_zero_iff K F L v y).mp
    rw [hy]
    exact hx v
  rw [← hy,hy0,map_zero]

end UnitDistance.ArithmeticProP
