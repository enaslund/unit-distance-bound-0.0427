module

public import UnitDistance.SigmaPrimeSupport
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.RamificationSupport
public import UnitDistance.UnramifiedAwayEquiv

@[expose] public section
set_option backward.privateInPublic true


/-! Agreement between the actual six-prime support and the local ramification
predicate proved for the catalog fields. -/
noncomputable section
open NumberField IsDedekindDomain
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.Sawin QuadraticRamification
variable (K : Type*) [Field K] [NumberField K]

/-- The actual local support theorem gives the actual finite-place condition
used in the maximal pro-2 compositum. -/
theorem unramifiedOutsideSigma_of_unramifiedAway
    (h : UnramifiedAway K 30030) :
    IsUnramifiedAtFinitePlacesOutside ℚ K sigmaPrimeSupport := by
  intro P hP
  have hN : (30030:𝓞 K) ∉ P.asIdeal := by
    intro hNP
    apply hP
    rw [mem_sigmaPrimeSupport_iff]
    change algebraMap (𝓞 ℚ) (𝓞 K) (30030:𝓞 ℚ) ∈ P.asIdeal
    simpa only [map_ofNat] using hNP
  letI : Algebra.IsUnramifiedAt ℤ P.asIdeal := h P.asIdeal (by simpa using hN)
  exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ P.asIdeal

end UnitDistance.ArithmeticProP
