module

public import UnitDistance.RationalPrimeCompletionValuation
public import UnitDistance.GaloisEmbeddingRestriction
public import Mathlib.Algebra.Algebra.Hom.Rat

@[expose] public section
set_option backward.privateInPublic true


/-! The chosen rational absolute decomposition comparison acts on an actual
embedding of the rational algebraic closure into the local separable closure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open scoped NumberField ValuativeRel
namespace UnitDistance.PrimeCompletion
open NumberField IsDedekindDomain ClassFieldTower.Martinet.Shafarevich
open LocalFieldTheory LocalClassFieldTheory
open HilbertRamification
attribute [local instance] primeFact baseRationalAlgebra

abbrev AbsoluteDecomposition (p : Nat.Primes) :=
  finitePlaceAbsoluteDecompositionGroup ℚ (place p)
abbrev AbsoluteInertia (p : Nat.Primes) :=
  finitePlaceAbsoluteInertiaSubgroup ℚ (place p)

def absoluteEmbedding (p : Nat.Primes) :
    AlgebraicClosure ℚ →ₐ[ℚ] SeparableClosure (Base p) := by
  let v := HeightOneSpectrum.adicAbv ℚ (place p)
  let w := finitePlaceAbsoluteValueExtension ℚ (place p)
  letI hQ := AbsoluteValue.extensionCompletionAlgebra (K:=ℚ) w.1
  letI : SMul ℚ w.1.Completion := hQ.toSMul
  letI := AbsoluteValue.completionAlgebra v w.1 w.2
  exact ((finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure ℚ (place p)).toRingHom.comp
    (AbsoluteValue.toAlgebraicLocalization v w.1 w.2)).toRatAlgHom

def decompositionEquiv (p : Nat.Primes) :
    AbsoluteDecomposition p ≃ₜ* Gal(SeparableClosure (Base p)/Base p) :=
  finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup ℚ (place p)

/-- The comparison preserves the action on the actual global algebraic closure. -/
theorem decomposition_commutes (p : Nat.Primes) (σ : AbsoluteDecomposition p)
    (x : AlgebraicClosure ℚ) :
    decompositionEquiv p σ (absoluteEmbedding p x)=absoluteEmbedding p (σ.val x) := by
  let v := HeightOneSpectrum.adicAbv ℚ (place p)
  let w := finitePlaceAbsoluteValueExtension ℚ (place p)
  letI hQ := AbsoluteValue.extensionCompletionAlgebra (K:=ℚ) w.1
  letI : SMul ℚ w.1.Completion := hQ.toSMul
  letI := AbsoluteValue.completionAlgebra v w.1 w.2
  change finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
    ℚ (place p) σ _=_
  rw [finitePlaceDecompositionTransport_apply]
  change (finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure ℚ (place p))
      (decompositionGroupEquivAlgebraicLocalizationAut v (RayClass.adicAbv_isNontrivial (place p)) w σ
        ((finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure ℚ (place p)).symm
          ((finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure ℚ (place p))
            (AbsoluteValue.toAlgebraicLocalization v w.1 w.2 x))))=_
  rw [AlgEquiv.symm_apply_apply,
    localizationRamificationGroups_decompositionGroupEquiv_toLocalization]
  rfl

/-- The same comparison identifies actual inertia with local absolute inertia. -/
theorem decomposition_mem_inertia_iff (p : Nat.Primes) (σ : AbsoluteDecomposition p) :
    decompositionEquiv p σ∈(localResidueDegree (Base p)).toMonoidHom.ker ↔
      σ∈AbsoluteInertia p := by
  rw [localResidueDegree_ker_eq_valuationInertiaGroupInAut]
  exact finitePlaceDecompositionTransport_mem_inertia_iff ℚ (place p) σ

end UnitDistance.PrimeCompletion
