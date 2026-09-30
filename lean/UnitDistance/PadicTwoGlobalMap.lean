module

public import UnitDistance.PadicTwoMaximalProTwo
public import UnitDistance.RationalLocalAbsoluteEmbedding
public import UnitDistance.AbsoluteProPRestriction
public import UnitDistance.MaximalProTwoSigma
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence

@[expose] public section
set_option backward.privateInPublic true


/-! The actual maximal local pro-two Galois group maps continuously into the
actual global group unramified outside Sigma. The map is induced by the
chosen decomposition embedding and the residual-core universal property. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace UnitDistance.PadicTwoGlobalMap
open ProCGroups ProCGroups.ProC ArithmeticProP
open PadicTwoMaximalProTwo
open scoped NumberField
attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

abbrev prime : Nat.Primes := ⟨2,Nat.prime_two⟩
abbrev Base := PrimeCompletion.Base prime
abbrev LocalClosure := SeparableClosure Base
abbrev GlobalGroup := Gal(maximalSigmaProTwo/ℚ)

instance localCharZero : CharZero LocalClosure := inferInstance

def closureEquiv : Closure ≃+* LocalClosure :=
  IsAlgClosure.equivOfEquiv Closure LocalClosure (PrimeCompletion.equiv prime).toRingEquiv.symm

theorem closureEquiv_commutes (x : ℚ_[2]) :
    closureEquiv (algebraMap ℚ_[2] Closure x)=
      algebraMap Base LocalClosure ((PrimeCompletion.equiv prime).symm x) :=
  congrArg (fun f : ℚ_[2] →+* LocalClosure => f x)
    (IsAlgClosure.equivOfEquiv_comp_algebraMap Closure LocalClosure
      (PrimeCompletion.equiv prime).toRingEquiv.symm)

def absoluteMonoidHom : AbsoluteGroup →* Gal(LocalClosure/Base) :=
    { toFun := fun σ =>
        { (closureEquiv.symm.trans (σ.toRingEquiv.trans closureEquiv)) with
          commutes' := by
            intro x
            have hx : closureEquiv.symm (algebraMap Base LocalClosure x)=
                algebraMap ℚ_[2] Closure (PrimeCompletion.equiv prime x) := by
              apply closureEquiv.injective
              rw [closureEquiv.apply_symm_apply,closureEquiv_commutes]
              rw [(PrimeCompletion.equiv prime).symm_apply_apply]
            change closureEquiv (σ (closureEquiv.symm (algebraMap Base LocalClosure x)))=_
            rw [hx,σ.commutes,closureEquiv_commutes,(PrimeCompletion.equiv prime).symm_apply_apply] }
      map_one' := by ext x; simp
      map_mul' := by intro σ τ; ext x; simp }

def absoluteHom : AbsoluteGroup →ₜ* Gal(LocalClosure/Base) :=
  ⟨absoluteMonoidHom,
    RamificationTheory.Field.absoluteGaloisGroup.semilinear_conjugation_continuous
      (PrimeCompletion.equiv prime).toRingEquiv.symm closureEquiv closureEquiv_commutes
      absoluteMonoidHom (fun _ => rfl)⟩

/-- The actual decomposition automorphism associated with a local automorphism. -/
def decomposition (σ : AbsoluteGroup) : PrimeCompletion.AbsoluteDecomposition prime :=
  (PrimeCompletion.decompositionEquiv prime).symm (absoluteHom σ)

def toAbsoluteGlobal : AbsoluteGroup →ₜ* Field.absoluteGaloisGroup ℚ :=
  (⟨(PrimeCompletion.AbsoluteDecomposition prime).subtype,continuous_subtype_val⟩ :
    PrimeCompletion.AbsoluteDecomposition prime →ₜ* Field.absoluteGaloisGroup ℚ).comp
      ((⟨(PrimeCompletion.decompositionEquiv prime).symm.toMulEquiv.toMonoidHom,
        (PrimeCompletion.decompositionEquiv prime).symm.continuous⟩ :
          Gal(LocalClosure/Base) →ₜ* PrimeCompletion.AbsoluteDecomposition prime).comp absoluteHom)

def absoluteMap : AbsoluteGroup →ₜ* GlobalGroup :=
  (absoluteToMaximalProPOutside 2 sigmaPrimeSupport).comp toAbsoluteGlobal

/-- The residual pro-two core is killed because the actual global target is pro-two. -/
def toGlobal : PadicTwoMaximalProTwo.Group →ₜ* GlobalGroup :=
  lift_proCResidualCoreQuotient (FiniteGroupClass.pGroup_hereditary 2) absoluteMap
    maximalSigmaProTwo_hasPGroupOpenNormalBasis

@[simp] theorem toGlobal_projection (σ : AbsoluteGroup) :
    toGlobal (projection σ)=absoluteMap σ := rfl

/-- The concrete embedding into the chosen algebraic closure of Q₂. -/
def globalEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] Closure :=
  closureEquiv.symm.toRingHom.toRatAlgHom.comp (PrimeCompletion.absoluteEmbedding prime)

theorem decomposition_commutes (σ : AbsoluteGroup) (x : AlgebraicClosure ℚ) :
    σ (globalEmbedding x)=globalEmbedding ((decomposition σ).val x) := by
  apply closureEquiv.injective
  change closureEquiv (σ (closureEquiv.symm (PrimeCompletion.absoluteEmbedding prime x)))=
    closureEquiv (closureEquiv.symm (PrimeCompletion.absoluteEmbedding prime ((decomposition σ).val x)))
  rw [closureEquiv.apply_symm_apply]
  have h := PrimeCompletion.decomposition_commutes prime (decomposition σ) x
  rw [show PrimeCompletion.decompositionEquiv prime (decomposition σ)=absoluteHom σ from
    (PrimeCompletion.decompositionEquiv prime).apply_symm_apply _] at h
  exact h

theorem absoluteMap_commutes (σ : AbsoluteGroup) (x : maximalSigmaProTwo) :
    globalEmbedding ((absoluteMap σ x : maximalSigmaProTwo) : AlgebraicClosure ℚ)=
      σ (globalEmbedding (x : AlgebraicClosure ℚ)) := by
  change globalEmbedding ((absoluteToMaximalProPOutside 2 sigmaPrimeSupport (toAbsoluteGlobal σ) x :
    maximalProPOutside 2 sigmaPrimeSupport) : AlgebraicClosure ℚ)=_
  rw [absoluteToMaximalProPOutside_apply]
  exact (decomposition_commutes σ x).symm

end UnitDistance.PadicTwoGlobalMap
