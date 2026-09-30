module

public import UnitDistance.SupportedIdeleCocycles
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.UnramifiedFinitePlaceIntegralBlockH2

@[expose] public section
set_option backward.privateInPublic true


/-! Vanishing of the actual finite coordinate outside the support, with no
condition on the infinite places. -/
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.Martinet.Shafarevich
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
local instance outsideRelativeIdeleAction : MulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L) :=
  RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
local instance outsideSupportedIdeleAction (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction Gal(L/K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := K) (L := L) S
local instance outsideTensorUnitsAction (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L/K) (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.adicCompletion K)
local instance outsideIntegralTensorUnitsAction (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L/K)
      (relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) v) :=
  relativeLocalTensorDecompositionIntegralUnitSubgroupAction (K := K) (L := L) v

/-- A supported idele evaluates to an integral unit outside its support. -/
def supportedIdeleIntegralRepHom (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    supportedIdeleRep K L S ⟶ Rep.ofMulDistribMulAction Gal(L/K)
      (relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) v) := by
  let f : relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S →*
      relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) v :=
    ((RelativeIdeleGroup.finiteComponent (K := K) (L := L) v).comp
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S).subtype).codRestrict _
      (fun x => Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp x.property v) hv)
  exact equivariantRepHom f (by
    intro g x
    apply Subtype.ext
    exact RelativeIdeleGroup.finiteComponent_smul (K := K) (L := L) v g x.1)

/-- Inclusion of actual local integral units into local tensor units. -/
def integralTensorInclusionRepHom (v : HeightOneSpectrum (𝓞 K)) :
    Rep.ofMulDistribMulAction Gal(L/K)
      (relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) v) ⟶
    Rep.ofMulDistribMulAction Gal(L/K) (v.adicCompletion K ⊗[K] L)ˣ :=
  equivariantRepHom
    (relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) v).subtype
    (fun _ _ => rfl)

/-- Literal finite evaluation factors through integral units outside S. -/
theorem supportedIdeleIntegralRepHom_factor (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    supportedIdeleIntegralRepHom K L S v hv ≫ integralTensorInclusionRepHom K L v =
      supportedIdeleInclusionRepHom K L S ≫ ideleFiniteRepHom K L v := by
  ext z
  rfl

/-- An unramified finite coordinate outside S vanishes on every supported
idele H² class, regardless of ramification at infinite places. -/
theorem supportedIdeleH2_finite_eq_zero_of_unramified
    (S : Finset (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S) (hunram : ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (x : groupCohomology (supportedIdeleRep K L S) 2) :
    (ideleFiniteH2 K L v).hom
      ((groupCohomology.map (MonoidHom.id Gal(L/K))
        (supportedIdeleInclusionRepHom K L S) 2).hom x) = 0 := by
  let C := groupCohomology.functor ℤ Gal(L/K) 2
  letI := unramifiedFinitePlaceIntegralBlockH2_subsingleton K L v hunram
  have hz : (C.map (supportedIdeleIntegralRepHom K L S v hv)).hom x = 0 :=
    @Subsingleton.elim _ (unramifiedFinitePlaceIntegralBlockH2_subsingleton K L v hunram) _ _
  have h := congrArg (fun f => (C.map f).hom x)
    (supportedIdeleIntegralRepHom_factor K L S v hv)
  rw [Functor.map_comp,Functor.map_comp] at h
  change (C.map (integralTensorInclusionRepHom K L v)).hom
      ((C.map (supportedIdeleIntegralRepHom K L S v hv)).hom x) = _ at h
  rw [hz,map_zero] at h
  exact h.symm

end UnitDistance.ArithmeticProP
