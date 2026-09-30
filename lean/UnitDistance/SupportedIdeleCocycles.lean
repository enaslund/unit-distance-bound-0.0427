module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.SPlaces
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public section
set_option backward.privateInPublic true


/-! Finite-support representatives for actual relative-idele two-cocycles.
This is new glue over the attributed Yamaguchi relative-idele definitions. -/
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct
namespace UnitDistance.ArithmeticProP
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local instance : MulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L) :=
  RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
local instance (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction Gal(L/K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := K) (L := L) S

abbrev supportedIdeleRep (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  Rep.ofMulDistribMulAction Gal(L/K)
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)

/-- The literal subgroup inclusion as an equivariant coefficient map. -/
def supportedIdeleInclusionRepHom (S : Finset (HeightOneSpectrum (𝓞 K))) :
    supportedIdeleRep K L S ⟶ Rep.ofMulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L) :=
  equivariantRepHom
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S).subtype
    (fun _ _ => rfl)

/-- Any idele two-cocycle has a finite-support lift, with any prescribed
finite exceptional set included in its support. -/
theorem exists_supportedIdele_cocycle
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (c : groupCohomology.cocycles₂
      (Rep.ofMulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      ∃ cS : groupCohomology.cocycles₂ (supportedIdeleRep K L S),
        groupCohomology.mapCocycles₂ (MonoidHom.id Gal(L/K))
          (supportedIdeleInclusionRepHom K L S) cS = c := by
  classical
  let S := S₀ ∪ Finset.univ.biUnion (fun gh : Gal(L/K) × Gal(L/K) =>
    relativeIdeleLocalTensorDecompositionSupport (K := K) (L := L) (c gh).toMul)
  have hmem (gh : Gal(L/K) × Gal(L/K)) : (c gh).toMul ∈
      relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S := by
    apply relativeIdeleLocalTensorDecompositionSupportedSubgroup_mono
      (K := K) (L := L) (S := relativeIdeleLocalTensorDecompositionSupport
        (K := K) (L := L) (c gh).toMul) (T := S)
    · intro v hv
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨gh, Finset.mem_univ _, hv⟩)
    · exact relativeIdele_mem_localTensorDecompositionSupportedSubgroup
        (K := K) (L := L) (c gh).toMul
  let cS : groupCohomology.cocycles₂ (supportedIdeleRep K L S) :=
    ⟨fun gh => Additive.ofMul ⟨(c gh).toMul, hmem gh⟩, by
      apply (groupCohomology.mem_cocycles₂_iff
        (A := supportedIdeleRep K L S) _).mpr
      intro g h j
      apply Additive.toMul.injective
      apply Subtype.ext
      exact congrArg Additive.toMul
        ((groupCohomology.mem_cocycles₂_iff c).mp c.property g h j)⟩
  refine ⟨S, Finset.subset_union_left, cS, ?_⟩
  apply groupCohomology.cocycles₂_ext
  intro g h
  rfl

/-- Every idele H² class lifts to some finite-support subgroup, while
retaining any initially prescribed exceptional primes. -/
theorem exists_supportedIdele_H2
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (x : groupCohomology
      (Rep.ofMulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L)) 2) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      ∃ xS : groupCohomology (supportedIdeleRep K L S) 2,
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          (supportedIdeleInclusionRepHom K L S) 2).hom xS = x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    obtain ⟨S, hS, cS, hcS⟩ := exists_supportedIdele_cocycle K L S₀ c
    refine ⟨S, hS, groupCohomology.H2π _ cS, ?_⟩
    rw [groupCohomology.H2π_comp_map_apply, hcS]

local instance (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L/K) (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.adicCompletion K)

/-- Actual evaluation of a relative idele at a finite tensor block. -/
def ideleFiniteRepHom (v : HeightOneSpectrum (𝓞 K)) :
    Rep.ofMulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L) ⟶
      Rep.ofMulDistribMulAction Gal(L/K) (v.adicCompletion K ⊗[K] L)ˣ :=
  equivariantRepHom (RelativeIdeleGroup.finiteComponent (K := K) (L := L) v)
    (fun g z => RelativeIdeleGroup.finiteComponent_smul (K := K) (L := L) v g z)

/-- Actual finite tensor evaluation on idele cohomology. -/
def ideleFiniteH2 (v : HeightOneSpectrum (𝓞 K)) :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L)) 2 ⟶
      groupCohomology
        (Rep.ofMulDistribMulAction Gal(L/K) (v.adicCompletion K ⊗[K] L)ˣ) 2 :=
  groupCohomology.map (MonoidHom.id Gal(L/K)) (ideleFiniteRepHom K L v) 2

end UnitDistance.ArithmeticProP
