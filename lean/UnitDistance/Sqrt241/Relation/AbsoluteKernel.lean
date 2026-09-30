/-
Retyped from `UnitDistance/ProTwoH2AbsoluteKernel.lean` (adapted from Naganori
Yamaguchi, SawinTotallyRealTowers, commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4,
Apache-2.0; source RealProTwoH2AbsoluteKernel.lean): the base ℚ is replaced by
an arbitrary number field `F`, the maximal pro-two extension by the generic
`UnitDistance.Sqrt241.ProP.maximalProPOutside F 2 T`, and the ℚ-only input
(prime three in `T`) by `PrescribedQuadraticInertia F T`.
-/
module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.FiniteKummerContinuousKernel
import all UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteUnramifiedGaloisSequence
public import UnitDistance.Sqrt241.ProP.ProPOpenNormalStage
public import UnitDistance.Sqrt241.ProP.ProPStageRestriction
public import UnitDistance.Sqrt241.Relation.LiftCorrection
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
public import UnitDistance.Sqrt241.ProP.AbsoluteProPFactor
public import UnitDistance.Sqrt241.ProP.AbsoluteProPRestriction
public import UnitDistance.Sqrt241.ProP.AbsoluteProPUnramified
public import UnitDistance.Sqrt241.ProP.MaximalProPOutside
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2CocycleExtension
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2CocycleExtensionLinearLifts
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2CocycleExtensionPullback
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2CentralExtensionClass
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.TrivialZModP
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Descending absolute degree-two vanishing to the maximal pro-two group over `F`

An absolute cocycle lift is corrected at its finite ramification support by a
global quadratic character (`PrescribedQuadraticInertia F T`). Its kernel field
is an admissible finite two-extension, so the corrected lift factors through
the maximal pro-two compositum. Thus vanishing after absolute inflation
implies vanishing after inflation into this maximal group.
-/

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.Relation

open ClassFieldTower.Sawin ClassFieldTower.Cohomology ClassFieldTower.ProP
open ClassFieldTower.Martinet.Shafarevich
open UnitDistance.Sqrt241.ProP

variable (F : Type) [Field F] [NumberField F]

/-- Every absolute solution of a finite two-group cocycle embedding problem
comes from a solution on the maximal pro-two group. -/
theorem exists_maximalProTwo_cocycle_lift_of_absolute_lift
    (T : Set (HeightOneSpectrum (𝓞 F)))
    (hchar : PrescribedQuadraticInertia F T)
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (hQ : IsPGroup 2 Q)
    (q : (maximalProPOutside F 2 T ≃ₐ[F] maximalProPOutside F 2 T) →ₜ* Q)
    (z : trivialZModPCocyclesLifted 2 Q 2)
    (s : Field.absoluteGaloisGroup F →ₜ* H2CocycleExtension z)
    (hs : (H2CocycleExtension.projection z).comp s =
      q.comp (absoluteToMaximalProPOutside F 2 T)) :
    ∃ t : (maximalProPOutside F 2 T ≃ₐ[F] maximalProPOutside F 2 T) →ₜ*
        H2CocycleExtension z,
      (H2CocycleExtension.projection z).comp t = q := by
  obtain ⟨γ, hInertia⟩ := exists_inertia_corrected_absolute_cocycle_lift
    F T hchar (q.comp (absoluteToMaximalProPOutside F 2 T)) z s hs
    (by
      intro v hv σ
      change q (absoluteToMaximalProPOutside F 2 T
        (finitePlaceAbsoluteDecompositionInclusion F v σ.1)) = 1
      rw [absoluteToMaximalProPOutside_inertia F 2 T v hv σ, map_one])
  obtain ⟨t, ht⟩ :=
    exists_maximalProPOutside_factor_of_inertia_trivial
      F 2 T (H2CocycleExtension.isPGroup z hQ)
      (H2CocycleExtension.twistByCharacter z s γ) hInertia
  refine ⟨t, ?_⟩
  ext g
  obtain ⟨σ, rfl⟩ := absoluteToMaximalProPOutside_surjective F 2 T g
  have htσ := DFunLike.congr_fun ht σ
  have hp := DFunLike.congr_fun
    ((H2CocycleExtension.twistByCharacter_projection z s γ).trans hs) σ
  exact (congrArg (H2CocycleExtension.projection z) htσ).trans hp

/-- At every finite two-group stage, the kernel of absolute inflation
is contained in the kernel of inflation to the maximal pro-two group. -/
theorem maximalProTwo_H2_eq_zero_of_absolute_inflation_eq_zero
    (T : Set (HeightOneSpectrum (𝓞 F)))
    (hchar : PrescribedQuadraticInertia F T)
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (hQ : IsPGroup 2 Q)
    (q : (maximalProPOutside F 2 T ≃ₐ[F] maximalProPOutside F 2 T) →ₜ* Q)
    (x : continuousCohomologyZModPLifted 2 Q 2)
    (hx : (continuousCohomologyZModPMapLifted 2
      (q.comp (absoluteToMaximalProPOutside F 2 T)) 2).hom x = 0) :
    (continuousCohomologyZModPMapLifted 2 q 2).hom x = 0 := by
  let z := degreeTwoCocycleRepresentative x
  obtain ⟨s, hs⟩ := H2CocycleExtension.exists_lift_of_restriction_eq_zero
    (q.comp (absoluteToMaximalProPOutside F 2 T)) z
    (by simpa only [z, degreeTwoCocycleRepresentative_π] using hx)
  obtain ⟨t, ht⟩ :=
    exists_maximalProTwo_cocycle_lift_of_absolute_lift F T hchar hQ q z s hs
  have h := H2CocycleExtension.restriction_eq_zero_of_lift q z t ht
  simpa only [z, degreeTwoCocycleRepresentative_π] using h

set_option maxHeartbeats 1000000 in
/-- The finite Kummer kernel dies under inflation from every constructed
arithmetic stage to the maximal pro-two group. -/
theorem finiteKummerContinuousH2Map_ker_le_proPStageInflation_ker
    (T : Set (HeightOneSpectrum (𝓞 F)))
    (hchar : PrescribedQuadraticInertia F T)
    (U : OpenNormalSubgroup
      (maximalProPOutside F 2 T ≃ₐ[F] maximalProPOutside F 2 T))
    (hmu : (primitiveRoots 2 F).Nonempty) :
    (finiteKummerContinuousH2Map F (2 : ℕ+) (proPOpenNormalStage F 2 T U).val hmu).ker ≤
      (continuousCohomologyZModPMapLifted 2
        (proPOpenNormalStageRestriction F 2 T U) 2).hom.toLinearMap.toAddMonoidHom.ker := by
  intro x hx
  apply maximalProTwo_H2_eq_zero_of_absolute_inflation_eq_zero F T hchar
    (proPOpenNormalStage F 2 T U).property.1
    (proPOpenNormalStageRestriction F 2 T U) x
  rw [proPOpenNormalStageRestriction_comp_absolute]
  exact finiteKummerContinuousH2Map_ker_le_absoluteInflation_ker F (2 : ℕ+)
    (proPOpenNormalStage F 2 T U).val hmu hx

end UnitDistance.Sqrt241.Relation
