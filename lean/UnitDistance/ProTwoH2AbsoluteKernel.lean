/-
Adapted from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Source: SawinTotallyRealTowers/RealProTwoH2AbsoluteKernel.lean.
Modified: finite-inertia correction and actual unrestricted maximal pro-two factorization replace all real-place conditions.
-/
module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.FiniteKummerContinuousKernel
import all UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteUnramifiedGaloisSequence
public import UnitDistance.ProPOpenNormalStage
public import UnitDistance.ProPStageRestriction
public import UnitDistance.CentralLiftCorrection
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
public import UnitDistance.AbsoluteProPFactor
public import UnitDistance.AbsoluteProPRestriction
public import UnitDistance.AbsoluteProPUnramified
public import UnitDistance.MaximalProPOutside
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2CocycleExtension
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2CocycleExtensionLinearLifts
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2CocycleExtensionPullback
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2CentralExtensionClass
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.TrivialZModP
public import Mathlib.GroupTheory.PGroup
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Descending absolute degree-two vanishing to the actual maximal pro-two group

An actual absolute cocycle lift is corrected at its finite ramification
support. Its kernel field is an admissible finite
two-extension, so the corrected lift factors through the constructed
maximal pro-two compositum. Thus vanishing after absolute inflation
already implies vanishing after inflation into this maximal group.
-/

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.ArithmeticProP

open ClassFieldTower.Sawin ClassFieldTower.Cohomology ClassFieldTower.ProP
open ClassFieldTower.Sawin ClassFieldTower.Martinet.Shafarevich

/-- Every absolute solution of a finite two-group cocycle embedding problem
comes from an actual solution on the maximal pro-two group. -/
theorem exists_maximalProTwo_cocycle_lift_of_absolute_lift
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hThree : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ T)
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (hQ : IsPGroup 2 Q)
    (q : (maximalProPOutside 2 T ≃ₐ[ℚ] maximalProPOutside 2 T) →ₜ* Q)
    (z : trivialZModPCocyclesLifted 2 Q 2)
    (s : Field.absoluteGaloisGroup ℚ →ₜ* H2CocycleExtension z)
    (hs : (H2CocycleExtension.projection z).comp s =
      q.comp (absoluteToMaximalProPOutside 2 T)) :
    ∃ t : (maximalProPOutside 2 T ≃ₐ[ℚ] maximalProPOutside 2 T) →ₜ*
        H2CocycleExtension z,
      (H2CocycleExtension.projection z).comp t = q := by
  obtain ⟨γ, hInertia⟩ := exists_inertia_corrected_absolute_cocycle_lift
    T hThree (q.comp (absoluteToMaximalProPOutside 2 T)) z s hs
    (by
      intro v hv σ
      change q (absoluteToMaximalProPOutside 2 T
        (finitePlaceAbsoluteDecompositionInclusion ℚ v σ.1)) = 1
      rw [absoluteToMaximalProPOutside_inertia 2 T v hv σ, map_one])
  obtain ⟨t, ht⟩ :=
    exists_maximalProPOutside_factor_of_inertia_trivial
      2 T (H2CocycleExtension.isPGroup z hQ)
      (H2CocycleExtension.twistByCharacter z s γ) hInertia
  refine ⟨t, ?_⟩
  ext g
  obtain ⟨σ, rfl⟩ := absoluteToMaximalProPOutside_surjective 2 T g
  have htσ := DFunLike.congr_fun ht σ
  have hp := DFunLike.congr_fun
    ((H2CocycleExtension.twistByCharacter_projection z s γ).trans hs) σ
  exact (congrArg (H2CocycleExtension.projection z) htσ).trans hp

/-- At every actual finite two-group stage, the kernel of absolute inflation
is contained in the kernel of inflation to the maximal pro-two group. -/
theorem maximalProTwo_H2_eq_zero_of_absolute_inflation_eq_zero
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hThree : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ T)
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (hQ : IsPGroup 2 Q)
    (q : (maximalProPOutside 2 T ≃ₐ[ℚ] maximalProPOutside 2 T) →ₜ* Q)
    (x : continuousCohomologyZModPLifted 2 Q 2)
    (hx : (continuousCohomologyZModPMapLifted 2
      (q.comp (absoluteToMaximalProPOutside 2 T)) 2).hom x = 0) :
    (continuousCohomologyZModPMapLifted 2 q 2).hom x = 0 := by
  let : IsGalois ℚ (maximalProPOutside 2 T) :=
    maximalProPOutside_isGalois 2 T
  let z := degreeTwoCocycleRepresentative x
  obtain ⟨s, hs⟩ := H2CocycleExtension.exists_lift_of_restriction_eq_zero
    (q.comp (absoluteToMaximalProPOutside 2 T)) z
    (by simpa only [z, degreeTwoCocycleRepresentative_π] using hx)
  obtain ⟨t, ht⟩ :=
    exists_maximalProTwo_cocycle_lift_of_absolute_lift T hThree hQ q z s hs
  have h := H2CocycleExtension.restriction_eq_zero_of_lift q z t ht
  simpa only [z, degreeTwoCocycleRepresentative_π] using h

set_option maxHeartbeats 1000000 in
/-- The finite Kummer kernel dies under actual inflation from every constructed
arithmetic stage to the maximal pro-two group. -/
theorem finiteKummerContinuousH2Map_ker_le_proPStageInflation_ker
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hThree : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ T)
    (U : OpenNormalSubgroup
      (maximalProPOutside 2 T ≃ₐ[ℚ] maximalProPOutside 2 T))
    (hmu : (primitiveRoots 2 ℚ).Nonempty) :
    (finiteKummerContinuousH2Map ℚ (2 : ℕ+) (proPOpenNormalStage 2 T U).val hmu).ker ≤
      (continuousCohomologyZModPMapLifted 2
        (proPOpenNormalStageRestriction 2 T U) 2).hom.toLinearMap.toAddMonoidHom.ker := by
  intro x hx
  apply maximalProTwo_H2_eq_zero_of_absolute_inflation_eq_zero T hThree
    (proPOpenNormalStage 2 T U).property.1
    (proPOpenNormalStageRestriction 2 T U) x
  rw [proPOpenNormalStageRestriction_comp_absolute]
  exact finiteKummerContinuousH2Map_ker_le_absoluteInflation_ker ℚ (2 : ℕ+)
    (proPOpenNormalStage 2 T U).val hmu hx

end UnitDistance.ArithmeticProP
