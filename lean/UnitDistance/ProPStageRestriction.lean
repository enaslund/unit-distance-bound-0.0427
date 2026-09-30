/-
Adapted from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Source: SawinTotallyRealTowers/RealProPStageRestriction.lean.
Modified: use the actual maximal extension with unrestricted infinite places; retain the restriction comparison proof.
-/
module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import UnitDistance.MaximalProPOutside
public import UnitDistance.ProPOpenNormalStage
public import UnitDistance.AbsoluteProPRestriction
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerAbsoluteLift
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.QuotientRestriction
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Topologies.QuotientMaps
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Profinite.OpenSubgroups
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Absolute restriction and finite arithmetic stages

The actual finite quotient is continuously identified with the Galois group
of its lifted fixed field. Its restriction map agrees with restriction from
the fixed algebraic closure, by the actions of both maps on every field element.
-/

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.ArithmeticProP

open ClassFieldTower.Martinet.Shafarevich ClassFieldTower.Cohomology ProCGroups

private def quotientToDiscreteMap
    {G H : Type} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] [Group H] [TopologicalSpace H]
    (U : OpenNormalSubgroup G) (f : (G ⧸ (U : Subgroup G)) →* H) : G →ₜ* H := by
  let : DiscreteTopology (G ⧸ (U : Subgroup G)) :=
    QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen
  exact
    { toMonoidHom := f.comp (QuotientGroup.mk' (U : Subgroup G))
      continuous_toFun := (show Continuous f from continuous_of_discreteTopology).comp
        (show Continuous (QuotientGroup.mk' (U : Subgroup G)) from QuotientGroup.continuous_mk) }

private def quotientDiscreteEquiv
    {G H : Type} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (U : OpenNormalSubgroup G) (e : (G ⧸ (U : Subgroup G)) ≃* H) :
    (G ⧸ (U : Subgroup G)) ≃ₜ* H := by
  let : DiscreteTopology (G ⧸ (U : Subgroup G)) :=
    QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen
  exact
    { toMulEquiv := e
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The finite open normal quotient and its actual arithmetic Galois group
are continuously isomorphic. -/
def proPOpenNormalQuotientContinuousEquivStage
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T)) :
    ((maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T) ⧸
      (U : Subgroup _)) ≃ₜ* ((proPOpenNormalStage p T U).val ≃ₐ[ℚ]
        (proPOpenNormalStage p T U).val) :=
  quotientDiscreteEquiv U (proPOpenNormalQuotientEquivStage p T U)

/-- Restriction to the actual finite arithmetic layer of an open normal subgroup. -/
def proPOpenNormalStageRestriction
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T)) :
    (maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T) →ₜ*
      ((proPOpenNormalStage p T U).val ≃ₐ[ℚ]
        (proPOpenNormalStage p T U).val) :=
  quotientToDiscreteMap U (proPOpenNormalQuotientEquivStage p T U).toMonoidHom

/-- Restriction through the actual maximal field agrees with absolute restriction
on its finite arithmetic layer. -/
theorem proPOpenNormalStageRestriction_comp_absolute
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (U : OpenNormalSubgroup
      (maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T)) :
    (proPOpenNormalStageRestriction p T U).comp
      (absoluteToMaximalProPOutside p T) =
    absoluteFiniteGaloisRestriction ℚ (proPOpenNormalStage p T U).val := by
  apply ContinuousMonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  have h := proPOpenNormalQuotientEquivStage_apply p T U
    (absoluteToMaximalProPOutside p T σ) x
  have hA := absoluteToMaximalProPOutside_apply p T σ
    ⟨(x : AlgebraicClosure ℚ),
      le_maximalProPOutside (proPOpenNormalStage p T U) x.property⟩
  have hR := AlgEquiv.restrictNormalHom_apply
    (proPOpenNormalStage p T U).val.toIntermediateField
    (absoluteGaloisGroupContinuousMulEquiv ℚ σ) x
  exact (h.trans hA).trans hR.symm

end UnitDistance.ArithmeticProP
