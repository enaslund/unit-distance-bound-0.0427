/-
Retyped from `UnitDistance/ProPStageRestriction.lean` (adapted from Naganori
Yamaguchi, SawinTotallyRealTowers, commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4,
Apache-2.0; source RealProPStageRestriction.lean): ℚ is replaced by an
arbitrary number field `F`.
-/
module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import UnitDistance.Sqrt241.ProP.MaximalProPOutside
public import UnitDistance.Sqrt241.ProP.ProPOpenNormalStage
public import UnitDistance.Sqrt241.ProP.AbsoluteProPRestriction
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerAbsoluteLift
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.QuotientRestriction
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Topologies.QuotientMaps
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Profinite.OpenSubgroups
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Absolute restriction and finite arithmetic stages over `F`

The finite quotient is continuously identified with the Galois group of its
lifted fixed field. Its restriction map agrees with restriction from the fixed
algebraic closure.
-/

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.ProP

open ClassFieldTower.Martinet.Shafarevich ClassFieldTower.Cohomology ProCGroups

/-- A homomorphism out of a finite discrete quotient, as a continuous
homomorphism out of the group. -/
def quotientToDiscreteMap
    {G H : Type} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] [Group H]
    [TopologicalSpace H]
    (U : OpenNormalSubgroup G) (f : (G ⧸ (U : Subgroup G)) →* H) : G →ₜ* H := by
  let : DiscreteTopology (G ⧸ (U : Subgroup G)) :=
    QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen
  exact
    { toMonoidHom := f.comp (QuotientGroup.mk' (U : Subgroup G))
      continuous_toFun := (show Continuous f from continuous_of_discreteTopology).comp
        (show Continuous (QuotientGroup.mk' (U : Subgroup G)) from QuotientGroup.continuous_mk) }

/-- A group isomorphism from an open quotient onto a discrete group is a
homeomorphism. -/
def quotientDiscreteEquiv
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

variable (F : Type) [Field F] [NumberField F]

/-- The finite open normal quotient and its actual arithmetic Galois group
are continuously isomorphic. -/
def proPOpenNormalQuotientContinuousEquivStage
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    (U : OpenNormalSubgroup
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T)) :
    ((maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) ⧸
      (U : Subgroup _)) ≃ₜ* ((proPOpenNormalStage F p T U).val ≃ₐ[F]
        (proPOpenNormalStage F p T U).val) :=
  quotientDiscreteEquiv U (proPOpenNormalQuotientEquivStage F p T U)

/-- Restriction to the actual finite arithmetic layer of an open normal subgroup. -/
def proPOpenNormalStageRestriction
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    (U : OpenNormalSubgroup
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T)) :
    (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) →ₜ*
      ((proPOpenNormalStage F p T U).val ≃ₐ[F]
        (proPOpenNormalStage F p T U).val) :=
  quotientToDiscreteMap U (proPOpenNormalQuotientEquivStage F p T U).toMonoidHom

/-- Restriction through the maximal field agrees with absolute restriction
on its finite arithmetic layer. -/
theorem proPOpenNormalStageRestriction_comp_absolute
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    (U : OpenNormalSubgroup
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T)) :
    (proPOpenNormalStageRestriction F p T U).comp
      (absoluteToMaximalProPOutside F p T) =
    absoluteFiniteGaloisRestriction F (proPOpenNormalStage F p T U).val := by
  apply ContinuousMonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  have h := proPOpenNormalQuotientEquivStage_apply F p T U
    (absoluteToMaximalProPOutside F p T σ) x
  have hA := absoluteToMaximalProPOutside_apply F p T σ
    ⟨(x : AlgebraicClosure F),
      le_maximalProPOutside (proPOpenNormalStage F p T U) x.property⟩
  have hR := AlgEquiv.restrictNormalHom_apply
    (proPOpenNormalStage F p T U).val.toIntermediateField
    (absoluteGaloisGroupContinuousMulEquiv F σ) x
  exact (h.trans hA).trans hR.symm

end UnitDistance.Sqrt241.ProP
