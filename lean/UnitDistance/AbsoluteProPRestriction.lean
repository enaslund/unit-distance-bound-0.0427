/-
Adapted from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Source: SawinTotallyRealTowers/AbsoluteRealProPRestriction.lean.
Modified: restriction to the actual maximal pro-p extension with unrestricted
infinite places. The Galois/topological proofs are retained.
-/
module

public import UnitDistance.MaximalProPOutside
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Topologies.ContinuousMulEquiv
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Absolute restriction to the maximal pro-p compositum

The actual ambient inclusion supplies a continuous surjective restriction
homomorphism. Its kernel is exactly the subgroup fixing the constructed
compositum. The quotient by this kernel is continuously isomorphic to the
relative Galois group, providing the concrete quotient for later factorization.
No primality or ramification comparison is needed for this Galois boundary.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.ArithmeticProP

private def normalAbsoluteRestriction (F : Type) [Field F]
    (M : IntermediateField F (AlgebraicClosure F)) (hM : Normal F M) :
    Field.absoluteGaloisGroup F →ₜ* (M ≃ₐ[F] M) := by
  let : Normal F M := hM
  exact
    { toMonoidHom := AlgEquiv.restrictNormalHom M
      continuous_toFun := InfiniteGalois.restrictNormalHom_continuous M }

private theorem normalAbsoluteRestriction_surjective (F : Type) [Field F]
    (M : IntermediateField F (AlgebraicClosure F)) (hM : Normal F M) :
    Function.Surjective (normalAbsoluteRestriction F M hM) := by
  let : Normal F M := hM
  exact AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure F)

private theorem normalAbsoluteRestriction_apply (F : Type) [Field F]
    (M : IntermediateField F (AlgebraicClosure F)) (hM : Normal F M)
    (σ : Field.absoluteGaloisGroup F) (x : M) :
    (normalAbsoluteRestriction F M hM σ x : AlgebraicClosure F) =
      (AlgEquiv.toAlgHom (R := F) (A₁ := AlgebraicClosure F)
        (A₂ := AlgebraicClosure F) σ) (x : AlgebraicClosure F) := by
  let : Normal F M := hM
  exact AlgEquiv.restrictNormalHom_apply M σ x

private theorem normalAbsoluteRestriction_ker (F : Type) [Field F]
    (M : IntermediateField F (AlgebraicClosure F)) (hM : Normal F M) :
    (normalAbsoluteRestriction F M hM).toMonoidHom.ker = M.fixingSubgroup := by
  let : Normal F M := hM
  exact IntermediateField.restrictNormalHom_ker M

/-- Restriction of absolute automorphisms to the constructed maximal
compositum with the given finite ramification support. -/
def absoluteToMaximalProPOutside (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    Field.absoluteGaloisGroup ℚ →ₜ*
      (maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T) :=
  normalAbsoluteRestriction ℚ (maximalProPOutside p T)
    (maximalProPOutside_isGalois p T).to_normal

/-- Every automorphism of the maximal compositum extends to the fixed
algebraic closure. -/
theorem absoluteToMaximalProPOutside_surjective (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    Function.Surjective (absoluteToMaximalProPOutside p T) :=
  normalAbsoluteRestriction_surjective ℚ (maximalProPOutside p T)
    (maximalProPOutside_isGalois p T).to_normal

/-- The restriction acts by the original absolute automorphism on each
element of the constructed intermediate field. -/
theorem absoluteToMaximalProPOutside_apply (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (σ : Field.absoluteGaloisGroup ℚ) (x : maximalProPOutside p T) :
    (absoluteToMaximalProPOutside p T σ x : AlgebraicClosure ℚ) =
      (AlgEquiv.toAlgHom (R := ℚ) (A₁ := AlgebraicClosure ℚ)
        (A₂ := AlgebraicClosure ℚ) σ) (x : AlgebraicClosure ℚ) :=
  normalAbsoluteRestriction_apply ℚ (maximalProPOutside p T)
    (maximalProPOutside_isGalois p T).to_normal σ x

/-- The actual restriction kernel is the fixing subgroup of the actual
maximal compositum. No separate kernel structure is introduced. -/
theorem absoluteToMaximalProPOutside_ker (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    (absoluteToMaximalProPOutside p T).toMonoidHom.ker =
      (maximalProPOutside p T).fixingSubgroup :=
  normalAbsoluteRestriction_ker ℚ (maximalProPOutside p T)
    (maximalProPOutside_isGalois p T).to_normal

/-- The quotient by the actual restriction kernel is the relative Galois
group as a topological group. -/
def absoluteProPOutsideQuotientEquiv (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    (Field.absoluteGaloisGroup ℚ ⧸
      (absoluteToMaximalProPOutside p T).toMonoidHom.ker) ≃ₜ*
      (maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T) := by
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let : IsGalois ℚ (maximalProPOutside p T) := maximalProPOutside_isGalois p T
  let : CompactSpace (Field.absoluteGaloisGroup ℚ) :=
    inferInstanceAs
      (CompactSpace (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  let f := absoluteToMaximalProPOutside p T
  let e := QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom
    (absoluteToMaximalProPOutside_surjective p T)
  have hContinuous : Continuous e.toMonoidHom := by
    apply (QuotientGroup.isQuotientMap_mk f.toMonoidHom.ker).continuous_iff.mpr
    exact f.continuous_toFun
  have hBijective : Function.Bijective e.toMonoidHom := e.bijective
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    e.toMonoidHom hContinuous hBijective

/-- The quotient equivalence sends the class of an absolute automorphism
to its restriction. -/
theorem absoluteProPOutsideQuotientEquiv_mk (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) (σ : Field.absoluteGaloisGroup ℚ) :
    absoluteProPOutsideQuotientEquiv p T
      (QuotientGroup.mk' (absoluteToMaximalProPOutside p T).toMonoidHom.ker σ) =
        absoluteToMaximalProPOutside p T σ := by
  change QuotientGroup.kerLift (absoluteToMaximalProPOutside p T).toMonoidHom
      (QuotientGroup.mk' (absoluteToMaximalProPOutside p T).toMonoidHom.ker σ) =
    absoluteToMaximalProPOutside p T σ
  exact QuotientGroup.kerLift_mk (absoluteToMaximalProPOutside p T).toMonoidHom σ

end UnitDistance.ArithmeticProP
