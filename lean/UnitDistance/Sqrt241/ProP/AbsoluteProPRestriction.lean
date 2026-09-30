/-
Retyped from `UnitDistance/AbsoluteProPRestriction.lean` (adapted from Naganori
Yamaguchi, SawinTotallyRealTowers, commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4,
Apache-2.0; source AbsoluteRealProPRestriction.lean): ℚ is replaced by an
arbitrary number field `F`, and the private `normalAbsoluteRestriction` is
exposed as `absoluteToNormal`.
-/
module

public import UnitDistance.Sqrt241.ProP.MaximalProPOutside
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
# Absolute restriction to the maximal pro-p compositum over `F`

The ambient inclusion supplies a continuous surjective restriction
homomorphism from `Field.absoluteGaloisGroup F` onto the Galois group of any
normal intermediate field (`absoluteToNormal`), in particular onto the Galois
group of the maximal compositum. Its kernel is the fixing subgroup, and the
quotient by the kernel is continuously isomorphic to the relative Galois group.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.ProP

/-- Continuous restriction from the absolute Galois group of `F` to a normal
intermediate field of `AlgebraicClosure F`. -/
def absoluteToNormal (F : Type) [Field F]
    (M : IntermediateField F (AlgebraicClosure F)) (hM : Normal F M) :
    Field.absoluteGaloisGroup F →ₜ* (M ≃ₐ[F] M) := by
  let : Normal F M := hM
  exact
    { toMonoidHom := AlgEquiv.restrictNormalHom M
      continuous_toFun := InfiniteGalois.restrictNormalHom_continuous M }

theorem absoluteToNormal_surjective (F : Type) [Field F]
    (M : IntermediateField F (AlgebraicClosure F)) (hM : Normal F M) :
    Function.Surjective (absoluteToNormal F M hM) := by
  let : Normal F M := hM
  exact AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure F)

theorem absoluteToNormal_apply (F : Type) [Field F]
    (M : IntermediateField F (AlgebraicClosure F)) (hM : Normal F M)
    (σ : Field.absoluteGaloisGroup F) (x : M) :
    (absoluteToNormal F M hM σ x : AlgebraicClosure F) =
      (AlgEquiv.toAlgHom (R := F) (A₁ := AlgebraicClosure F)
        (A₂ := AlgebraicClosure F) σ) (x : AlgebraicClosure F) := by
  let : Normal F M := hM
  exact AlgEquiv.restrictNormalHom_apply M σ x

theorem absoluteToNormal_ker (F : Type) [Field F]
    (M : IntermediateField F (AlgebraicClosure F)) (hM : Normal F M) :
    (absoluteToNormal F M hM).toMonoidHom.ker = M.fixingSubgroup := by
  let : Normal F M := hM
  exact IntermediateField.restrictNormalHom_ker M

variable (F : Type) [Field F] [NumberField F]

/-- Restriction of absolute automorphisms to the constructed maximal
compositum with the given finite ramification support. -/
def absoluteToMaximalProPOutside (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) :
    Field.absoluteGaloisGroup F →ₜ*
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) :=
  absoluteToNormal F (maximalProPOutside F p T)
    (maximalProPOutside_isGalois F p T).to_normal

/-- Every automorphism of the maximal compositum extends to the fixed
algebraic closure. -/
theorem absoluteToMaximalProPOutside_surjective (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) :
    Function.Surjective (absoluteToMaximalProPOutside F p T) :=
  absoluteToNormal_surjective F (maximalProPOutside F p T)
    (maximalProPOutside_isGalois F p T).to_normal

/-- The restriction acts by the original absolute automorphism on each
element of the constructed intermediate field. -/
theorem absoluteToMaximalProPOutside_apply (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F)))
    (σ : Field.absoluteGaloisGroup F) (x : maximalProPOutside F p T) :
    (absoluteToMaximalProPOutside F p T σ x : AlgebraicClosure F) =
      (AlgEquiv.toAlgHom (R := F) (A₁ := AlgebraicClosure F)
        (A₂ := AlgebraicClosure F) σ) (x : AlgebraicClosure F) :=
  absoluteToNormal_apply F (maximalProPOutside F p T)
    (maximalProPOutside_isGalois F p T).to_normal σ x

/-- The restriction kernel is the fixing subgroup of the maximal compositum. -/
theorem absoluteToMaximalProPOutside_ker (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) :
    (absoluteToMaximalProPOutside F p T).toMonoidHom.ker =
      (maximalProPOutside F p T).fixingSubgroup :=
  absoluteToNormal_ker F (maximalProPOutside F p T)
    (maximalProPOutside_isGalois F p T).to_normal

/-- The quotient by the restriction kernel is the relative Galois
group as a topological group. -/
def absoluteProPOutsideQuotientEquiv (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) :
    (Field.absoluteGaloisGroup F ⧸
      (absoluteToMaximalProPOutside F p T).toMonoidHom.ker) ≃ₜ*
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) := by
  let : Algebra.IsAlgebraic F (AlgebraicClosure F) := AlgebraicClosure.isAlgebraic F
  let : IsGalois F (maximalProPOutside F p T) := maximalProPOutside_isGalois F p T
  let : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs
      (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  let f := absoluteToMaximalProPOutside F p T
  let e := QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom
    (absoluteToMaximalProPOutside_surjective F p T)
  have hContinuous : Continuous e.toMonoidHom := by
    apply (QuotientGroup.isQuotientMap_mk f.toMonoidHom.ker).continuous_iff.mpr
    exact f.continuous_toFun
  have hBijective : Function.Bijective e.toMonoidHom := e.bijective
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    e.toMonoidHom hContinuous hBijective

/-- The quotient equivalence sends the class of an absolute automorphism
to its restriction. -/
theorem absoluteProPOutsideQuotientEquiv_mk (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) (σ : Field.absoluteGaloisGroup F) :
    absoluteProPOutsideQuotientEquiv F p T
      (QuotientGroup.mk' (absoluteToMaximalProPOutside F p T).toMonoidHom.ker σ) =
        absoluteToMaximalProPOutside F p T σ := by
  change QuotientGroup.kerLift (absoluteToMaximalProPOutside F p T).toMonoidHom
      (QuotientGroup.mk' (absoluteToMaximalProPOutside F p T).toMonoidHom.ker σ) =
    absoluteToMaximalProPOutside F p T σ
  exact QuotientGroup.kerLift_mk (absoluteToMaximalProPOutside F p T).toMonoidHom σ

end UnitDistance.Sqrt241.ProP
