/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Compatibility names for the absolute abelianization

The field-generic construction is owned by
`AlgebraicNumberTheory.Galois.AbsoluteAbelianization`.  This module preserves
the established local names as definitional wrappers for downstream users.
-/

noncomputable section

namespace LocalClassFieldTheory

variable (K : Type) [Field K]

/-- Compatibility name for the absolute commutator closure. -/
abbrev localAbsoluteCommutatorClosure :
    ClosedSubgroup (intrinsicAbsoluteGalois K) :=
  absoluteCommutatorClosure K

/-- Compatibility instance for normality of the absolute commutator closure. -/
instance localAbsoluteCommutatorClosure_normal :
    (localAbsoluteCommutatorClosure K).Normal :=
  absoluteCommutatorClosure_normal K

/-- Compatibility name for the maximal abelian subextension. -/
abbrev localMaximalAbelianExtension :
    IntermediateField K (SeparableClosure K) :=
  maximalAbelianExtension K

/-- Compatibility instance for the Galois structure on the maximal abelian
subextension. -/
instance localMaximalAbelianExtension_isGalois :
    IsGalois K (localMaximalAbelianExtension K) :=
  maximalAbelianExtension_isGalois K

/-- Compatibility name for the underlying multiplicative equivalence. -/
noncomputable abbrev localAbsoluteAbelianizationMulEquiv :
    TopologicalAbelianization (intrinsicAbsoluteGalois K) ≃*
      Gal(localMaximalAbelianExtension K / K) :=
  absoluteAbelianizationMulEquivMaximalAbelianGalois K

/-- The compatibility equivalence sends a quotient class to restriction. -/
@[simp]
theorem localAbsoluteAbelianizationMulEquiv_mk
    (sigma : intrinsicAbsoluteGalois K) :
    localAbsoluteAbelianizationMulEquiv K (QuotientGroup.mk sigma) =
      AlgEquiv.restrictNormalHom (localMaximalAbelianExtension K) sigma :=
  absoluteAbelianizationMulEquivMaximalAbelianGalois_mk K sigma

/-- Compatibility form of continuity of the multiplicative equivalence. -/
theorem localAbsoluteAbelianizationMulEquiv_continuous :
    Continuous (localAbsoluteAbelianizationMulEquiv K) :=
  absoluteAbelianizationMulEquivMaximalAbelianGalois_continuous K

/-- Compatibility name for the canonical topological equivalence. -/
noncomputable abbrev localAbsoluteAbelianizationEquiv :
    TopologicalAbelianization (intrinsicAbsoluteGalois K) ≃ₜ*
      Gal(localMaximalAbelianExtension K / K) :=
  absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K

/-- Compatibility instance for total disconnectedness. -/
instance localAbsoluteTopologicalAbelianization_totallyDisconnectedSpace :
    TotallyDisconnectedSpace
      (TopologicalAbelianization (intrinsicAbsoluteGalois K)) :=
  absoluteTopologicalAbelianization_totallyDisconnectedSpace K

/-- Compatibility instance for the abelian Galois structure. -/
instance localMaximalAbelianExtension_isAbelianGalois :
    IsAbelianGalois K (localMaximalAbelianExtension K) :=
  maximalAbelianExtension_isAbelianGalois K

end LocalClassFieldTheory
