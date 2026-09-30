/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.Completion.DegreeNormTrace
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.Completion.FiniteProductNormTrace

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Local components of the idele norm

The local algebra at a place of the base field is a finite product of the
completions above it. This file proves that the determinant norm on a finite
product is the product of the norms of its factors. The last theorem applies
this calculation to the canonical completion decomposition.
-/

open scoped BigOperators TensorProduct

noncomputable section


namespace RelativeIdeleGroup

open AlgebraicNumberTheory.Valuations
open ValuationTheory.Completion

universe u v

/-- At one place of the base field, under the
canonical isomorphism

`K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w`,

the determinant norm of an arbitrary local component is the product of
the field norms of its components above `v`. -/
theorem localNorm_eq_prod
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (z : vK.Completion ⊗[K] L) :
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w ↦ completionModuleFinite vK hvK w
    _root_.Algebra.norm vK.Completion z =
      ∏ w : AbsoluteValueExtension vK L,
        _root_.Algebra.norm vK.Completion
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK z w) := by
  classical
  let :=
    completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L,
      Algebra vK.Completion w.1.Completion :=
    fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Free vK.Completion w.1.Completion :=
    fun w ↦ Module.Free.of_divisionRing
      vK.Completion w.1.Completion
  let : ∀ w : AbsoluteValueExtension vK L,
      Module.Finite vK.Completion w.1.Completion :=
    fun w ↦ completionModuleFinite vK hvK w
  let e :=
    completionTensorDecomposition_left
      (K := K) (L := L) vK hvK
  calc
    _root_.Algebra.norm vK.Completion z =
        _root_.Algebra.norm vK.Completion (e z) :=
      (_root_.Algebra.norm_eq_of_algEquiv e z).symm
    _ = ∏ w : AbsoluteValueExtension vK L,
        _root_.Algebra.norm vK.Completion (e z w) :=
      algebra_norm_pi_apply
        (R := vK.Completion)
        (fun w : AbsoluteValueExtension vK L ↦
          w.1.Completion) (e z)

/-- The unit-valued version of `localNorm_eq_prod`, which is the formula
used for local components of ideles. -/
theorem localNorm_units_eq_prod
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (z : (vK.Completion ⊗[K] L)ˣ) :
    letI :=
      completionTensorDecomposition_extensionFintype
        (K := K) (L := L) vK hvK
    letI : ∀ w : AbsoluteValueExtension vK L,
        Algebra vK.Completion w.1.Completion :=
      fun w ↦ AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : ∀ w : AbsoluteValueExtension vK L,
        Module.Finite vK.Completion w.1.Completion :=
      fun w ↦ completionModuleFinite vK hvK w
    ((Units.map (_root_.Algebra.norm vK.Completion) z :
        vK.Completionˣ) : vK.Completion) =
      ∏ w : AbsoluteValueExtension vK L,
        _root_.Algebra.norm vK.Completion
          (completionTensorDecomposition_left
            (K := K) (L := L) vK hvK (z : _) w) := by
  exact localNorm_eq_prod vK hvK (z : vK.Completion ⊗[K] L)

end RelativeIdeleGroup
