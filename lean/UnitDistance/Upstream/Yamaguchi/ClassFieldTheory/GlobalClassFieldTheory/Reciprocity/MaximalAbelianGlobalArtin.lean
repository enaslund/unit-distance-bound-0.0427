/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinDescent
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinSurjectivity

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Global Artin map for the maximal abelian extension

This module specializes the continuous infinite global Artin map to the
maximal abelian subextension of the separable closure.  It also exposes the
idele-representative evaluation and its finite Galois projections.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable (K : Type) [Field K] [NumberField K]

/-- The continuous global Artin homomorphism from the idele class group to
the Galois group of the maximal abelian extension. -/
noncomputable def maximalAbelianGlobalArtin :
    IdeleClassGroup K →ₜ* Gal(maximalAbelianExtension K / K) :=
  infiniteGlobalIdeleClassArtinContinuousMonoidHom
    (K := K) (Ω := maximalAbelianExtension K)

/-- Evaluation of the maximal abelian global Artin map on an idele
representative recovers the infinite global Artin map. -/
@[simp]
theorem maximalAbelianGlobalArtin_mk (a : IdeleGroup K) :
    maximalAbelianGlobalArtin K
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a) =
      infiniteGlobalArtinMonoidHom K (maximalAbelianExtension K) a :=
  infiniteGlobalIdeleClassArtinMonoidHom_mk
    (K := K) (Ω := maximalAbelianExtension K) a

/-- Projection of the maximal abelian global Artin map at an idele
representative to a finite Galois intermediate field agrees with the finite
global Artin map. -/
@[simp]
theorem maximalAbelianGlobalArtin_finiteProjection
    (a : IdeleGroup K)
    (E : FiniteGaloisIntermediateField K (maximalAbelianExtension K)) :
    letI : NumberField E := NumberField.of_module_finite K E
    AlgEquiv.restrictNormalHom E
        (maximalAbelianGlobalArtin K
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a)) =
      globalArtinMonoidHom (K := K) (L := E) a := by
  let : NumberField E := NumberField.of_module_finite K E
  rw [maximalAbelianGlobalArtin_mk]
  exact
    restrictNormalHom_infiniteGlobalArtinMonoidHom
      K (maximalAbelianExtension K) a E

/-- The maximal abelian global Artin homomorphism is surjective. -/
theorem maximalAbelianGlobalArtin_surjective :
    Function.Surjective (maximalAbelianGlobalArtin K) :=
  infiniteGlobalIdeleClassArtinContinuousMonoidHom_surjective
    K (maximalAbelianExtension K)

end Reciprocity
end GlobalClassFieldTheory
