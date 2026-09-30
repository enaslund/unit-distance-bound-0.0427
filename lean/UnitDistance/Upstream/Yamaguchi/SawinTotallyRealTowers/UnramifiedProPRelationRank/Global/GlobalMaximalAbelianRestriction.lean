/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteExtensionCorrespondence

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false
/-! # Restriction to the actual maximal abelian subextension -/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

variable (F : Type) [Field F]

/-- Restrict the standard absolute Galois group to the maximal abelian
subextension of the fixed separable closure. -/
noncomputable def globalMaximalAbelianRestriction :
    Field.absoluteGaloisGroup F →ₜ* Gal(_root_.maximalAbelianExtension F / F) :=
  ({ toMonoidHom := AlgEquiv.restrictNormalHom (_root_.maximalAbelianExtension F)
     continuous_toFun := InfiniteGalois.restrictNormalHom_continuous
       (_root_.maximalAbelianExtension F) } :
      Gal(SeparableClosure F / F) →ₜ* Gal(_root_.maximalAbelianExtension F / F)).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv F))

@[simp]
theorem globalMaximalAbelianRestriction_apply (sigma : Field.absoluteGaloisGroup F) :
    globalMaximalAbelianRestriction F sigma =
      AlgEquiv.restrictNormalHom (_root_.maximalAbelianExtension F)
        (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv F sigma) :=
  rfl

/-- Absolute automorphisms surject onto the maximal abelian Galois group. -/
theorem globalMaximalAbelianRestriction_surjective :
    Function.Surjective (globalMaximalAbelianRestriction F) :=
  (AlgEquiv.restrictNormalHom_surjective
    (F := F) (K₁ := _root_.maximalAbelianExtension F) (SeparableClosure F)).comp
      (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv F).surjective

end ClassFieldTower.Martinet.Shafarevich
