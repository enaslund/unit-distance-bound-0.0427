module

public import UnitDistance.ProTwoElementaryQuotient
public import UnitDistance.ArithmeticChosenGenusRoots
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true


/-! Actual restriction to the genus field and the seven-generator consequence
of exhaustive quadratic-subfield classification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticGenusFrattini
open ArithmeticChosenGenus ClassFieldTower.ProP
open ProCGroups ProCGroups.ProC ProCGroups.Generation ProCGroups.FiniteGeneration

abbrev VectorGroup := Multiplicative (Fin 7 → ZMod 2)
instance vectorGroupTopology : TopologicalSpace VectorGroup := ⊥
instance vectorGroupDiscrete : DiscreteTopology VectorGroup := ⟨rfl⟩
instance vectorGroupTopologicalGroup : IsTopologicalGroup VectorGroup := inferInstance
instance vectorGroupT2 : T2Space VectorGroup := inferInstance

local instance ratSelfSMul : SMul ℚ ℚ := instSMulOfMul

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]

local instance rationalSubfieldAlgebra (E : IntermediateField ℚ Ω) : Algebra ℚ E :=
  E.algebra'
local instance rationalSubfieldModule (E : IntermediateField ℚ Ω) : Module ℚ E :=
  Algebra.toModule

/-- Actual Galois restriction, identified with the seven actual root signs. -/
def genusRestriction (E : IntermediateField ℚ Ω) [Normal ℚ E] [Module.Finite ℚ E]
    (e : E ≃ₐ[ℚ] GenusField) : Gal(Ω/ℚ) →ₜ* VectorGroup where
  toMonoidHom := genusGaloisEquiv.symm.toMonoidHom.comp
    ((AlgEquiv.autCongr e).toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) E))
  continuous_toFun := by
    exact (continuous_of_discreteTopology : Continuous
      (fun σ : Gal(E/ℚ) ↦ genusGaloisEquiv.symm (AlgEquiv.autCongr e σ))).comp
      (InfiniteGalois.restrictNormalHom_continuous E)

theorem genusRestriction_surjective (E : IntermediateField ℚ Ω) [Normal ℚ E] [Module.Finite ℚ E]
    (e : E ≃ₐ[ℚ] GenusField) : Function.Surjective (genusRestriction E e) :=
  genusGaloisEquiv.symm.surjective.comp ((AlgEquiv.autCongr e).surjective.comp
    (AlgEquiv.restrictNormalHom_surjective Ω))

theorem genusRestriction_ker (E : IntermediateField ℚ Ω) [Normal ℚ E] [Module.Finite ℚ E]
    (e : E ≃ₐ[ℚ] GenusField) : (genusRestriction E e).toMonoidHom.ker = E.fixingSubgroup := by
  have hker : (genusRestriction E e).toMonoidHom.ker = (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) E).ker := by
    ext σ
    change genusGaloisEquiv.symm (AlgEquiv.autCongr e (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) E σ)) = 1 ↔
      AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) E σ = 1
    rw [map_eq_one_iff _ genusGaloisEquiv.symm.injective,
      map_eq_one_iff _ (AlgEquiv.autCongr e).injective]
  exact hker.trans E.restrictNormalHom_ker

theorem vectorGroup_pow_two (a : VectorGroup) : a ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  change (2 : ℕ) • a.toAdd = 0
  funext i
  simp [two_nsmul, ← two_mul, show (2 : ZMod 2) = 0 by decide]

theorem vectorGroup_card : Nat.card VectorGroup = 2 ^ 7 := by
  rw [Nat.card_congr (Multiplicative.toAdd : VectorGroup ≃ (Fin 7 → ZMod 2))]
  simp

/-- The finite genus quotient is the actual Frattini quotient once every
quadratic fixed field has been shown to lie in the actual genus subfield. -/
theorem frattini_eq_genusFixing
    (hG : HasPGroupOpenNormalBasis 2 Gal(Ω/ℚ))
    (E : IntermediateField ℚ Ω) [Normal ℚ E] [Module.Finite ℚ E] (e : E ≃ₐ[ℚ] GenusField)
    (hquadratic : ∀ U : OpenNormalSubgroup Gal(Ω/ℚ),
      (U : Subgroup Gal(Ω/ℚ)).index = 2 →
      IntermediateField.fixedField (U : Subgroup Gal(Ω/ℚ)) ≤ E) :
    closedPowerCommutator 2 Gal(Ω/ℚ) = E.fixingSubgroup := by
  rw [← genusRestriction_ker E e]
  apply ProTwoElementaryQuotient.closedPowerCommutator_eq_ker hG
    (genusRestriction E e) vectorGroup_pow_two
  intro U hU
  rw [genusRestriction_ker E e]
  have h := IntermediateField.fixingSubgroup_le (hquadratic U hU)
  have he := InfiniteGalois.fixingSubgroup_fixedField
    (⟨(U : Subgroup Gal(Ω/ℚ)), U.isClosed⟩ : ClosedSubgroup Gal(Ω/ℚ))
  rwa [he] at h

/-- Exhaustion of the actual quadratic subfields proves seven generators
and exact topological generator rank seven. -/
theorem generatorRank_seven
    (hG : HasPGroupOpenNormalBasis 2 Gal(Ω/ℚ))
    (E : IntermediateField ℚ Ω) [Normal ℚ E] [Module.Finite ℚ E] (e : E ≃ₐ[ℚ] GenusField)
    (hquadratic : ∀ U : OpenNormalSubgroup Gal(Ω/ℚ),
      (U : Subgroup Gal(Ω/ℚ)).index = 2 →
      IntermediateField.fixedField (U : Subgroup Gal(Ω/ℚ)) ≤ E) :
    TopologicallyGeneratedByAtMost 7 Gal(Ω/ℚ) ∧ topologicalGeneratorRank Gal(Ω/ℚ) = 7 := by
  letI : (closedPowerCommutator 2 Gal(Ω/ℚ)).Normal :=
    closedPowerCommutator_normal 2 Gal(Ω/ℚ)
  have hk : closedPowerCommutator 2 Gal(Ω/ℚ) = (genusRestriction E e).toMonoidHom.ker :=
    (frattini_eq_genusFixing hG E e hquadratic).trans (genusRestriction_ker E e).symm
  let eqv : powerCommutatorQuotient 2 Gal(Ω/ℚ) ≃* VectorGroup :=
    QuotientGroup.liftEquiv _ (genusRestriction_surjective E e) hk
  exact ProTwoElementaryQuotient.generatorRank_of_powerCommutator_card hG 7
    ((Nat.card_congr eqv.toEquiv).trans vectorGroup_card)

end UnitDistance.ArithmeticGenusFrattini
