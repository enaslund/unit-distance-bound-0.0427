module

public import UnitDistance.ArithmeticDyadicInertiaCards
public import UnitDistance.ArithmeticDyadicModel

@[expose] public section
set_option backward.privateInPublic true


/-!
# The intrinsic dyadic inertia on the ramified retained direction

This file identifies the two central elements of the concrete dyadic model
that matter for separating the ramified quadratic direction from the
unramified complement.  The argument uses the actual residue action of the
completed retained field.  In particular, it does not infer a different
exponent from the abstract inertia order.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ValuativeRel
open scoped IsMulCommutative
namespace UnitDistance

namespace Dyadic.D

/-- In any cyclic quotient of order four of the concrete dyadic group, the
image of the Frobenius generator has nontrivial square. -/
theorem z_sq_not_ker_of_surjective_cyclic_card_four
    {A : Type*} [Group A] [Finite A] [IsCyclic A]
    (f : D →* A) (hf : Function.Surjective f) (hcard : Nat.card A = 4) :
    f (z ^ 2) ≠ 1 := by
  letI : CommGroup A := IsCyclic.commGroup
  intro hz
  have hall : ∀ d : D, (f d) ^ 2 = 1 := by
    intro d
    rw [← normal_form d, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow,
      map_pow]
    have hx : (f x) ^ 2 = 1 := by rw [← map_pow, x_sq, map_one]
    have hy : (f y) ^ 2 = 1 := by rw [← map_pow, y_sq, map_one]
    have hw : (f w) ^ 2 = 1 := by rw [← map_pow, w_sq, map_one]
    have hz' : (f z) ^ 2 = 1 := by simpa only [map_pow] using hz
    have hx' : (f x ^ d.a.val) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm d.a.val 2, pow_mul, hx, one_pow]
    have hy' : (f y ^ d.b.val) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm d.b.val 2, pow_mul, hy, one_pow]
    have hz'' : (f z ^ d.c.val) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm d.c.val 2, pow_mul, hz', one_pow]
    have hw' : (f w ^ d.d.val) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm d.d.val 2, pow_mul, hw, one_pow]
    simp only [mul_pow]
    simp only [hx', hy', hz'', hw', one_mul]
  obtain ⟨g, hg⟩ :=
    (isCyclic_iff_exists_orderOf_eq_natCard (α := A)).mp inferInstance
  have hgord : orderOf g = 4 := hg.trans hcard
  obtain ⟨d, rfl⟩ := hf g
  have hdvd : orderOf (f d) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (hall d)
  rw [hgord] at hdvd
  norm_num at hdvd

end Dyadic.D

namespace RetainedQuadratic

/-- The canonical local commutator is the central retained coordinate with
mask `2747`. -/
theorem dyadicMap_w_coordinates :
    dyadicMap Dyadic.D.w =
      ClassTwo.GroupModel.centralHom cocycle
        (Multiplicative.ofAdd (binaryVector 12 2747)) := by
  apply ClassTwo.GroupModel.ext <;> funext i <;> fin_cases i <;> decide +kernel

/-- The square of the canonical Frobenius lift is the central retained
coordinate with mask `3693`. -/
theorem dyadicMap_z_sq_coordinates :
    dyadicMap (Dyadic.D.z ^ 2) =
      ClassTwo.GroupModel.centralHom cocycle
        (Multiplicative.ofAdd (binaryVector 12 3693)) := by
  apply ClassTwo.GroupModel.ext <;> funext i <;> fin_cases i <;> decide +kernel

/-- The kernel of the genus-coordinate projection inside the canonical
dyadic group consists of the two central directions `w` and `z²`. -/
theorem dyadicMap_base_eq_zero_iff (d : Dyadic.D) :
    (dyadicMap d).base = 0 ↔
      d = 1 ∨ d = Dyadic.D.w ∨ d = Dyadic.D.z ^ 2 ∨
        d = Dyadic.D.w * Dyadic.D.z ^ 2 := by
  change (dyadicMapFn d).base = 0 ↔ _
  set_option maxHeartbeats 4000000 in
    decide +kernel +revert

end RetainedQuadratic

namespace CatalogRetainedCoordinates

/-- In actual retained-root coordinates, the local commutator flips only
root number eleven. -/
theorem toSigns_dyadic_w :
    toSigns (RetainedQuadratic.binaryVector 12 2747) =
      RetainedQuadratic.binaryVector 12 2048 := by
  funext i
  fin_cases i <;> decide +kernel

/-- In actual retained-root coordinates, the square of the Frobenius lift
flips roots `2, 7, 10, 11`. -/
theorem toSigns_dyadic_z_sq :
    toSigns (RetainedQuadratic.binaryVector 12 3693) =
      RetainedQuadratic.binaryVector 12 3204 := by
  funext i
  fin_cases i <;> decide +kernel

end CatalogRetainedCoordinates

namespace ArithmeticDyadic

open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open ArithmeticRetained Multiquadratic
local instance retainedDifferentFactTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance retainedDifferentNormedField : NontriviallyNormedField LocalField :=
  intrinsicNormedField
local instance retainedDifferentValuativeRel : ValuativeRel LocalField :=
  intrinsicValuativeRel
local instance retainedDifferentLocalField : IsNonarchimedeanLocalField LocalField :=
  intrinsicLocalField
local instance retainedDifferentHasExtension :
    Valuation.HasExtension (ValuativeRel.valuation ℚ_[2])
      (ValuativeRel.valuation LocalField) := intrinsicHasExtension
local instance retainedDifferentIntegralClosure :
    IsIntegralClosure 𝒪[LocalField] 𝒪[ℚ_[2]] LocalField := intrinsicIntegralClosure

abbrev IntrinsicResidueGalois :=
  𝓀[LocalField] ≃ₐ[𝓀[ℚ_[2]]] 𝓀[LocalField]

/-- The actual residue action, expressed on the concrete order-32 model. -/
def intrinsicResidueModelMap : Dyadic.D →* IntrinsicResidueGalois :=
  intrinsicResidueAction.comp galoisEquiv.toMonoidHom

@[simp] theorem dyadicModelMap_base (d : Dyadic.D) :
    (dyadicModelMap d).base = (RetainedQuadratic.dyadicMap d).base := rfl

theorem intrinsicResidueModelMap_surjective :
    Function.Surjective intrinsicResidueModelMap :=
  (ArithmeticProP.intrinsicResidueAction_surjective ℚ_[2] LocalField).comp
    galoisEquiv.surjective

theorem intrinsicResidueGalois_card : Nat.card IntrinsicResidueGalois = 4 := by
  rw [residueAlgEquiv_card_eq_finrank ℚ_[2] LocalField]
  exact actual_residueDegree_inertia_card.1

/-- The lift adjustment used to match the actual local generators is
invisible on elements whose canonical retained-model base coordinate is
zero. -/
theorem dyadicModelMap_eq_dyadicMap_of_base_eq_zero (d : Dyadic.D)
    (hd : (RetainedQuadratic.dyadicMap d).base = 0) :
    dyadicModelMap d = RetainedQuadratic.dyadicMap d := by
  change ClassTwo.GroupModel.centralShear RetainedQuadratic.cocycle _
      (RetainedQuadratic.dyadicMap d) = RetainedQuadratic.dyadicMap d
  apply ClassTwo.GroupModel.ext
  · rfl
  · change (RetainedQuadratic.dyadicMap d).central +
      RetainedQuadratic.dyadicAdjustment _ _ _
        (RetainedQuadratic.dyadicMap d).base =
        (RetainedQuadratic.dyadicMap d).central
    rw [hd, map_zero, add_zero]

theorem dyadicModelMap_w :
    dyadicModelMap Dyadic.D.w =
      ClassTwo.GroupModel.centralHom RetainedQuadratic.cocycle
        (Multiplicative.ofAdd (RetainedQuadratic.binaryVector 12 2747)) := by
  rw [dyadicModelMap_eq_dyadicMap_of_base_eq_zero,
    RetainedQuadratic.dyadicMap_w_coordinates]
  rw [RetainedQuadratic.dyadicMap_w_coordinates]
  rfl

theorem dyadicModelMap_z_sq :
    dyadicModelMap (Dyadic.D.z ^ 2) =
      ClassTwo.GroupModel.centralHom RetainedQuadratic.cocycle
        (Multiplicative.ofAdd (RetainedQuadratic.binaryVector 12 3693)) := by
  rw [dyadicModelMap_eq_dyadicMap_of_base_eq_zero,
    RetainedQuadratic.dyadicMap_z_sq_coordinates]
  rw [RetainedQuadratic.dyadicMap_z_sq_coordinates]
  rfl

/-- The global restriction of the actual local commutator flips precisely
the retained root with index eleven. -/
theorem restriction_galoisEquiv_w_action (j : Fin 12) :
    restriction (galoisEquiv Dyadic.D.w) (ArithmeticRetained.retainedRoot j) =
      binarySign (RetainedQuadratic.binaryVector 12 2048 j) *
        ArithmeticRetained.retainedRoot j := by
  have hrestriction :
      restriction (galoisEquiv Dyadic.D.w) =
        ArithmeticRetained.retainedModelEquiv
          (ClassTwo.GroupModel.centralHom RetainedQuadratic.cocycle
            (Multiplicative.ofAdd (RetainedQuadratic.binaryVector 12 2747))) := by
    apply ArithmeticRetained.retainedModelEquiv.symm.injective
    change model (galoisEquiv Dyadic.D.w) = _
    rw [model_galoisEquiv, dyadicModelMap_w]
    simp
  rw [hrestriction, ArithmeticRetained.retainedModelEquiv_central,
    ArithmeticRetained.modelCentral_action, toAdd_ofAdd,
    CatalogRetainedCoordinates.toSigns_dyadic_w]

/-- The global restriction of the actual squared Frobenius flips retained
roots `2, 7, 10, 11`. -/
theorem restriction_galoisEquiv_z_sq_action (j : Fin 12) :
    restriction (galoisEquiv (Dyadic.D.z ^ 2))
        (ArithmeticRetained.retainedRoot j) =
      binarySign (RetainedQuadratic.binaryVector 12 3204 j) *
        ArithmeticRetained.retainedRoot j := by
  have hrestriction :
      restriction (galoisEquiv (Dyadic.D.z ^ 2)) =
        ArithmeticRetained.retainedModelEquiv
          (ClassTwo.GroupModel.centralHom RetainedQuadratic.cocycle
            (Multiplicative.ofAdd (RetainedQuadratic.binaryVector 12 3693))) := by
    apply ArithmeticRetained.retainedModelEquiv.symm.injective
    change model (galoisEquiv (Dyadic.D.z ^ 2)) = _
    rw [model_galoisEquiv, dyadicModelMap_z_sq]
    simp
  rw [hrestriction, ArithmeticRetained.retainedModelEquiv_central,
    ArithmeticRetained.modelCentral_action, toAdd_ofAdd,
    CatalogRetainedCoordinates.toSigns_dyadic_z_sq]

/-- The central commutator direction belongs to the actual intrinsic
inertia. -/
theorem galoisEquiv_w_mem_intrinsicInertia :
    galoisEquiv Dyadic.D.w ∈ intrinsicInertia := by
  change intrinsicResidueModelMap Dyadic.D.w = 1
  rw [← Dyadic.D.comm_y_z]
  change intrinsicResidueModelMap
    (Dyadic.D.y⁻¹ * Dyadic.D.z⁻¹ * Dyadic.D.y * Dyadic.D.z) = 1
  simp only [map_mul, map_inv]
  let a := intrinsicResidueModelMap Dyadic.D.y
  let b := intrinsicResidueModelMap Dyadic.D.z
  change a⁻¹ * b⁻¹ * a * b = 1
  calc
    a⁻¹ * b⁻¹ * a * b = a⁻¹ * (b⁻¹ * a) * b := by simp only [mul_assoc]
    _ = a⁻¹ * (a * b⁻¹) * b := by rw [mul_comm b⁻¹ a]
    _ = 1 := by simp [← mul_assoc]

/-- The square of the Frobenius direction is not in the actual intrinsic
inertia. -/
theorem galoisEquiv_z_sq_not_mem_intrinsicInertia :
    galoisEquiv (Dyadic.D.z ^ 2) ∉ intrinsicInertia := by
  change intrinsicResidueModelMap (Dyadic.D.z ^ 2) ≠ 1
  exact Dyadic.D.z_sq_not_ker_of_surjective_cyclic_card_four
    intrinsicResidueModelMap intrinsicResidueModelMap_surjective
      intrinsicResidueGalois_card

/-- Among actual local automorphisms that fix the genus field, intrinsic
inertia is exactly the order-two commutator direction. -/
theorem galoisEquiv_mem_intrinsicInertia_and_base_zero_iff (d : Dyadic.D) :
    (galoisEquiv d ∈ intrinsicInertia ∧ (dyadicModelMap d).base = 0) ↔
      d = 1 ∨ d = Dyadic.D.w := by
  constructor
  · rintro ⟨hdinertia, hdbase⟩
    rw [dyadicModelMap_base] at hdbase
    have hcanonical : (RetainedQuadratic.dyadicMap d).base = 0 := hdbase
    rcases (RetainedQuadratic.dyadicMap_base_eq_zero_iff d).mp hcanonical with
      rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (galoisEquiv_z_sq_not_mem_intrinsicInertia hdinertia).elim
    · exfalso
      change intrinsicResidueModelMap
        (Dyadic.D.w * Dyadic.D.z ^ 2) = 1 at hdinertia
      have hw : intrinsicResidueModelMap Dyadic.D.w = 1 := by
        exact galoisEquiv_w_mem_intrinsicInertia
      rw [map_mul, hw, one_mul] at hdinertia
      exact galoisEquiv_z_sq_not_mem_intrinsicInertia hdinertia
  · rintro (rfl | rfl)
    · constructor
      · change intrinsicResidueModelMap 1 = 1
        simp
      · rw [dyadicModelMap_base]
        simp
    · constructor
      · exact galoisEquiv_w_mem_intrinsicInertia
      · rw [dyadicModelMap_w]
        rfl

/-- Valuation-theoretic version of `galoisEquiv_w_mem_intrinsicInertia`. -/
theorem galoisEquiv_w_mem_inertia : galoisEquiv Dyadic.D.w ∈ inertia := by
  rw [← intrinsicInertia_eq]
  exact galoisEquiv_w_mem_intrinsicInertia

/-- Valuation-theoretic version of `galoisEquiv_z_sq_not_mem_intrinsicInertia`. -/
theorem galoisEquiv_z_sq_not_mem_inertia :
    galoisEquiv (Dyadic.D.z ^ 2) ∉ inertia := by
  rw [← intrinsicInertia_eq]
  exact galoisEquiv_z_sq_not_mem_intrinsicInertia

end ArithmeticDyadic

end UnitDistance
