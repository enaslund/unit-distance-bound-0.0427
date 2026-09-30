module

public import UnitDistance.ArithmeticRetainedModelGenerators
public import UnitDistance.RetainedQuadraticUniversal

@[expose] public section
set_option backward.privateInPublic true


/-! An actual isomorphism between the independently constructed retained
number field's Galois group and the independently defined bilinear finite
group. It is assembled from actual automorphisms, their proved actions on
actual radicals, and the proved collection law. -/
noncomputable section
namespace UnitDistance.ArithmeticRetained
open ArithmeticChosenGenus Multiquadratic ClassTwo.Collection

/-- The true genus coordinates vanish on every automorphism fixing the genus field. -/
theorem genusVector_eq_zero_of_fixes (σ : Gal(RetainedField/ℚ))
    (h : ∀ a : GenusField, σ (algebraMap GenusField RetainedField a)=
      algebraMap GenusField RetainedField a) : genusVector σ=0 := by
  have he : σ.restrictNormal GenusField=1 := by
    ext a
    apply (algebraMap GenusField RetainedField).injective
    simpa only [AlgEquiv.one_apply,AlgEquiv.restrictNormal_commutes] using h a
  change (genusGaloisEquiv.symm (σ.restrictNormal GenusField)).toAdd=0
  rw [he,map_one]
  rfl

@[simp] theorem genusVector_one : genusVector (1 : Gal(RetainedField/ℚ))=0 :=
  genusVector_eq_zero_of_fixes _ (fun _ => rfl)

@[simp] theorem genusVector_modelCentral (v : Multiplicative RetainedQuadratic.W) :
    genusVector (modelCentral v)=0 :=
  genusVector_eq_zero_of_fixes _ (modelCentral_fixes_genus v)

theorem genusVector_bit_basis (i : Fin 7) (t : ZMod 2) :
    genusVector (bit (basisLift i) t)=t • Pi.single i 1 := by
  rcases binary_cases t with rfl | rfl <;>
    simp [genusVector_basisLift]

theorem genusVector_basis_word (v : RetainedQuadratic.V) :
    genusVector (word basisLift RetainedQuadratic.Universal.indices v)=v := by
  simp only [word,RetainedQuadratic.Universal.indices,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,genusVector_mul,genusVector_one,genusVector_bit_basis]
  funext i
  fin_cases i <;> simp

/-- The actual homomorphism evaluating model coordinates in the actual Galois group. -/
def retainedModelHom : RetainedQuadratic.Q →* Gal(RetainedField/ℚ) :=
  RetainedQuadratic.Universal.modelHom modelCentral modelCentral_central basisLift
    basisLift_square basisLift_swap

theorem genusVector_retainedModelHom (q : RetainedQuadratic.Q) :
    genusVector (retainedModelHom q)=q.base := by
  change genusVector (modelCentral (Multiplicative.ofAdd q.central)*
    word basisLift RetainedQuadratic.Universal.indices q.base)=q.base
  rw [genusVector_mul,genusVector_modelCentral,genusVector_basis_word,zero_add]

theorem retainedModelHom_injective : Function.Injective retainedModelHom := by
  intro q r h
  have hb : q.base=r.base := by
    simpa only [genusVector_retainedModelHom] using congrArg genusVector h
  have hc : q.central=r.central := by
    have he : modelCentral (Multiplicative.ofAdd q.central)=
        modelCentral (Multiplicative.ofAdd r.central) := by
      apply mul_right_cancel (b := word basisLift RetainedQuadratic.Universal.indices r.base)
      change modelCentral (Multiplicative.ofAdd q.central)*
          word basisLift RetainedQuadratic.Universal.indices q.base=
        modelCentral (Multiplicative.ofAdd r.central)*
          word basisLift RetainedQuadratic.Universal.indices r.base at h
      simpa only [hb] using h
    exact congrArg Multiplicative.toAdd (modelCentral_injective he)
  exact ClassTwo.GroupModel.ext hb hc

theorem retainedModelHom_bijective : Function.Bijective retainedModelHom := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨retainedModelHom_injective,?_⟩
  rw [RetainedQuadratic.card_Q,retainedField_galoisGroup_card]
  norm_num

/-- The independent finite group model is the actual retained Galois group. -/
def retainedModelEquiv : RetainedQuadratic.Q ≃* Gal(RetainedField/ℚ) :=
  MulEquiv.ofBijective retainedModelHom retainedModelHom_bijective

theorem retainedModelEquiv_basis (i : Fin 7) :
    retainedModelEquiv (RetainedQuadratic.Universal.basis i)=basisLift i :=
  RetainedQuadratic.Universal.modelMap_basis modelCentral basisLift i

theorem retainedModelEquiv_central (v : RetainedQuadratic.W) :
    retainedModelEquiv (ClassTwo.GroupModel.centralHom RetainedQuadratic.cocycle
      (Multiplicative.ofAdd v))=modelCentral (Multiplicative.ofAdd v) :=
  RetainedQuadratic.Universal.modelMap_central modelCentral basisLift v

end UnitDistance.ArithmeticRetained
