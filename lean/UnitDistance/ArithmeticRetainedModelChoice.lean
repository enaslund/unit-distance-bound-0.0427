module

public import UnitDistance.ArithmeticRetainedModel

@[expose] public section
set_option backward.privateInPublic true


/-! The retained-field comparison works for any actual seven lifts of the
genus basis, so it can be aligned with a given arithmetic presentation. -/
noncomputable section
namespace UnitDistance.ArithmeticRetained
open ArithmeticChosenGenus Multiquadratic ClassTwo.Collection

theorem commutator_eq_of_genusVector_eq {σ τ σ' τ' : Gal(RetainedField/ℚ)}
    (hσ : genusVector σ=genusVector σ') (hτ : genusVector τ=genusVector τ') :
    σ⁻¹*τ⁻¹*σ*τ=σ'⁻¹*τ'⁻¹*σ'*τ' := by
  apply retained_aut_ext_roots
  · intro a
    rw [fixes_genus_of_vector_zero _ (commutator_genusVector σ τ),
      fixes_genus_of_vector_zero _ (commutator_genusVector σ' τ')]
  · intro j
    rw [commutator_action_on_radical _ _ j _ (retainedRoot_sq j),
      commutator_action_on_radical _ _ j _ (retainedRoot_sq j),hσ,hτ]

variable (g : Fin 7 → Gal(RetainedField/ℚ))
  (hg : ∀ i, genusVector (g i)=Pi.single i 1)
include hg

theorem genus_basis_lifts_square (i : Fin 7) : g i^2=1 := basis_lift_square _ i (hg i)

theorem genus_basis_lifts_swap (i j : Fin 7) :
    g i*g j=modelCentral (Multiplicative.ofAdd
      (RetainedQuadratic.Universal.swapCoordinate i j))*g j*g i := by
  have hc : (g i)⁻¹*(g j)⁻¹*g i*g j=
      modelCentral (Multiplicative.ofAdd (RetainedQuadratic.Universal.swapCoordinate i j)) :=
    (commutator_eq_of_genusVector_eq
      ((hg i).trans (genusVector_basisLift i).symm)
      ((hg j).trans (genusVector_basisLift j).symm)).trans (basisLift_commutator i j)
  calc
    g i*g j=(g j*g i)*((g i)⁻¹*(g j)⁻¹*g i*g j) := by group
    _ = _ := by
      rw [hc,(modelCentral_central _ (g j*g i)).symm.eq]
      group

theorem genusVector_bit_of_lifts (i : Fin 7) (t : ZMod 2) :
    genusVector (bit (g i) t)=t • Pi.single i 1 := by
  rcases binary_cases t with rfl | rfl <;> simp [hg]

theorem genusVector_word_of_lifts (v : RetainedQuadratic.V) :
    genusVector (word g RetainedQuadratic.Universal.indices v)=v := by
  simp only [word,RetainedQuadratic.Universal.indices,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,genusVector_mul,genusVector_one,genusVector_bit_of_lifts g hg]
  funext i
  fin_cases i <;> simp

/-- Actual evaluation using the basis lifts supplied by an arithmetic presentation. -/
def retainedModelHomOfLifts : RetainedQuadratic.Q →* Gal(RetainedField/ℚ) :=
  RetainedQuadratic.Universal.modelHom modelCentral modelCentral_central g
    (genus_basis_lifts_square g hg) (genus_basis_lifts_swap g hg)

theorem genusVector_retainedModelHomOfLifts (q : RetainedQuadratic.Q) :
    genusVector (retainedModelHomOfLifts g hg q)=q.base := by
  change genusVector (modelCentral (Multiplicative.ofAdd q.central)*
    word g RetainedQuadratic.Universal.indices q.base)=q.base
  rw [genusVector_mul,genusVector_modelCentral,genusVector_word_of_lifts g hg,zero_add]

theorem retainedModelHomOfLifts_injective : Function.Injective (retainedModelHomOfLifts g hg) := by
  intro q r h
  have hb : q.base=r.base := by
    simpa only [genusVector_retainedModelHomOfLifts] using congrArg genusVector h
  have hc : q.central=r.central := by
    have he : modelCentral (Multiplicative.ofAdd q.central)=
        modelCentral (Multiplicative.ofAdd r.central) := by
      apply mul_right_cancel (b := word g RetainedQuadratic.Universal.indices r.base)
      change modelCentral (Multiplicative.ofAdd q.central)*
          word g RetainedQuadratic.Universal.indices q.base=
        modelCentral (Multiplicative.ofAdd r.central)*
          word g RetainedQuadratic.Universal.indices r.base at h
      simpa only [hb] using h
    exact congrArg Multiplicative.toAdd (modelCentral_injective he)
  exact ClassTwo.GroupModel.ext hb hc

/-- The actual isomorphism can be aligned with any seven actual genus basis lifts. -/
def retainedModelEquivOfLifts : RetainedQuadratic.Q ≃* Gal(RetainedField/ℚ) :=
  MulEquiv.ofBijective (retainedModelHomOfLifts g hg) (by
    apply (Nat.bijective_iff_injective_and_card _).mpr
    refine ⟨retainedModelHomOfLifts_injective g hg,?_⟩
    rw [RetainedQuadratic.card_Q,retainedField_galoisGroup_card]
    norm_num)

theorem retainedModelEquivOfLifts_basis (i : Fin 7) :
    retainedModelEquivOfLifts g hg (RetainedQuadratic.Universal.basis i)=g i :=
  RetainedQuadratic.Universal.modelMap_basis modelCentral g i

end UnitDistance.ArithmeticRetained
