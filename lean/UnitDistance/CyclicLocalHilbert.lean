module

public import UnitDistance.RetainedCyclicLocalModels
public import UnitDistance.JenningsBinaryHilbert

@[expose] public section
set_option backward.privateInPublic true


/-! The augmentation Hilbert polynomials of the actual cyclic local groups,
proved from homogeneous directions in their genuine dimension filtration. -/
noncomputable section
open scoped BigOperators
namespace UnitDistance.RetainedCyclic
open OddLocal RetainedQuadratic GroupAugmentation Polynomial

theorem cyclicTwo_card : Nat.card (Cyclic 2)=2 := by
  simp [Cyclic,Nat.card_eq_fintype_card]
theorem cyclicFour_card : Nat.card (Cyclic 4)=4 := by
  simp [Cyclic,Nat.card_eq_fintype_card]
theorem cyclicTwo_isTwoGroup : IsPGroup 2 (Cyclic 2) := IsPGroup.of_card (n:=1) cyclicTwo_card
theorem cyclicFour_isTwoGroup : IsPGroup 2 (Cyclic 4) := IsPGroup.of_card (n:=2) cyclicFour_card

theorem cyclicTwo_hilbert : hilbertPolynomial (Cyclic 2)=1+X := by
  have h := hilbertPolynomial_of_homogeneous_generators (Cyclic 2) cyclicTwo_isTwoGroup
    1 (fun _ => cyclicGenerator 2) (fun _ => 1) (fun _ => le_rfl)
    (fun _ => by simp) ?_ (by rw [cyclicTwo_card]; decide)
  · simpa using h
  intro n hn
  by_cases hn1 : n=1
  · subst n
    rw [dimensionSubgroup_one]
    have he : {x : Cyclic 2 | ∃i : Fin 1,1≤(1 : ℕ) ∧ x=cyclicGenerator 2}=
        {cyclicGenerator 2} := by ext x; simp
    rw [he,cyclic_generates]
  · have hn2 : 2≤n := by omega
    have he := cyclicTwo_dimension_two infinityElement infinityElement_square infinityElement_base_ne_zero
    exact ((dimensionSubgroup_antitone F (Cyclic 2) hn2).trans he.le).trans bot_le

def fourDirections : Fin 2 → Cyclic 4 := ![cyclicGenerator 4,cyclicGenerator 4^2]
def fourWeights : Fin 2 → ℕ := ![1,2]

theorem fourDirections_mem (i : Fin 2) : fourDirections i∈dimensionSubgroup F (Cyclic 4) (fourWeights i) := by
  fin_cases i
  · simp [fourDirections,fourWeights]
  · exact square_mem F (Cyclic 4) (n:=1) (g:=cyclicGenerator 4) (by simp)

theorem fourDirections_generate (n : ℕ) (hn : 1≤n) : dimensionSubgroup F (Cyclic 4) n≤
    Subgroup.closure {x | ∃i : Fin 2,n≤fourWeights i ∧ x=fourDirections i} := by
  by_cases hn1 : n=1
  · subst n
    rw [dimensionSubgroup_one,←cyclic_generates 4]
    apply Subgroup.closure_mono
    intro x hx
    have hx' : x=cyclicGenerator 4 := hx
    exact ⟨0,by decide,hx'⟩
  by_cases hn2 : n=2
  · subst n
    apply cyclicFour_dimension_two_le.trans
    apply Subgroup.closure_mono
    intro x hx
    have hx' : x=cyclicGenerator 4^2 := hx
    exact ⟨1,by decide,hx'⟩
  have hn3 : 3≤n := by omega
  exact ((dimensionSubgroup_antitone F (Cyclic 4) hn3).trans cyclicFour_dimension_three.le).trans bot_le

theorem cyclicFour_hilbert : hilbertPolynomial (Cyclic 4)=(1+X)*(1+X^2) := by
  have h := hilbertPolynomial_of_homogeneous_generators (Cyclic 4) cyclicFour_isTwoGroup
    2 fourDirections fourWeights (by intro i; fin_cases i <;> decide)
    fourDirections_mem fourDirections_generate (by rw [cyclicFour_card]; decide)
  simpa [fourWeights,Fin.prod_univ_two] using h

end UnitDistance.RetainedCyclic
