module

public import UnitDistance.RetainedOddLocalModels
public import UnitDistance.JenningsGeneratedLayers
public import UnitDistance.JenningsBinaryHilbert
public import Mathlib.Algebra.Module.Pi

@[expose] public section
set_option backward.privateInPublic true


/-! Exact augmentation Hilbert polynomials of the actual order-four and
order-eight odd local models, derived from their weighted Jennings bases. -/
noncomputable section
open scoped BigOperators
namespace UnitDistance.OddLocal
open GroupAugmentation RetainedQuadratic
open Polynomial
local notation "F" => ZMod 2

-- These coordinatewise structures are local to the odd-model development;
-- the imported model file's local instances do not cross module boundaries.
local instance : AddCommGroup F := Ring.toAddCommGroup
local instance : Module F F := Semiring.toModule
local instance : AddCommGroup V := Pi.addCommGroup
local instance : AddCommGroup W := Pi.addCommGroup
local instance : Module F V := Pi.Function.module (Fin 7) F F
local instance : Module F W := Pi.Function.module (Fin 12) F F

def rank (i : Fin 5) : ℕ := if i.val<2 then 2 else 3
def directions (i : Fin 5) (j : Fin (rank i)) : D i :=
  if j.val=0 then inertia i else if j.val=1 then frobenius i else frobenius i^2
def weight (i : Fin 5) (j : Fin (rank i)) : ℕ := if j.val<2 then 1 else 2

theorem two_pow_rank (i : Fin 5) : 2^rank i=Nat.card (D i) := by
  rw [card]
  fin_cases i <;> norm_num [rank,residueDegree]

theorem isTwoGroup (i : Fin 5) : IsPGroup 2 (D i) := IsPGroup.of_card (two_pow_rank i).symm

theorem directions_mem (i : Fin 5) (j : Fin (rank i)) :
    directions i j∈dimensionSubgroup F (D i) (weight i j) := by
  by_cases hj : j.val<2
  · simp [weight,hj]
  · have h0 : j.val≠0 := by omega
    have h1 : j.val≠1 := by omega
    simp only [weight,hj,ite_false,directions,h0,h1]
    exact square_mem F (D i) (n := 1) (g := frobenius i) (by simp)

theorem dimension_two_cases (i : Fin 5) (g : D i)
    (hg : g∈dimensionSubgroup F (D i) 2) : g=1 ∨ g=frobenius i^2 := by
  have hm := map_dimensionSubgroup_le F (D i) (oddMap i) 2 ⟨g,hg,rfl⟩
  have hb := ClassTwo.GroupModel.base_eq_zero_of_mem_dimension_two cocycle (oddMap i g) hm
  rw [oddMap_eq_fn] at hb
  exact oddMap_first_layer_certificate i g (fun k ↦ congrFun hb k)

theorem low_frobenius_square (i : Fin 5) (hi : i.val<2) : frobenius i^2=1 := by
  have hc : i=0 ∨ i=1 := by omega
  rcases hc with rfl | rfl <;> decide +kernel

theorem weighted_generation (i : Fin 5) (n : ℕ) (hn : 1≤n) :
    dimensionSubgroup F (D i) n≤Subgroup.closure {x | ∃ j, n≤weight i j ∧ x=directions i j} := by
  have hr : 2≤rank i := by unfold rank; split <;> omega
  rcases n with _ | _ | _ | n
  · omega
  · have hle : Subgroup.closure ({inertia i,frobenius i} : Set (D i))≤
        Subgroup.closure {x | ∃ j, 1≤weight i j ∧ x=directions i j} := by
      apply Subgroup.closure_mono
      intro x hx
      rcases hx with rfl | rfl
      · exact ⟨⟨0,by omega⟩,by simp [weight],by simp [directions]⟩
      · exact ⟨⟨1,by omega⟩,by simp [weight],by simp [directions]⟩
    rw [generators] at hle
    exact le_top.trans hle
  · intro g hg
    rcases dimension_two_cases i g hg with rfl | rfl
    · exact Subgroup.one_mem _
    · by_cases hi : i.val<2
      · rw [low_frobenius_square i hi]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨⟨2,by simp [rank,hi]⟩,
          by simp [weight],by simp [directions]⟩
  · intro g hg
    have h3 := dimensionSubgroup_antitone F (D i) (show 3≤n+3 by omega) hg
    rw [odd_dimensionSubgroup_three,Subgroup.mem_bot] at h3
    simpa [h3] using (Subgroup.one_mem (Subgroup.closure
      {x | ∃ j, n+3≤weight i j ∧ x=directions i j}))

theorem spansLayers (i : Fin 5) : SpansActualLayers (D i) (Fin (rank i)) (directions i) (weight i) :=
  spansActualLayers_of_generation (D i) (directions i) (weight i)
    (directions_mem i) (weighted_generation i)

theorem weight_pos (i : Fin 5) (j : Fin (rank i)) : 1≤weight i j := by
  unfold weight
  split <;> omega

def augmentationBasis (i : Fin 5) : Module.Basis (Fin (rank i) → Bool) F (A F (D i)) :=
  homogeneousBinaryBasis (D i) (isTwoGroup i) (rank i) (directions i) (weight i)
    (weight_pos i) (directions_mem i) (spansLayers i) (two_pow_rank i)

theorem basis_weighted_span (i : Fin 5) (n : ℕ) :
    Submodule.span F {a | ∃ c, n≤JenningsCollection.binaryWeight (rank i) (weight i) c ∧
      a=augmentationBasis i c}=power F (D i) n := by
  simp only [augmentationBasis,homogeneousBinaryBasis_apply]
  exact binarySpan_eq_power_of_spansActualLayers (D i) (isTwoGroup i)
    (rank i) (directions i) (weight i) (weight_pos i) (directions_mem i) (spansLayers i) n

theorem hilbert_eq_weight_sum (i : Fin 5) :
    hilbertPolynomial (D i)=∑ c : Fin (rank i) → Bool,
      (Polynomial.monomial (JenningsCollection.binaryWeight (rank i) (weight i) c) 1 : ℕ[X]) :=
  hilbertPolynomial_eq_basisWeightSum (D i) (isTwoGroup i) (augmentationBasis i)
    (JenningsCollection.binaryWeight (rank i) (weight i)) (basis_weighted_span i)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem weight_sum_certificate : ∀ i : Fin 5,
    (∑ c : Fin (rank i) → Bool,
      (Polynomial.monomial (JenningsCollection.binaryWeight (rank i) (weight i) c) 1 : ℕ[X]))=
      (1+X)^2*(if i.val<2 then 1 else 1+X^2) := by
  intro i
  rw [binary_weight_sum_product]
  have h2 : (∏ j : Fin 2,(1+(X : ℕ[X])^(if j.val<2 then 1 else 2)))=(1+X)^2*1 := by
    simp [Fin.prod_univ_succ]
    ring
  have h3 : (∏ j : Fin 3,(1+(X : ℕ[X])^(if j.val<2 then 1 else 2)))=(1+X)^2*(1+X^2) := by
    simp [Fin.prod_univ_succ]
    ring
  fin_cases i
  · exact h2
  · exact h2
  · exact h3
  · exact h3
  · exact h3

theorem hilbertPolynomial_eq (i : Fin 5) :
    hilbertPolynomial (D i)=(1+X)^2*(if i.val<2 then 1 else 1+X^2) := by
  rw [hilbert_eq_weight_sum,weight_sum_certificate]

end UnitDistance.OddLocal
