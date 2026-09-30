module

public import UnitDistance.GroupAugmentation
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.NoncommRing

@[expose] public section
set_option backward.privateInPublic true


/-! Actual augmentation degrees of the literal power and commutator words
used by the cut presentation. These hold for arbitrary groups, finite or not. -/
noncomputable section
namespace UnitDistance.GroupAugmentation
variable (R G : Type*) [CommRing R] [Group G]

/-- Commutators add actual augmentation degrees. -/
theorem commutator_mem_dimension_add {m n : ℕ} (g h : G)
    (hg : g∈dimensionSubgroup R G m) (hh : h∈dimensionSubgroup R G n) :
    g⁻¹*h⁻¹*g*h∈dimensionSubgroup R G (m+n) := by
  change delta R (g⁻¹*h⁻¹*g*h)-1∈power R G (m+n)
  have he : delta R (g⁻¹*h⁻¹*g*h)-1=
      delta R g⁻¹*delta R h⁻¹*
        ((delta R g-1)*(delta R h-1)-(delta R h-1)*(delta R g-1)) := by
    have hd : (delta R g-1)*(delta R h-1)-(delta R h-1)*(delta R g-1)=
        delta R g*delta R h-delta R h*delta R g := by noncomm_ring
    rw [hd]
    simp [mul_sub,mul_assoc]
  rw [he]
  apply mul_mem_left R G (m+n)
  exact (power R G (m+n)).sub_mem (mul_mem_add R G hg hh)
    (by simpa only [Nat.add_comm] using mul_mem_add R G hh hg)

/-- In characteristic two, squaring doubles the actual augmentation degree. -/
theorem square_mem_dimension_double [CharP R 2] {n : ℕ} (g : G)
    (hg : g∈dimensionSubgroup R G n) : g^2∈dimensionSubgroup R G (n+n) := by
  have hadd (a : A R G) : a+a=0 := by
    rw [← two_smul R,CharTwo.two_eq_zero,zero_smul]
  have hneg (a : A R G) : -a=a := neg_eq_iff_add_eq_zero.mpr (hadd a)
  have he : delta R (g^2)-1=(delta R g-1)*(delta R g-1) := by
    simp only [pow_two,sub_eq_add_neg,hneg,mul_add,add_mul,mul_one,one_mul]
    rw [← delta_mul]
    have hz : delta R g+delta R g=0 := hadd _
    calc
      delta R g*delta R g+1 = delta R g*delta R g+(delta R g+delta R g)+1 := by rw [hz,add_zero]
      _ = _ := by abel
  change delta R (g^2)-1∈power R G (n+n)
  rw [he]
  exact mul_mem_add R G hg hg

theorem fourth_pow_mem_dimension_four [CharP R 2] (g : G) :
    g^4∈dimensionSubgroup R G 4 := by
  have h1 : g∈dimensionSubgroup R G 1 := by rw [dimensionSubgroup_one]; trivial
  have h2 : g^2∈dimensionSubgroup R G 2 := square_mem_dimension_double R G g h1
  have h4 : (g^2)^2∈dimensionSubgroup R G 4 := square_mem_dimension_double R G (g^2) h2
  simpa only [← pow_mul] using h4

theorem commutator_mem_dimension_two (g h : G) :
    g⁻¹*h⁻¹*g*h∈dimensionSubgroup R G 2 := by
  apply commutator_mem_dimension_add R G (m := 1) (n := 1)
  all_goals rw [dimensionSubgroup_one]; trivial

theorem commutator_square_mem_dimension_four [CharP R 2] (g h : G) :
    (g⁻¹*h⁻¹*g*h)^2∈dimensionSubgroup R G 4 :=
  square_mem_dimension_double R G _ (commutator_mem_dimension_two R G g h)

theorem nested_commutator_mem_dimension_three (g h : G) :
    (g⁻¹*h⁻¹*g*h)⁻¹*h⁻¹*(g⁻¹*h⁻¹*g*h)*h∈dimensionSubgroup R G 3 := by
  apply commutator_mem_dimension_add R G (m := 2) (n := 1)
  · exact commutator_mem_dimension_two R G g h
  · rw [dimensionSubgroup_one]; trivial

end UnitDistance.GroupAugmentation
