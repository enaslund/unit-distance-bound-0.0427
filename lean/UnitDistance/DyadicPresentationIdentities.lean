module

public import UnitDistance.ClassTwoCollectionDiagonal
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice

@[expose] public section
set_option backward.privateInPublic true


/-! Group identities forced by the seven literal dyadic relators. -/
noncomputable section
namespace UnitDistance.Dyadic.Presentation
variable {G : Type*} [Group G]

def comm (y z : G) : G := y⁻¹*z⁻¹*y*z

variable (x y z : G) (hx : x^2=1) (hy : y^2=1) (hz : z^4=1)
  (hxy : Commute x y) (hxz : Commute x z)
  (hw : comm y z^2=1) (hwz : Commute (comm y z) z)

include hy in
theorem y_inv : y⁻¹=y := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hy)
include hw in
theorem w_inv : (comm y z)⁻¹=comm y z :=
  inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hw)

include hw in
theorem zy_swap : z*y=y*z*comm y z := by
  calc
    z*y=(y*z)*(comm y z)⁻¹ := by dsimp [comm]; group
    _ = _ := by rw [w_inv y z hw]

include hy hw in
theorem w_commute_y : Commute (comm y z) y := by
  change comm y z*y=y*comm y z
  calc
    comm y z*y=y*(comm y z)⁻¹ := by
      simp only [comm,mul_inv_rev,inv_inv,y_inv y hy,mul_assoc]
    _ = _ := by rw [w_inv y z hw]

include hxy hxz in
theorem w_commute_x : Commute (comm y z) x :=
  (((hxy.inv_right.mul_right hxz.inv_right).mul_right hxy).mul_right hxz).symm

include hw hwz in
theorem z_square_commute_y : Commute (z^2) y := by
  change z^2*y=y*z^2
  have hww : comm y z*comm y z=1 := by simpa only [pow_two] using hw
  calc
    z^2*y=z*(z*y) := by simp only [pow_two,mul_assoc]
    _ = z*(y*z*comm y z) := by rw [zy_swap y z hw]
    _ = (z*y)*z*comm y z := by group
    _ = (y*z*comm y z)*z*comm y z := by rw [zy_swap y z hw]
    _ = y*z*(comm y z*z)*comm y z := by group
    _ = y*z*(z*comm y z)*comm y z := by rw [hwz.eq]
    _ = y*z^2 := by simp only [mul_assoc,hww,mul_one,pow_two]

include hy hw hwz in
theorem yz_square : (y*z)^2=comm y z*z^2 := by
  have hyy : y*y=1 := by simpa only [pow_two] using hy
  calc
    (y*z)^2=y*(z*y)*z := by simp only [pow_two,mul_assoc]
    _ = y*(y*z*comm y z)*z := by rw [zy_swap y z hw]
    _ = (y*y)*z*(comm y z*z) := by group
    _ = comm y z*z^2 := by
      rw [hyy,one_mul,hwz.eq]
      simpa only [pow_two,mul_assoc] using (hwz.pow_right 2).symm.eq

include hy hw hwz in
theorem y_yz_swap : y*(y*z)=comm y z*(y*z)*y := by
  have hyy : y*y=1 := by simpa only [pow_two] using hy
  have hww : comm y z*comm y z=1 := by simpa only [pow_two] using hw
  symm
  calc
    comm y z*(y*z)*y=comm y z*y*(z*y) := by group
    _ = comm y z*y*(y*z*comm y z) := by rw [zy_swap y z hw]
    _ = comm y z*(y*y)*z*comm y z := by group
    _ = z := by rw [hyy,mul_one,hwz.eq]; simp only [mul_assoc,hww,mul_one]
    _ = y*(y*z) := by rw [←mul_assoc,hyy,one_mul]

section Topology
variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem central_of_generator_commutes
    (hgen : (Subgroup.closure ({x,y,z}:Set G)).topologicalClosure=⊤)
    (a : G) (ha : Commute a x ∧ Commute a y ∧ Commute a z) : ∀g,Commute a g := by
  have hs : Subgroup.closure ({x,y,z}:Set G)≤Subgroup.centralizer {a} := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr ha.1.symm.eq
    · exact Subgroup.mem_centralizer_singleton_iff.mpr ha.2.1.symm.eq
    · exact Subgroup.mem_centralizer_singleton_iff.mpr ha.2.2.symm.eq
  have hc := Subgroup.topologicalClosure_minimal _ hs (Set.isClosed_centralizer ({a}:Set G))
  rw [hgen] at hc
  intro g
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hc (Subgroup.mem_top g))).symm

end Topology
end UnitDistance.Dyadic.Presentation
