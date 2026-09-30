module

public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section
set_option backward.privateInPublic true


/-! Finite word and generation information transfers between actual group
homomorphisms when their kernels are nested. -/
namespace UnitDistance.HomKernelTransfer
variable {G A B : Type*} [Group G] [Group A] [Group B]
  (f : G →* A) (g : G →* B) (h : f.ker≤g.ker)
include h

theorem eq_of_eq {x y : G} (he : f x=f y) : g x=g y := by
  have hm : x⁻¹*y∈f.ker := by simp only [MonoidHom.mem_ker,map_mul,map_inv,he,inv_mul_cancel]
  have hn := h hm
  have hn' : (g x)⁻¹*g y=1 := by simpa only [MonoidHom.mem_ker,map_mul,map_inv] using hn
  exact inv_mul_eq_one.mp hn'

/-- Generation by a specified set descends along a kernel inclusion. -/
theorem mem_closure_image {S : Set G} {x : G}
    (hx : f x∈Subgroup.closure (f '' S)) :
    g x∈Subgroup.closure (g '' S) := by
  rw [←MonoidHom.map_closure] at hx ⊢
  obtain ⟨y,hy,hfy⟩ := hx
  exact ⟨y,hy,eq_of_eq f g h hfy⟩

/-- The same transfer for a chosen cyclic generator. -/
theorem eq_zpow_of_eq_zpow {x t : G} {n : ℤ} (hx : f x=(f t)^n) :
    g x=(g t)^n := by
  rw [←map_zpow] at hx ⊢
  exact eq_of_eq f g h hx

end UnitDistance.HomKernelTransfer
