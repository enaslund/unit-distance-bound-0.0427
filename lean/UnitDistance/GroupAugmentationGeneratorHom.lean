module

public import Mathlib.Algebra.Group.Subgroup.Lattice

@[expose] public section
set_option backward.privateInPublic true


/-! A map preserving right multiplication by actual group generators is a
homomorphism. This permits small Cayley-edge certificates for concrete maps. -/

namespace UnitDistance.GroupAugmentation
variable {G H ι : Type*} [Group G] [Group H]

/-- The elements whose right multiplication is preserved by the actual map. -/
def rightMultipliers (f : G → H) (h1 : f 1 = 1) : Subgroup G where
  carrier := {h | ∀ g, f (g*h) = f g*f h}
  one_mem' := by simp [h1]
  mul_mem' {h k} hh hk := by
    intro g
    rw [← mul_assoc,hk,hh,hk,mul_assoc]
  inv_mem' {h} hh := by
    intro g
    have hinv : f h⁻¹*f h = 1 := by rw [← hh]; simp [h1]
    apply mul_right_cancel (b := f h)
    rw [mul_assoc,hinv,mul_one,← hh]
    simp

/-- Only one certificate per right Cayley edge is needed. -/
def homOfRightGenerators (f : G → H) (h1 : f 1 = 1) (generators : ι → G)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (hstep : ∀ g i, f (g*generators i) = f g*f (generators i)) : G →* H where
  toFun := f
  map_one' := h1
  map_mul' g h := by
    have he : Subgroup.closure (Set.range generators) ≤ rightMultipliers f h1 := by
      apply (Subgroup.closure_le _).mpr
      rintro h ⟨i,rfl⟩ g
      exact hstep g i
    rw [hgen] at he
    exact he (Subgroup.mem_top h) g

end UnitDistance.GroupAugmentation
