module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The order-32 dyadic normal-form group

This is the concrete group in Lemma `tw:new-local-two` of the manuscript.
It proves the finite group structure, normal forms, relations, and the
abstract inertia/residue sequence. Identification with a Galois group over
`ℚ₂`, ramification, different exponents, and local reciprocity are separate
arithmetic obligations and are not claimed here.
-/

namespace UnitDistance.Dyadic

/-- Reduction of the Frobenius coordinate modulo two. -/
def parity : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide) (ZMod 2)

/-- Coordinates of `xᵃ yᵇ zᶜ wᵈ`, with `w = [y,z]` central. -/
@[ext]
structure D where
  a : ZMod 2
  b : ZMod 2
  c : ZMod 4
  d : ZMod 2
  deriving DecidableEq, Fintype

namespace D

/-- The manuscript's normal-form product; the final coordinate contains the
commutator contribution from passing `zᶜ` through `yᴮ`. -/
def mul (g h : D) : D :=
  ⟨g.a + h.a, g.b + h.b, g.c + h.c,
    g.d + h.d + parity g.c * h.b⟩

def inv (g : D) : D :=
  ⟨-g.a, -g.b, -g.c, -g.d + parity g.c * g.b⟩

instance : Group D where
  mul := mul
  one := ⟨0, 0, 0, 0⟩
  inv := inv
  mul_assoc g h k := by
    change mul (mul g h) k = mul g (mul h k)
    ext <;> simp only [mul, map_add] <;> ring
  one_mul g := by
    change mul ⟨0, 0, 0, 0⟩ g = g
    ext <;> simp [mul]
  mul_one g := by
    change mul g ⟨0, 0, 0, 0⟩ = g
    ext <;> simp [mul]
  inv_mul_cancel g := by
    change mul (inv g) g = ⟨0, 0, 0, 0⟩
    ext <;> simp only [mul, inv, map_neg] <;> ring

theorem mul_coordinates (g h : D) :
    g * h = ⟨g.a + h.a, g.b + h.b, g.c + h.c,
      g.d + h.d + parity g.c * h.b⟩ := rfl

theorem card : Fintype.card D = 32 := by decide

/-- A concrete row/column index for exact group-algebra certificates. -/
def index (g : D) : Fin 32 :=
  ⟨16 * g.a.val + 8 * g.b.val + 2 * g.c.val + g.d.val, by
    have ha := ZMod.val_lt g.a
    have hb := ZMod.val_lt g.b
    have hc := ZMod.val_lt g.c
    have hd := ZMod.val_lt g.d
    omega⟩

def ofIndex (i : Fin 32) : D :=
  ⟨(i.val / 16 : ℕ), (i.val / 8 : ℕ), (i.val / 2 : ℕ), (i.val : ℕ)⟩

theorem ofIndex_index : ∀ g : D, ofIndex (index g) = g := by decide
theorem index_ofIndex : ∀ i : Fin 32, index (ofIndex i) = i := by decide

def indexEquiv : D ≃ Fin 32 where
  toFun := index
  invFun := ofIndex
  left_inv := ofIndex_index
  right_inv := index_ofIndex

/-- First central inertia generator. -/
def x : D := ⟨1, 0, 0, 0⟩
/-- Noncentral inertia generator. -/
def y : D := ⟨0, 1, 0, 0⟩
/-- Frobenius generator, of order four. -/
def z : D := ⟨0, 0, 1, 0⟩
/-- The central commutator coordinate. -/
def w : D := ⟨0, 0, 0, 1⟩

/-- Commutator convention used by the manuscript: `g⁻¹ h⁻¹ g h`. -/
def comm (g h : D) : D := g⁻¹ * h⁻¹ * g * h

theorem x_sq : x ^ 2 = 1 := by decide
theorem y_sq : y ^ 2 = 1 := by decide
theorem z_fourth : z ^ 4 = 1 := by decide
theorem z_sq_ne_one : z ^ 2 ≠ 1 := by decide
theorem w_sq : w ^ 2 = 1 := by decide
theorem comm_y_z : comm y z = w := by decide
theorem comm_x_y : comm x y = 1 := by decide
theorem comm_x_z : comm x z = 1 := by decide
theorem comm_w_z : comm w z = 1 := by decide
theorem x_central : ∀ g : D, x * g = g * x := by decide
theorem w_central : ∀ g : D, w * g = g * w := by decide
theorem y_z_noncommute : y * z ≠ z * y := by decide
theorem z_sq_ne_w : z ^ 2 ≠ w := by decide
theorem exponent_four : ∀ g : D, g ^ 4 = 1 := by decide
theorem inv_eq_cube : ∀ g : D, g⁻¹ = g ^ 3 := by decide

/-- Every coordinate tuple is the indicated word, with no existence input. -/
theorem normal_form : ∀ g : D,
    x ^ g.a.val * y ^ g.b.val * z ^ g.c.val * w ^ g.d.val = g := by
  decide

/-- The named three elements generate the entire concrete group. -/
theorem generators : Subgroup.closure ({x, y, z} : Set D) = ⊤ := by
  apply top_unique
  intro g _
  have hx : x ∈ Subgroup.closure ({x, y, z} : Set D) :=
    Subgroup.subset_closure (by simp)
  have hy : y ∈ Subgroup.closure ({x, y, z} : Set D) :=
    Subgroup.subset_closure (by simp)
  have hz : z ∈ Subgroup.closure ({x, y, z} : Set D) :=
    Subgroup.subset_closure (by simp)
  have hw : w ∈ Subgroup.closure ({x, y, z} : Set D) := by
    rw [← comm_y_z, comm]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) (Subgroup.inv_mem _ hz)) hy) hz
  rw [← normal_form g]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ hx _) (Subgroup.pow_mem _ hy _))
    (Subgroup.pow_mem _ hz _)) (Subgroup.pow_mem _ hw _)

/-- Projection onto the ordinary cyclic group of order four. -/
def residue : D →* Multiplicative (ZMod 4) where
  toFun g := Multiplicative.ofAdd g.c
  map_one' := rfl
  map_mul' _ _ := rfl

theorem residue_surjective : Function.Surjective residue := by
  intro c
  exact ⟨⟨0, 0, c.toAdd, 0⟩, rfl⟩

/-- Abstract inertia is the kernel of the Frobenius-coordinate projection. -/
def inertia : Subgroup D := residue.ker

@[simp]
theorem mem_inertia (g : D) : g ∈ inertia ↔ g.c = 0 := Iff.rfl

instance : DecidablePred (· ∈ inertia) :=
  fun g => inferInstanceAs (Decidable (g.c = 0))

theorem inertia_card : Fintype.card inertia = 8 := by decide

/-- The concrete inertia subgroup is elementary abelian of exponent two. -/
theorem inertia_square : ∀ g : inertia, (g : D) ^ 2 = 1 := by decide

theorem inertia_commutative : ∀ g h : inertia, (g : D) * h = (h : D) * g := by
  decide

theorem inertia_generators : Subgroup.closure ({x, y, w} : Set D) = inertia := by
  apply le_antisymm
  · apply (Subgroup.closure_le inertia).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl <;> rfl
  · intro g hg
    have hx : x ∈ Subgroup.closure ({x, y, w} : Set D) :=
      Subgroup.subset_closure (by simp)
    have hy : y ∈ Subgroup.closure ({x, y, w} : Set D) :=
      Subgroup.subset_closure (by simp)
    have hw : w ∈ Subgroup.closure ({x, y, w} : Set D) :=
      Subgroup.subset_closure (by simp)
    have hc : g.c = 0 := (mem_inertia g).mp hg
    rw [← normal_form g]
    simp only [hc, ZMod.val_zero, pow_zero, mul_one]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hx _) (Subgroup.pow_mem _ hy _))
      (Subgroup.pow_mem _ hw _)

end D
end UnitDistance.Dyadic
