module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Pi
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Abel
public import Mathlib.SetTheory.Cardinal.NatCard

@[expose] public section
set_option backward.privateInPublic true


/-! The genuine degree-three truncated Magnus group. Its coordinates are
coefficients of words of lengths one, two and three; multiplication is
literal truncated noncommutative multiplication. -/
noncomputable section
namespace UnitDistance.TruncatedMagnus
variable (R : Type*) [CommRing R]
abbrev V₁ := Fin 7 → R
abbrev V₂ := Fin 7 → Fin 7 → R
abbrev V₃ := Fin 7 → Fin 7 → Fin 7 → R

@[ext] structure Group where
  first : V₁ R
  second : V₂ R
  third : V₃ R
  deriving DecidableEq

namespace Group
variable {R}

def mul (g h : Group R) : Group R :=
  ⟨g.first+h.first,
   fun i j => g.second i j+h.second i j+g.first i*h.first j,
   fun i j k => g.third i j k+h.third i j k+
     g.first i*h.second j k+g.second i j*h.first k⟩

def inv (g : Group R) : Group R :=
  ⟨-g.first,
   fun i j => -g.second i j+g.first i*g.first j,
   fun i j k => -g.third i j k+g.first i*g.second j k+
     g.second i j*g.first k-g.first i*g.first j*g.first k⟩

instance : _root_.Group (Group R) where
  one := ⟨0,0,0⟩
  mul := mul
  inv := inv
  mul_assoc g h k := by
    change mul (mul g h) k=mul g (mul h k)
    ext <;> simp [mul] <;> ring
  one_mul g := by
    change mul ⟨0,0,0⟩ g=g
    ext <;> simp [mul]
  mul_one g := by
    change mul g ⟨0,0,0⟩=g
    ext <;> simp [mul]
  inv_mul_cancel g := by
    change mul (inv g) g=⟨0,0,0⟩
    ext <;> simp [mul,inv] <;> ring

@[simp] theorem one_first : (1 : Group R).first=0 := rfl
@[simp] theorem one_second : (1 : Group R).second=0 := rfl
@[simp] theorem one_third : (1 : Group R).third=0 := rfl
@[simp] theorem mul_first (g h : Group R) : (g*h).first=g.first+h.first := rfl
@[simp] theorem mul_second (g h : Group R) (i j : Fin 7) :
    (g*h).second i j=g.second i j+h.second i j+g.first i*h.first j := rfl
@[simp] theorem mul_third (g h : Group R) (i j k : Fin 7) :
    (g*h).third i j k=g.third i j k+h.third i j k+
      g.first i*h.second j k+g.second i j*h.first k := rfl
@[simp] theorem inv_first (g : Group R) : (g⁻¹).first= -g.first := rfl
@[simp] theorem inv_second (g : Group R) (i j : Fin 7) :
    (g⁻¹).second i j= -g.second i j+g.first i*g.first j := rfl
@[simp] theorem inv_third (g : Group R) (i j k : Fin 7) :
    (g⁻¹).third i j k= -g.third i j k+g.first i*g.second j k+
      g.second i j*g.first k-g.first i*g.first j*g.first k := rfl

def equivProd : Group R ≃ V₁ R × V₂ R × V₃ R where
  toFun g := (g.first,g.second,g.third)
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite R] : Finite (Group R) := Finite.of_equiv _ equivProd.symm

def firstHom : Group R →* Multiplicative (V₁ R) where
  toFun g := Multiplicative.ofAdd g.first
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Actual pure degree-two and degree-three elements add componentwise. -/
def degreeTwoHom : Multiplicative (V₂ R × V₃ R) →* Group R where
  toFun w := ⟨0,w.toAdd.1,w.toAdd.2⟩
  map_one' := rfl
  map_mul' g h := by ext <;> simp

/-- Actual degree-three elements are central. -/
def centralHom : Multiplicative (V₃ R) →* Group R where
  toFun z := ⟨0,0,z.toAdd⟩
  map_one' := rfl
  map_mul' g h := by ext <;> simp

theorem centralHom_central (z : Multiplicative (V₃ R)) (g : Group R) :
    Commute (centralHom z) g := by
  change centralHom z*g=g*centralHom z
  ext <;> simp [centralHom,add_comm]

/-- Conjugation of degree-two elements is the literal cubic bracket. -/
theorem conjugate_degreeTwo (g : Group R) (y : V₂ R) (z : V₃ R) :
    g*(⟨0,y,z⟩ : Group R)*g⁻¹ =
      (⟨0,y,fun i j k => z i j k+g.first i*y j k-y i j*g.first k⟩ : Group R) := by
  ext <;> simp <;> ring

/-- The quadratic component of an actual commutator is its alternating tensor. -/
theorem commutator_second (g h : Group R) (i j : Fin 7) :
    (g*h*g⁻¹*h⁻¹).second i j=g.first i*h.first j-h.first i*g.first j := by
  simp
  ring

@[simp] theorem commutator_first (g h : Group R) :
    (g*h*g⁻¹*h⁻¹).first=0 := by simp

end Group

/-- The actual tensor group is finite of the coordinate-counted order. -/
theorem card_binaryGroup : Nat.card (Group (ZMod 2))=2^399 := by
  rw [Nat.card_congr Group.equivProd,Nat.card_prod,Nat.card_prod]
  simp only [V₁,V₂,V₃,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  norm_num
  decide +kernel

/-- In particular the concrete cubic detector is an actual finite 2-group. -/
theorem binaryGroup_isTwoGroup : IsPGroup 2 (Group (ZMod 2)) :=
  IsPGroup.of_card card_binaryGroup

end UnitDistance.TruncatedMagnus
