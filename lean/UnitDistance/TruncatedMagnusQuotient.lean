module

public import UnitDistance.TruncatedMagnusGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! Actual normal quotients of the truncated tensor group. The quadratic
relations and their cubic tails are genuine elements; a linear annihilator
of their commutators determines a normal subgroup containing them. -/
noncomputable section
namespace UnitDistance.TruncatedMagnus
open Group
variable {R : Type*} [CommRing R]
variable {W : Type*} [AddCommGroup W] [Module R W]

def bracket (x : V₁ R) (y : V₂ R) : V₃ R :=
  fun i j k => x i*y j k-y i j*x k

variable (S : Submodule R (V₂ R)) (L : V₃ R →ₗ[R] W) (T : V₂ R →ₗ[R] W)

/-- The actual subgroup encoding quadratic relations with arbitrary compatible cubic tails. -/
def relationSubgroup : Subgroup (Group R) where
  carrier := {g | g.first=0 ∧ g.second∈S ∧ L g.third=T g.second}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨ha,has,hat⟩
    rcases hb with ⟨hb,hbs,hbt⟩
    have h2 : (a*b).second=a.second+b.second := by ext i j; simp [ha]
    have h3 : (a*b).third=a.third+b.third := by ext i j k; simp [ha,hb]
    exact ⟨by simp [ha,hb],by rw [h2]; exact S.add_mem has hbs,
      by rw [h2,h3,map_add,map_add,hat,hbt]⟩
  inv_mem' := by
    intro a ha
    rcases ha with ⟨ha,has,hat⟩
    have h2 : (a⁻¹).second= -a.second := by ext i j; simp [ha]
    have h3 : (a⁻¹).third= -a.third := by ext i j k; simp [ha]
    exact ⟨by simp [ha],by rw [h2]; exact S.neg_mem has,
      by rw [h2,h3,map_neg,map_neg,hat]⟩

@[simp] theorem mem_relationSubgroup (g : Group R) :
    g∈relationSubgroup S L T ↔ g.first=0 ∧ g.second∈S ∧ L g.third=T g.second := Iff.rfl

/-- Annihilation of the actual cubic brackets makes the displayed subgroup normal. -/
theorem relationSubgroup_normal
    (hL : ∀ (x : V₁ R) (y : V₂ R), y∈S → L (bracket x y)=0) :
    (relationSubgroup S L T).Normal := by
  constructor
  intro n hn g
  rcases hn with ⟨hn,hns,hnt⟩
  have he : n=(⟨0,n.second,n.third⟩ : Group R) := by ext <;> simp [hn]
  rw [he,conjugate_degreeTwo]
  have ht : (fun i j k => n.third i j k+g.first i*n.second j k-n.second i j*g.first k)=
      n.third+bracket g.first n.second := by
    ext i j k
    simp only [Pi.add_apply,bracket]
    ring
  change (0 : V₁ R)=0 ∧ n.second∈S ∧
    L (fun i j k => n.third i j k+g.first i*n.second j k-n.second i j*g.first k)=T n.second
  rw [ht]
  exact ⟨rfl,hns,by rw [map_add,hL _ _ hns,add_zero,hnt]⟩

@[simp] theorem central_mem_relationSubgroup (z : V₃ R) :
    (⟨0,0,z⟩ : Group R)∈relationSubgroup S L T ↔ L z=0 := by simp

/-- The cubic-tail condition is checked on actual elements, without dropping the tails. -/
theorem relation_mem (y : V₂ R) (z : V₃ R) (hy : y∈S) (hz : L z=T y) :
    (⟨0,y,z⟩ : Group R)∈relationSubgroup S L T := ⟨rfl,hy,hz⟩

end UnitDistance.TruncatedMagnus
