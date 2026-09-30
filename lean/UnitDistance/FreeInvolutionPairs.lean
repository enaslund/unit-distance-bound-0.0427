module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option backward.privateInPublic true


/-! Canonical finite pairs for an actual fixed-point-free involution. -/
noncomputable section
namespace UnitDistance.FreeInvolution
variable {α : Type*} [Fintype α] (f : α → α)

/-- Choose the smaller point in each two-element orbit using a finite enumeration. -/
abbrev Representatives := {x : α // (Fintype.equivFin α x).val < (Fintype.equivFin α (f x)).val}

instance : Fintype (Representatives f) := Fintype.ofFinite _

def pair (p : Representatives f × Bool) : α := if p.2 then f p.1.1 else p.1.1

@[simp] theorem pair_false (x : Representatives f) : pair f (x,false) = x.1 := rfl
@[simp] theorem pair_true (x : Representatives f) : pair f (x,true) = f x.1 := rfl

theorem pair_injective (hf : Function.Involutive f) : Function.Injective (pair f) := by
  rintro ⟨x,b⟩ ⟨y,c⟩ h
  cases b <;> cases c
  · simpa only [pair_false, Subtype.val_inj, Prod.mk.injEq, and_true] using h
  · simp only [pair_false, pair_true] at h
    have hx := x.2
    have hy := y.2
    rw [h,hf] at hx
    omega
  · simp only [pair_false, pair_true] at h
    have hx := x.2
    have hy := y.2
    rw [← h,hf] at hy
    omega
  · simp only [pair_true] at h
    have he : x = y := Subtype.ext (hf.injective h)
    subst y
    rfl

theorem pair_surjective (hf : Function.Involutive f) (hn : ∀x, f x ≠ x) :
    Function.Surjective (pair f) := by
  intro x
  have hne : (Fintype.equivFin α x).val ≠ (Fintype.equivFin α (f x)).val := by
    intro h
    exact hn x ((Fintype.equivFin α).injective (Fin.ext h)).symm
  by_cases hlt : (Fintype.equivFin α x).val < (Fintype.equivFin α (f x)).val
  · exact ⟨(⟨x,hlt⟩,false),rfl⟩
  · have hlt' : (Fintype.equivFin α (f x)).val < (Fintype.equivFin α (f (f x))).val := by
      rw [hf]
      omega
    exact ⟨(⟨f x,hlt'⟩,true),hf x⟩

/-- The actual two-point orbit partition, with the second point obtained by `f`. -/
def pairEquiv (hf : Function.Involutive f) (hn : ∀x, f x ≠ x) :
    Representatives f × Bool ≃ α :=
  Equiv.ofBijective (pair f) ⟨pair_injective f hf,pair_surjective f hf hn⟩

theorem card_representatives_mul_two (hf : Function.Involutive f) (hn : ∀x, f x ≠ x) :
    Fintype.card (Representatives f) * 2 = Fintype.card α := by
  simpa using Fintype.card_congr (pairEquiv f hf hn)

end UnitDistance.FreeInvolution
