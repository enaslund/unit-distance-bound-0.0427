module

public import UnitDistance.DyadicGroup
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Coset.Card

@[expose] public section
set_option backward.privateInPublic true


/-! The actual abelianization of the explicit dyadic group. -/
noncomputable section
namespace UnitDistance.Dyadic.D
abbrev AbelianCoordinates := Multiplicative (ZMod 2 × ZMod 2 × ZMod 4)

def abelianProjection : D →* AbelianCoordinates where
  toFun g := Multiplicative.ofAdd (g.a,g.b,g.c)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem abelianProjection_surjective : Function.Surjective abelianProjection := by
  intro v
  exact ⟨⟨v.toAdd.1,v.toAdd.2.1,v.toAdd.2.2,0⟩,rfl⟩

theorem commutator_eq_ker : _root_.commutator D=abelianProjection.ker := by
  apply le_antisymm (Abelianization.commutator_subset_ker _)
  intro g hg
  have hc : g=1 ∨ g=w := by
    have h : ∀ g : D,abelianProjection g=1 → g=1 ∨ g=w := by decide +kernel
    exact h g hg
  rcases hc with rfl | rfl
  · exact Subgroup.one_mem _
  · rw [_root_.commutator_eq_closure]
    apply Subgroup.subset_closure
    exact ⟨y,z,by decide⟩

/-- The C4 factor survives in the abelianization; its order is sixteen. -/
theorem abelianization_card : Nat.card (Abelianization D)=16 := by
  change Nat.card (D ⧸ _root_.commutator D)=16
  rw [commutator_eq_ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective abelianProjection
      abelianProjection_surjective).toEquiv]
  simp [AbelianCoordinates,Nat.card_eq_fintype_card]

end UnitDistance.Dyadic.D
