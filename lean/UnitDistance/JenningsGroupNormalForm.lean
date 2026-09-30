module

public import UnitDistance.JenningsLayerNormalForm

@[expose] public section
set_option backward.privateInPublic true


/-!
# Ordered group normal forms along the complete binary dimension filtration

The one-layer factorization is iterated through the actual filtration. Its
termination is proved by finite 2-group augmentation nilpotence, so every
finite 2-group receives a genuine bijection from finite binary layer
coordinates to group elements. The coordinate map consists of ordered
products of lifted homogeneous group directions. No ambient PBW or desired
Hilbert polynomial is assumed.
-/

noncomputable section
universe u
namespace UnitDistance.GroupAugmentation
variable (G : Type u) [Group G] [Finite G]

/-- The actual positive layer, with a zero-based index for recursion. -/
def BinaryLayer (i : ℕ) : Type u := by
  letI : Fact (1 ≤ i+1) := ⟨Nat.succ_le_succ (Nat.zero_le i)⟩
  exact LayerVector G (i+1)

/-- A finite tuple of binary layer coordinates. Its terminal factor is a
singleton, not an assumed unknown residual subgroup. -/
def NormalCoordinates (start : ℕ) : ℕ → Type u
  | 0 => PUnit
  | length+1 => BinaryLayer G start × NormalCoordinates (start+1) length

/-- Iterating the actual ordered section yields a genuine unique normal
form whenever the terminal actual dimension subgroup is trivial. -/
def normalCoordinatesEquiv (length start : ℕ)
    (hend : dimensionSubgroup (ZMod 2) G (start+length+1) = ⊥) :
    NormalCoordinates G start length ≃ dimensionSubgroup (ZMod 2) G (start+1) := by
  induction length generalizing start with
  | zero =>
    have he : dimensionSubgroup (ZMod 2) G (start+1) = ⊥ := by simpa using hend
    letI : Subsingleton (dimensionSubgroup (ZMod 2) G (start+1)) := by
      rw [he]
      infer_instance
    change PUnit ≃ dimensionSubgroup (ZMod 2) G (start+1)
    exact
      { toFun := fun _ => 1
        invFun := fun _ => PUnit.unit
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
  | succ length ih =>
    letI : Fact (1 ≤ start+1) := ⟨Nat.succ_le_succ (Nat.zero_le start)⟩
    have htail : dimensionSubgroup (ZMod 2) G ((start+1)+length+1) = ⊥ := by
      have he : (start+1)+length+1 = start+(length+1)+1 := by omega
      rw [he]
      exact hend
    change BinaryLayer G start × NormalCoordinates G (start+1) length ≃ _
    exact (Equiv.prodCongr (Equiv.refl _) (ih (start+1) htail)).trans
      (orderedLayerCoordinatesNext G (start+1))

/-- The degree-one dimension subgroup is canonically the entire group. -/
def dimensionOneEquiv : dimensionSubgroup (ZMod 2) G 1 ≃ G where
  toFun := Subtype.val
  invFun g := ⟨g, by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Unconditional ordered group normal forms for every finite 2-group,
using the actual augmentation dimension filtration and actual lifted bases. -/
def groupNormalForm (hG : IsPGroup 2 G) :
    NormalCoordinates G 0 (Nat.card G) ≃ G :=
  (normalCoordinatesEquiv G (Nat.card G) 0
    (by simpa only [Nat.zero_add] using
      dimensionSubgroup_eq_bot_of_card_le G 2 hG (Nat.card G+1) (Nat.le_succ _))).trans
    (dimensionOneEquiv G)

/-- Every group element is represented, uniquely, by these actual ordered
binary-layer products. -/
theorem groupNormalForm_bijective (hG : IsPGroup 2 G) :
    Function.Bijective (groupNormalForm G hG) := (groupNormalForm G hG).bijective

end UnitDistance.GroupAugmentation
