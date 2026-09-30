module

public import UnitDistance.CatalogSquareclassData

@[expose] public section
set_option backward.privateInPublic true


/-! Exact catalog-word expressions behind completed-field containment. -/
noncomputable section
namespace UnitDistance.CatalogCompletedContainmentData
open CatalogSquareclassData

def combinationIndices : Fin 7 → List (Fin 12) := ![[0,4],[0,2,4,7,8,9],[3,4,5,7],[0],[10],[0,2,3,4,5,7,10],[6]]

def combinationWords (j : Fin 7) : List ℕ :=
  (combinationIndices j).map retainedWords ++ if j=0 ∨ j=1 ∨ j=5 then [26] else []

/-- Each completed word is the exact binary sum of these retained words
and, where indicated, the independently proved square relation word26. -/
theorem combination_certificate (j : Fin 7) :
    (combinationWords j).foldr (· ^^^ ·) 0 = completedWords j := by
  have h : ∀ j : Fin 7,
      (combinationWords j).foldr (· ^^^ ·) 0 = completedWords j := by decide +kernel
  exact h j

 theorem mem_combinationWords (j : Fin 7) (m : ℕ) (hm : m ∈ combinationWords j) :
    (∃ k : Fin 12, m=retainedWords k) ∨ m=26 := by
  unfold combinationWords at hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨k,_,hk⟩ := List.mem_map.mp hm
    exact Or.inl ⟨k,hk.symm⟩
  · split at hm <;> simp_all

end UnitDistance.CatalogCompletedContainmentData
