module

public import UnitDistance.ArithmeticCatalogRadicands
public import UnitDistance.CatalogCompletedSquareclassData

@[expose] public section
set_option backward.privateInPublic true


/-!
# Independence of actual completed squareclasses

The seven radicands are actual elements of the constructed genus field.
Every nonempty binary product has an actual involution whose lift multiplier
has twisted norm minus one. Thus its nonsquareness follows from a field
identity and the independently checked sign matrix.
-/

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace UnitDistance.ArithmeticCompleted
open ArithmeticChosenGenus ArithmeticCatalog Multiquadratic
abbrev F := ZMod 2

/-- The seven actual completed radicands. -/
def completedRadicand (j : Fin 7) : GenusField :=
  wordRadicand (CatalogSquareclassData.completedWords j)

theorem completedRadicand_ne_zero (j : Fin 7) : completedRadicand j ≠ 0 :=
  wordRadicand_ne_zero _

/-- An actual product selected by a binary coefficient vector. -/
def selectedRadicand (v : Fin 7 → F) : GenusField :=
  ∏ j : Fin 7, if v j = 0 then 1 else completedRadicand j

theorem selectedRadicand_ne_zero (v : Fin 7 → F) : selectedRadicand v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  split
  · exact one_ne_zero
  · exact completedRadicand_ne_zero j

/-- The actual multiplier for the selected radicand product. -/
def selectedMultiplier (v : Fin 7 → F) (w : Fin 7 → F) : GenusField :=
  ∏ j : Fin 7, if v j = 0 then 1 else
    wordMultiplier (CatalogSquareclassData.completedWords j) w

theorem selectedMultiplier_twist (v : Fin 7 → F) (w : Fin 7 → F) :
    selectedRadicand v*(selectedMultiplier v w)^2 =
      signAutomorphism w (selectedRadicand v) := by
  unfold selectedRadicand selectedMultiplier
  rw [map_prod,← Finset.prod_pow,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  split
  · simp
  · exact wordMultiplier_twist _ _

theorem binary_select_mul (x y : F) : (if x = 0 then 0 else y) = y*x := by
  have h : ∀ x y : F, (if x = 0 then 0 else y) = y*x := by decide +kernel
  exact h x y

/-- The true twisted norm agrees with the checked binary evaluation. -/
theorem selectedMultiplier_twisted_norm (v : Fin 7 → F) (w : Fin 7 → F) :
    selectedMultiplier v w*signAutomorphism w (selectedMultiplier v w) =
      binarySign (∑ j : Fin 7,
        CatalogSquareclassData.wordForm (CatalogSquareclassData.completedWords j) w * v j) := by
  unfold selectedMultiplier
  rw [map_prod,← Finset.prod_mul_distrib,binarySign_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [← binary_select_mul]
  split
  · simp
  · exact wordMultiplier_twisted_norm _ _

/-- Every nonzero combination of the seven actual completed squareclasses
is nonsquare in the actual genus field. -/
theorem completed_squareclasses_independent (v : Fin 7 → F) (hv : v ≠ 0) :
    KummerInvariant.Nonsquare (selectedRadicand v) := by
  obtain ⟨k,hk⟩ := CatalogCompletedSquareclassData.exists_nonzero_evaluation v hv
  let w := CatalogSquareclassData.pairVector k
  apply KummerInvariant.nonsquare_of_twisted_norm (signAutomorphism w)
    (signAutomorphism_involutive w) (selectedRadicand v) (selectedMultiplier v w)
    (selectedRadicand_ne_zero v) (selectedMultiplier_twist v w)
  rw [selectedMultiplier_twisted_norm]
  intro h
  apply hk
  apply binarySign_injective (E := GenusField)
  simpa [CatalogCompletedSquareclassData.completedEvaluation,w] using h

/-- The completed radicands are invariant squareclasses under every actual
automorphism of the actual genus field. -/
theorem completedRadicand_invariant (j : Fin 7) (σ : Gal(GenusField/ℚ)) :
    ∃ u : GenusField, completedRadicand j*u^2 = σ (completedRadicand j) :=
  wordRadicand_invariant _ σ

/-- The equivalent finite-subset formulation applies directly to the
actual quadratic-tower construction. -/
theorem completed_products_not_isSquare (s : Finset (Fin 7)) (hs : s.Nonempty) :
    ¬IsSquare (∏ j ∈ s, completedRadicand j) := by
  let v : Fin 7 → F := fun j => if j ∈ s then 1 else 0
  have hv : v ≠ 0 := by
    obtain ⟨j,hj⟩ := hs
    intro h
    have hh := congrFun h j
    simpa [v,hj] using hh
  have he : selectedRadicand v = ∏ j ∈ s, completedRadicand j := by
    unfold selectedRadicand
    calc
      (∏ j : Fin 7, if v j = 0 then 1 else completedRadicand j) =
          ∏ j ∈ s, if v j = 0 then 1 else completedRadicand j := by
        symm
        apply Finset.prod_subset (Finset.subset_univ s)
        intro j _ hj
        simp [v,hj]
      _ = _ := Finset.prod_congr rfl fun j hj => by simp [v,hj]
  intro h
  obtain ⟨x,hx⟩ := h
  apply completed_squareclasses_independent v hv x
  simpa [he,pow_two] using hx.symm

end UnitDistance.ArithmeticCompleted
