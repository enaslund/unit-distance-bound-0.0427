module

public import UnitDistance.CatalogSquareclassData

@[expose] public section
set_option backward.privateInPublic true


/-! Kernel-checked independence of the seven completed catalog word forms. -/
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
open scoped BigOperators
namespace UnitDistance.CatalogCompletedSquareclassData
open CatalogSquareclassData
/-- Actual evaluations of the retained catalog signs. -/
def completedEvaluation (k : Fin 21) (j : Fin 7) : F :=
  wordForm (completedWords j) (pairVector k)

/-- Compact independently checked values of those actual evaluations. -/
def evaluationMasks : Fin 21 → ℕ := ![37,98,21,14,96,8,0,3,64,101,102,32,32,66,2,42,54,9,110,4,107]

/-- Coefficients of an explicit left inverse. -/
def inverseMasks : Fin 7 → ℕ := ![146,18,58,32,172,169,185]

def inverseCoefficient (j : Fin 7) (k : Fin 21) : F :=
  if (inverseMasks j).testBit k.val then 1 else 0

/-- The small matrix is checked against the independently defined root-character calculation. -/
theorem evaluation_certificate (k : Fin 21) (j : Fin 7) :
    completedEvaluation k j = if (evaluationMasks k).testBit j.val then 1 else 0 := by
  simp only [completedEvaluation,wordForm,catalog_evaluation_certificate]
  have h : ∀ k : Fin 21, ∀ j : Fin 7,
      (∑ i : Fin 17, if (completedWords j).testBit i.val then
        (if (catalogEvaluationMasks k).testBit i.val then 1 else 0) else 0 : F) =
        if (evaluationMasks k).testBit j.val then 1 else 0 := by
    decide +kernel
  exact h k j

/-- The explicit matrix is a left inverse of the actual sign evaluations. -/
theorem inverse_certificate (i j : Fin 7) :
    (∑ k : Fin 21, inverseCoefficient i k * completedEvaluation k j) = if i = j then 1 else 0 := by
  simp_rw [evaluation_certificate]
  have h : ∀ i j : Fin 7,
      (∑ k : Fin 21, inverseCoefficient i k *
        (if (evaluationMasks k).testBit j.val then 1 else 0)) = if i = j then 1 else 0 := by
    decide +kernel
  exact h i j

attribute [local irreducible] completedEvaluation inverseCoefficient
set_option maxHeartbeats 400000

/-- The actual finite evaluation map of linear combinations of catalog forms. -/
def evaluationMap : (Fin 7 → F) →ₗ[F] (Fin 21 → F) :=
  Matrix.toLin' (Matrix.of completedEvaluation)

/-- The explicit reverse coordinate map. -/
def inverseMap : (Fin 21 → F) →ₗ[F] (Fin 7 → F) :=
  Matrix.toLin' (Matrix.of inverseCoefficient)

/-- Actual linear independence of the seven evaluated catalog forms. -/
theorem inverseMap_leftInverse : Function.LeftInverse inverseMap evaluationMap := by
  have he : Matrix.of inverseCoefficient * Matrix.of completedEvaluation = (1 : Matrix (Fin 7) (Fin 7) F) := by
    ext i j
    simpa only [Matrix.mul_apply,Matrix.one_apply,Matrix.of_apply] using inverse_certificate i j
  intro v
  change (Matrix.toLin' (Matrix.of inverseCoefficient)) ((Matrix.toLin' (Matrix.of completedEvaluation)) v) = v
  rw [← Matrix.toLin'_mul_apply,he,Matrix.toLin'_one,LinearMap.id_apply]

theorem evaluationMap_injective : Function.Injective evaluationMap :=
  inverseMap_leftInverse.injective

/-- Every nonzero combination has a nontrivial actual sign on a specified
pair vector; this is the exact certificate needed for Kummer nonsquareness. -/
theorem exists_nonzero_evaluation (v : Fin 7 → F) (hv : v ≠ 0) :
    ∃ k : Fin 21, (∑ j : Fin 7, completedEvaluation k j*v j) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hv
  apply evaluationMap_injective
  ext k
  simpa only [evaluationMap,Matrix.toLin'_apply,Matrix.of_apply,Matrix.mulVec,dotProduct,LinearMap.map_zero,Pi.zero_apply] using h k

end UnitDistance.CatalogCompletedSquareclassData
