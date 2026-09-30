module

public import UnitDistance.NormExtensionCatalog
public import UnitDistance.QuadraticSignLift
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section
set_option backward.privateInPublic true


/-!
# Independently computed catalog squareclass data

The characters are evaluated from the actual rational square-root masks.
The twelve retained catalog words are proved independent by a checked left
inverse of their evaluations on twenty-one actual binary vectors.
-/

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
open scoped BigOperators
namespace UnitDistance.CatalogSquareclassData
abbrev F := ZMod 2

/-- The rational genus radicands, in their fixed coordinate order. -/
def radicands : Fin 7 → ℚ := ![-1,2,3,5,7,11,13]

/-- Masks specifying the actual catalog A square roots. -/
def masksA : Fin 17 → ℕ := ![1,41,3,41,41,17,11,34,69,25,97,5,67,7,19,33,1]

/-- Masks specifying the actual catalog B square roots. -/
def masksB : Fin 17 → ℕ := ![72,80,36,18,66,2,112,84,40,100,22,64,28,56,72,8,64]

/-- The independently specified binary root character. -/
def character (m : ℕ) (v : Fin 7 → F) : F :=
  ∑ j : Fin 7, if m.testBit j.val then v j else 0

/-- The actual quadratic sign attached to one norm row. -/
def catalogForm (i : Fin 17) (v : Fin 7 → F) : F :=
  character (masksA i) v * character (masksB i) v

/-- Quadratic sign of the displayed product of norm rows. -/
def wordForm (m : ℕ) (v : Fin 7 → F) : F :=
  ∑ i : Fin 17, if m.testBit i.val then catalogForm i v else 0

/-- The seven raw words defining the completed retained field N. -/
def completedWords : Fin 7 → ℕ := ![17,27184,6220,2,32768,39508,132]

/-- The twelve raw words defining the full quadratic retained field M. -/
def retainedWords : Fin 12 → ℕ := ![2,256,512,4096,9,65,132,2052,24576,37,32768,65536]

/-- Every pair of distinct genus coordinates, in lexicographic order. -/
def pairs : Fin 21 → Fin 7 × Fin 7 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]

/-- The actual binary vector with ones at the two selected coordinates. -/
def pairVector (k : Fin 21) : Fin 7 → F :=
  fun j => if j = (pairs k).1 ∨ j = (pairs k).2 then 1 else 0

/-- Only the two supported coordinates contribute to a root character. -/
theorem character_pairVector (m : ℕ) (k : Fin 21) :
    character m (pairVector k) =
      (if m.testBit (pairs k).1.val then 1 else 0) +
      (if m.testBit (pairs k).2.val then 1 else 0) := by
  have hne : (pairs k).1 ≠ (pairs k).2 := by
    have h : ∀ k : Fin 21, (pairs k).1 ≠ (pairs k).2 := by decide +kernel
    exact h k
  unfold character
  rw [Fintype.sum_eq_add (pairs k).1 (pairs k).2 hne (by
    intro j hj
    simp [pairVector,hj.1,hj.2])]
  simp [pairVector]


/-- Evaluations of the seventeen individual catalog forms on the pair vectors. -/
def catalogEvaluationMasks : Fin 21 → ℕ :=
  ![1080,5636,61697,13386,9028,84563,4228,28696,12512,9308,17600,8960,8704,9600,7168,16458,33344,4946,1674,22016,402]

/-- Each table bit is checked against the independently defined actual root characters. -/
theorem catalog_evaluation_certificate (k : Fin 21) (i : Fin 17) :
    catalogForm i (pairVector k) =
      if (catalogEvaluationMasks k).testBit i.val then 1 else 0 := by
  simp only [catalogForm,character_pairVector]
  have h : ∀ k : Fin 21, ∀ i : Fin 17,
      (((if (masksA i).testBit (pairs k).1.val then 1 else 0) +
          (if (masksA i).testBit (pairs k).2.val then 1 else 0)) *
        ((if (masksB i).testBit (pairs k).1.val then 1 else 0) +
          (if (masksB i).testBit (pairs k).2.val then 1 else 0)) : F) =
        if (catalogEvaluationMasks k).testBit i.val then 1 else 0 := by
    decide +kernel
  exact h k i

/-- Actual evaluations of the retained catalog signs. -/
def retainedEvaluation (k : Fin 21) (j : Fin 12) : F :=
  wordForm (retainedWords j) (pairVector k)

/-- Compact independently checked values of those actual evaluations. -/
def evaluationMasks : Fin 21 → ℕ := ![528,716,1594,313,998,2965,648,24,872,1008,352,262,260,322,136,305,1060,47,85,268,67]

/-- Coefficients of an explicit left inverse. -/
def inverseMasks : Fin 12 → ℕ := ![22619,6144,22800,16577,16449,4547,22866,193,18704,16448,18695,18619]

def inverseCoefficient (j : Fin 12) (k : Fin 21) : F :=
  if (inverseMasks j).testBit k.val then 1 else 0

/-- The small matrix is checked against the independently defined root-character calculation. -/
theorem evaluation_certificate (k : Fin 21) (j : Fin 12) :
    retainedEvaluation k j = if (evaluationMasks k).testBit j.val then 1 else 0 := by
  simp only [retainedEvaluation,wordForm,catalog_evaluation_certificate]
  have h : ∀ k : Fin 21, ∀ j : Fin 12,
      (∑ i : Fin 17, if (retainedWords j).testBit i.val then
        (if (catalogEvaluationMasks k).testBit i.val then 1 else 0) else 0 : F) =
        if (evaluationMasks k).testBit j.val then 1 else 0 := by
    decide +kernel
  exact h k j

/-- The explicit matrix is a left inverse of the actual sign evaluations. -/
theorem inverse_certificate (i j : Fin 12) :
    (∑ k : Fin 21, inverseCoefficient i k * retainedEvaluation k j) = if i = j then 1 else 0 := by
  simp_rw [evaluation_certificate]
  have h : ∀ i j : Fin 12,
      (∑ k : Fin 21, inverseCoefficient i k *
        (if (evaluationMasks k).testBit j.val then 1 else 0)) = if i = j then 1 else 0 := by
    decide +kernel
  exact h i j

attribute [local irreducible] retainedEvaluation inverseCoefficient
set_option maxHeartbeats 400000

/-- The actual finite evaluation map of linear combinations of catalog forms. -/
def evaluationMap : (Fin 12 → F) →ₗ[F] (Fin 21 → F) :=
  Matrix.toLin' (Matrix.of retainedEvaluation)

/-- The explicit reverse coordinate map. -/
def inverseMap : (Fin 21 → F) →ₗ[F] (Fin 12 → F) :=
  Matrix.toLin' (Matrix.of inverseCoefficient)

/-- Actual linear independence of the twelve evaluated catalog forms. -/
theorem inverseMap_leftInverse : Function.LeftInverse inverseMap evaluationMap := by
  have he : Matrix.of inverseCoefficient * Matrix.of retainedEvaluation = (1 : Matrix (Fin 12) (Fin 12) F) := by
    ext i j
    simpa only [Matrix.mul_apply,Matrix.one_apply,Matrix.of_apply] using inverse_certificate i j
  intro v
  change (Matrix.toLin' (Matrix.of inverseCoefficient)) ((Matrix.toLin' (Matrix.of retainedEvaluation)) v) = v
  rw [← Matrix.toLin'_mul_apply,he,Matrix.toLin'_one,LinearMap.id_apply]

theorem evaluationMap_injective : Function.Injective evaluationMap :=
  inverseMap_leftInverse.injective

/-- Every nonzero combination has a nontrivial actual sign on a specified
pair vector; this is the exact certificate needed for Kummer nonsquareness. -/
theorem exists_nonzero_evaluation (v : Fin 12 → F) (hv : v ≠ 0) :
    ∃ k : Fin 21, (∑ j : Fin 12, retainedEvaluation k j*v j) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hv
  apply evaluationMap_injective
  ext k
  simpa only [evaluationMap,Matrix.toLin'_apply,Matrix.of_apply,Matrix.mulVec,dotProduct,LinearMap.map_zero,Pi.zero_apply] using h k

end UnitDistance.CatalogSquareclassData
