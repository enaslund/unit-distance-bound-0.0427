module

public import UnitDistance.GroupAugmentationRetainedQuadratic
public import Mathlib.LinearAlgebra.Pi

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact quadratic-relation certificate for the retained model

The kernel of the explicit 28-to-12 quadratic reduction is exactly the
span of the manuscript's sixteen literal rows. Both directions are proved
from finite column identities, including an explicit decomposition map.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

open scoped BigOperators
namespace UnitDistance.RetainedQuadratic

/-- Linear extension of binary columns over the ordinary field F₂. -/
def binaryMatrixMap (m n : ℕ) (columns : Fin m → ℕ) :
    (Fin m → F) →ₗ[F] (Fin n → F) where
  toFun v := ∑ i, v i • binaryVector n (columns i)
  map_add' v w := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r v := by simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,RingHom.id_apply]

def relationMasks : Fin 16 → ℕ :=
  ![1,1319172,21250048,71828496,167839776,218234880,4,8,16,32,64,2,106624,180352,8473259,69902422]

def relationVector (i : Fin 16) : Fin 28 → F := binaryVector 28 (relationMasks i)

def quadraticReduction := binaryMatrixMap 28 12 quadraticColumns

def relationExpansion := binaryMatrixMap 16 28 relationMasks

/-- Coefficients of the eliminated relation rows. -/
def relationCoefficientColumns : Fin 28 → ℕ :=
  ![1,2048,64,128,256,512,1024,0,0,0,0,0,0,0,0,0,4096,8192,0,0,66,0,44104,23169,44108,13116,44352,8492]

def relationCoefficients := binaryMatrixMap 28 16 relationCoefficientColumns

def freeColumnMasks : Fin 12 → ℕ :=
  ![128,256,512,1024,2048,4096,8192,16384,32768,262144,524288,2097152]

def freeExpansion := binaryMatrixMap 12 28 freeColumnMasks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem relation_reduction_certificate : ∀ (i : Fin 16) (k : Fin 12),
    quadraticReduction (relationVector i) k = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem quadratic_decomposition_certificate : ∀ (j : Fin 28) (k : Fin 28),
    (relationExpansion (relationCoefficients (Pi.single j 1)) +
      freeExpansion (quadraticReduction (Pi.single j 1))) k = (Pi.single j (1 : F) : Fin 28 → F) k := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem quadratic_section_certificate : ∀ (j : Fin 12) (k : Fin 12),
    quadraticReduction (freeExpansion (Pi.single j 1)) k = (Pi.single j (1 : F) : Fin 12 → F) k := by decide +kernel

attribute [local irreducible] quadraticReduction relationExpansion relationCoefficients freeExpansion

/-- Every literal quadratic vector is its actual relation part plus its
retained twelve-coordinate part. -/
theorem quadratic_decomposition (v : Fin 28 → F) :
    relationExpansion (relationCoefficients v)+freeExpansion (quadraticReduction v) = v := by
  have he : relationExpansion.comp relationCoefficients + freeExpansion.comp quadraticReduction =
      LinearMap.id := by
    apply (Pi.basisFun F (Fin 28)).ext
    intro j
    simpa only [Pi.basisFun_apply,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply]
      using funext (quadratic_decomposition_certificate j)
  exact congrArg (fun f : (Fin 28 → F) →ₗ[F] (Fin 28 → F) => f v) he

/-- No extra quadratic relation was inserted by the binary reduction. -/
theorem quadraticReduction_ker : quadraticReduction.ker =
    Submodule.span F (Set.range relationVector) := by
  apply le_antisymm
  · intro v hv
    have hz := LinearMap.mem_ker.mp hv
    rw [← quadratic_decomposition v,hz,map_zero,add_zero]
    rw [relationExpansion]
    change (∑ i, (relationCoefficients v) i • relationVector i) ∈ _
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro v ⟨i,rfl⟩
    exact funext (relation_reduction_certificate i)

/-- The twelve retained coordinates are all realized by actual quadratic
vectors; the displayed target is not an assumed quotient dimension. -/
theorem quadraticReduction_surjective : Function.Surjective quadraticReduction := by
  have he : quadraticReduction.comp freeExpansion = LinearMap.id := by
    apply (Pi.basisFun F (Fin 12)).ext
    intro j
    simpa only [Pi.basisFun_apply,LinearMap.comp_apply,LinearMap.id_apply]
      using funext (quadratic_section_certificate j)
  intro v
  exact ⟨freeExpansion v,congrArg (fun f : W →ₗ[F] W => f v) he⟩

end UnitDistance.RetainedQuadratic
