module

public import UnitDistance.JenningsOrderedBasis

@[expose] public section
set_option backward.privateInPublic true


/-!
# Canonical augmentation basis indexed by the actual group-generator list

This equivalent indexing makes the prescribed local factor block explicit
when constructing the ambient product basis.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
variable (G : Type*) [Group G] [Finite G] (hG : IsPGroup 2 G)

def generatorLetter (i : Fin (homogeneousGenerators G).length) : G :=
  (homogeneousGenerators G).get i

theorem generatorLetter_degree_pos (i : Fin (homogeneousGenerators G).length) :
    1 ≤ groupDegree G hG (generatorLetter G i) := by
  let j : Fin (homogeneousDifferences G).length := ⟨i.val,by simpa [homogeneousDifferences] using i.isLt⟩
  exact monomialLetter_degree_pos G hG j

theorem generatorLetters_spansActualLayers :
    SpansActualLayers G (Fin (homogeneousGenerators G).length) (generatorLetter G)
      (fun i => groupDegree G hG (generatorLetter G i)) := by
  intro n hn a
  letI : Fact (1 ≤ n) := ⟨hn⟩
  refine ⟨initialDifference G n a,?_,difference_sub_initial_mem G n a⟩
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (layerBasisLift_mem_homogeneousGenerators G hG n j)
  apply Submodule.subset_span
  refine ⟨i,?_,?_⟩
  · change groupDegree G hG ((homogeneousGenerators G).get i) = n
    rw [hi,groupDegree_layerBasisLift]
  · change delta (ZMod 2) (layerBasisLift G n j : G)-1 =
      delta (ZMod 2) ((homogeneousGenerators G).get i)-1
    rw [hi]

def generatorMonomial := JenningsCollection.binaryMonomial (ZMod 2) G
  (homogeneousGenerators G).length (fun i => delta (ZMod 2) (generatorLetter G i)-1)

def generatorWeight := JenningsCollection.binaryWeight (homogeneousGenerators G).length
  (fun i => groupDegree G hG (generatorLetter G i))

def generatorBasis : Module.Basis (Fin (homogeneousGenerators G).length → Bool)
    (ZMod 2) (A (ZMod 2) G) :=
  homogeneousBinaryBasis G hG _ (generatorLetter G)
    (fun i => groupDegree G hG (generatorLetter G i))
    (generatorLetter_degree_pos G hG)
    (fun _ => mem_dimensionSubgroup_groupDegree G hG _)
    (generatorLetters_spansActualLayers G hG) (two_pow_length_homogeneousGenerators G hG)

@[simp] theorem generatorBasis_apply (c : Fin (homogeneousGenerators G).length → Bool) :
    generatorBasis G hG c = generatorMonomial G c := by
  simp [generatorBasis,generatorMonomial]

theorem generatorWeightedSpan_eq_power (n : ℕ) :
    Submodule.span (ZMod 2) {a | ∃ c, n ≤ generatorWeight G hG c ∧ a = generatorBasis G hG c} =
      power (ZMod 2) G n := by
  simp only [generatorBasis_apply]
  exact binarySpan_eq_power_of_spansActualLayers G hG _ (generatorLetter G)
    (fun i => groupDegree G hG (generatorLetter G i))
    (generatorLetter_degree_pos G hG)
    (fun _ => mem_dimensionSubgroup_groupDegree G hG _)
    (generatorLetters_spansActualLayers G hG) n

end UnitDistance.GroupAugmentation
