module

public import UnitDistance.JenningsAdaptedGenerators
public import UnitDistance.JenningsGeneratorBasis

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual subgroup-compatible product basis and additive weights

The constructed ambient augmentation basis is reindexed into complementary
and local binary coordinates. Its elements are literally products of an
ambient complementary monomial and the image of the original local
augmentation monomial. Actual augmentation powers have exactly the sum
of these two independently defined weights.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.JenningsCollection
open GroupAugmentation

/-- Splitting a binary coordinate vector into its two consecutive blocks. -/
def splitBinaryChoices (r s : ℕ) : (Fin (r+s) → Bool) ≃ (Fin r → Bool) × (Fin s → Bool) where
  toFun c := (fun i => c (Fin.castAdd s i),fun i => c (Fin.natAdd r i))
  invFun p := Fin.addCases p.1 p.2
  left_inv c := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  right_inv p := by
    apply Prod.ext <;> funext i <;> simp

variable (R G : Type*) [CommRing R] [Group G] (r s : ℕ)

theorem binaryMonomial_add (x : Fin (r+s) → A R G) (c : Fin (r+s) → Bool) :
    binaryMonomial R G (r+s) x c =
      binaryMonomial R G r (fun i => x (Fin.castAdd s i)) (fun i => c (Fin.castAdd s i)) *
      binaryMonomial R G s (fun i => x (Fin.natAdd r i)) (fun i => c (Fin.natAdd r i)) := by
  simp only [binaryMonomial,List.ofFn_add,List.prod_append]
  rfl

theorem binaryWeight_add (w : Fin (r+s) → ℕ) (c : Fin (r+s) → Bool) :
    binaryWeight (r+s) w c =
      binaryWeight r (fun i => w (Fin.castAdd s i)) (fun i => c (Fin.castAdd s i)) +
      binaryWeight s (fun i => w (Fin.natAdd r i)) (fun i => c (Fin.natAdd r i)) := by
  exact Fin.sum_univ_add _

end UnitDistance.JenningsCollection

namespace UnitDistance.GroupAugmentation
open JenningsCollection
variable (D P : Type*) [Group D] [Group P] [Finite D] [Finite P]
variable (f : D →* P)
variable (hinj : ∀ n, Function.Injective (layerMap (ZMod 2) D f n))
variable (hD : IsPGroup 2 D) (hP : IsPGroup 2 P)

/-- Binary choices in only the added homogeneous ambient directions. -/
abbrev ComplementChoices := Fin (complementGenerators D P f hinj).length → Bool

/-- An actual complementary augmentation monomial in the ambient algebra. -/
def complementMonomial (c : ComplementChoices D P f hinj) : A (ZMod 2) P :=
  binaryMonomial (ZMod 2) P (complementGenerators D P f hinj).length
    (fun i => delta (ZMod 2) ((complementGenerators D P f hinj).get i)-1) c

/-- Its shift is the sum of actual augmentation degrees of its factors. -/
def complementWeight (c : ComplementChoices D P f hinj) : ℕ :=
  binaryWeight (complementGenerators D P f hinj).length
    (fun i => groupDegree P hP ((complementGenerators D P f hinj).get i)) c

include hinj in
/-- Injective actual layer maps preserve the exact degrees of the
prescribed local homogeneous group representatives. -/
theorem groupDegree_mapped_generatorLetter (i : Fin (homogeneousGenerators D).length) :
    groupDegree P hP (f (generatorLetter D i)) = groupDegree D hD (generatorLetter D i) := by
  let j : Fin (homogeneousDifferences D).length := ⟨i.val,by simpa [homogeneousDifferences] using i.isLt⟩
  obtain ⟨n,hn,k,hk⟩ := monomialLetter_has_layer D j
  letI := hn
  have hi : generatorLetter D i = (layerBasisLift D n k : D) := hk
  rw [hi,groupDegree_layerBasisLift]
  exact adaptedLayerLift_degree D P f n (hinj n) hP (Sum.inr k)

omit hinj hD hP in
theorem induced_generatorMonomial (c : Fin (homogeneousGenerators D).length → Bool) :
    induced (ZMod 2) D f (generatorMonomial D c) =
      binaryMonomial (ZMod 2) P (homogeneousGenerators D).length
        (fun i => delta (ZMod 2) (f (generatorLetter D i))-1) c := by
  simp [generatorMonomial,binaryMonomial,map_list_prod,List.map_ofFn,Function.comp_def,apply_ite]

/-- The actual product basis, indexed by complementary and local monomials. -/
def adaptedProductBasis :
    Module.Basis (ComplementChoices D P f hinj × (Fin (homogeneousGenerators D).length → Bool))
      (ZMod 2) (A (ZMod 2) P) :=
  (adaptedAugmentationBasis D P f hinj hD hP).reindex
    (splitBinaryChoices (complementGenerators D P f hinj).length (homogeneousGenerators D).length)

/-- Product factors are literal multiplication in the actual group algebra. -/
theorem adaptedProductBasis_apply
    (c : ComplementChoices D P f hinj) (d : Fin (homogeneousGenerators D).length → Bool) :
    adaptedProductBasis D P f hinj hD hP (c,d) =
      complementMonomial D P f hinj c * induced (ZMod 2) D f (generatorBasis D hD d) := by
  rw [adaptedProductBasis,Module.Basis.reindex_apply,adaptedAugmentationBasis_apply]
  rw [binaryMonomial_add,generatorBasis_apply,induced_generatorMonomial]
  simp only [splitBinaryChoices,Equiv.coe_fn_symm_mk,Fin.addCases_left,Fin.addCases_right,
    adaptedLetter,generatorLetter,complementMonomial]

theorem adaptedProductWeight
    (c : ComplementChoices D P f hinj) (d : Fin (homogeneousGenerators D).length → Bool) :
    binaryWeight (adaptedGeneratorCount D P f hinj)
      (fun i => groupDegree P hP (adaptedLetter D P f hinj i))
      ((splitBinaryChoices (complementGenerators D P f hinj).length
        (homogeneousGenerators D).length).symm (c,d)) =
      complementWeight D P f hinj hP c + generatorWeight D hD d := by
  rw [binaryWeight_add]
  simp only [splitBinaryChoices,Equiv.coe_fn_symm_mk,Fin.addCases_left,Fin.addCases_right,
    adaptedLetter,complementWeight,generatorWeight]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (if d i then groupDegree P hP (f (generatorLetter D i)) else 0) =
    (if d i then groupDegree D hD (generatorLetter D i) else 0)
  rw [groupDegree_mapped_generatorLetter D P f hinj hD hP]

/-- Actual ambient powers decompose according to the complementary shift
plus the actual local weight. This is the subgroup-compatible weighted
Jennings theorem, proved from the actual layer injections. -/
theorem adaptedProductWeightedSpan_eq_power (n : ℕ) :
    Submodule.span (ZMod 2) {a | ∃ p : ComplementChoices D P f hinj ×
      (Fin (homogeneousGenerators D).length → Bool),
      n ≤ complementWeight D P f hinj hP p.1 + generatorWeight D hD p.2 ∧
      a = adaptedProductBasis D P f hinj hD hP p} = power (ZMod 2) P n := by
  rw [← adaptedBinarySpan_eq_power D P f hinj hD hP n]
  unfold binarySpan
  congr 1
  ext a
  constructor
  · rintro ⟨⟨c,d⟩,hp,rfl⟩
    refine ⟨(splitBinaryChoices _ _).symm (c,d),?_,?_⟩
    · rwa [adaptedProductWeight]
    · simp only [adaptedProductBasis,Module.Basis.reindex_apply,adaptedAugmentationBasis_apply]
  · rintro ⟨c,hc,rfl⟩
    let p := splitBinaryChoices (complementGenerators D P f hinj).length
      (homogeneousGenerators D).length c
    refine ⟨p,?_,?_⟩
    · have he := adaptedProductWeight D P f hinj hD hP p.1 p.2
      have hpc : (splitBinaryChoices _ _).symm (p.1,p.2) = c := by
        exact (splitBinaryChoices _ _).symm_apply_apply c
      rw [hpc] at he
      exact he ▸ hc
    · simp only [adaptedProductBasis,Module.Basis.reindex_apply,adaptedAugmentationBasis_apply,p,
        Equiv.symm_apply_apply]

end UnitDistance.GroupAugmentation
