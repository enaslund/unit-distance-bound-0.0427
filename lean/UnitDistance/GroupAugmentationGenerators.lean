module

public import UnitDistance.GroupAugmentation
public import Mathlib.LinearAlgebra.Pi

@[expose] public section
set_option backward.privateInPublic true


/-!
# Strictness of the augmentation map from actual group generators

For arbitrary groups generated as groups by `dᵢ`, each actual augmentation
power `Iⁿ⁺¹` equals the sum of `Iⁿ(dᵢ-1)`. The proof handles inverse words
using the two-sided ideal property of the actual powers. Consequently the
usual finite generator map has exactly the required image at every degree.
This establishes the strict local augmentation sequence needed for filtered
Fox induction, without assuming an adapted ambient basis.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (R G : Type*) [CommRing R] [Group G]
variable {ι : Type*} (generators : ι → G)

/-- Right multiplication in the actual convolution algebra. -/
def rightMul (b : A R G) : A R G →ₗ[R] A R G where
  toFun a := a*b
  map_add' := fun _ _ => add_mul ..
  map_smul' := fun _ _ => smul_mul_assoc ..

/-- Degree `n` coefficients applied to the displayed generator differences. -/
def generatorImage (n : ℕ) : Submodule R (A R G) :=
  ⨆ i, (power R G n).map (rightMul R G (delta R (generators i) - 1))

theorem mul_generator_mem (n : ℕ) (i : ι) (a : A R G)
    (ha : a ∈ power R G n) : a * (delta R (generators i) - 1) ∈ generatorImage R G generators n :=
  (le_iSup (fun i => (power R G n).map (rightMul R G (delta R (generators i)-1))) i)
    ⟨a,ha,rfl⟩

/-- The group elements whose differences have the asserted generator expansion. -/
def expandedDifferences (n : ℕ) : Subgroup G where
  carrier := {g | ∀ a ∈ power R G n, a * (delta R g - 1) ∈ generatorImage R G generators n}
  one_mem' := by intro a _; simp
  mul_mem' {g h} hg hh := by
    intro a ha
    have h₁ := hh (a * delta R g) (mul_mem_right R G n _ _ ha)
    have h₂ := hg a ha
    have he : a * (delta R (g*h)-1) =
        (a * delta R g) * (delta R h-1) + a * (delta R g-1) := by
      rw [← delta_mul]
      noncomm_ring
    rw [he]
    exact (generatorImage R G generators n).add_mem h₁ h₂
  inv_mem' {g} hg := by
    intro a ha
    have hm := hg (a * delta R g⁻¹) (mul_mem_right R G n _ _ ha)
    have he : a * (delta R g⁻¹ - 1) = -(a * delta R g⁻¹ * (delta R g - 1)) := by
      simp [mul_sub, mul_assoc]
    rw [he]
    exact (generatorImage R G generators n).neg_mem hm

theorem mul_difference_mem
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (n : ℕ) (g : G) (a : A R G) (ha : a ∈ power R G n) :
    a * (delta R g - 1) ∈ generatorImage R G generators n := by
  have he : Subgroup.closure (Set.range generators) ≤ expandedDifferences R G generators n := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i,rfl⟩ a ha
    exact mul_generator_mem R G generators n i a ha
  rw [hgen] at he
  exact he (Subgroup.mem_top g) a ha

/-- Linear extension of the group-difference expansion, valid even for an
infinite group since every group-algebra vector has finite support. -/
theorem mul_augmentation_residual_mem
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (n : ℕ) (a b : A R G) (ha : a ∈ power R G n) :
    a * (b - augmentation R G b • 1) ∈ generatorImage R G generators n := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc =>
    have he : a * (b+c - augmentation R G (b+c) • 1) =
        a * (b - augmentation R G b • 1) + a * (c - augmentation R G c • 1) := by
      simp only [map_add, add_smul]
      noncomm_ring
    rw [he]
    exact (generatorImage R G generators n).add_mem hb hc
  | single g r =>
    have he : MonoidAlgebra.single g r = r • delta R g := by simp [delta]
    rw [augmentation_single, he, ← smul_sub, mul_smul_comm]
    exact (generatorImage R G generators n).smul_mem r
      (mul_difference_mem R G generators hgen n g a ha)

/-- Every augmentation power is generated in exactly the expected next
step by the actual chosen group generators. -/
theorem power_succ_eq_generatorImage
    (hgen : Subgroup.closure (Set.range generators) = ⊤) (n : ℕ) :
    power R G (n+1) = generatorImage R G generators n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨a,ha,b,hb,rfl⟩
    simpa [hb] using mul_augmentation_residual_mem R G generators hgen n a b ha
  · apply iSup_le
    intro i
    rintro v ⟨a,ha,rfl⟩
    exact mul_mem_succ R G ha (by simp)

variable [Fintype ι]

/-- The usual augmentation generator map with left Fox coefficients. -/
def foxMap : (ι → A R G) →ₗ[R] A R G where
  toFun a := ∑ i, a i * (delta R (generators i)-1)
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.smul_sum]

/-- Coefficient vectors with actual augmentation degree at least `n`. -/
def coefficientPower (n : ℕ) : Submodule R (ι → A R G) :=
  Submodule.pi Set.univ (fun _ => power R G n)

omit [Fintype ι] in
@[simp] theorem mem_coefficientPower (n : ℕ) (a : ι → A R G) :
    a ∈ coefficientPower R G (ι := ι) n ↔ ∀ i, a i ∈ power R G n := by
  simp [coefficientPower, Submodule.mem_pi]

theorem map_coefficientPower (n : ℕ) :
    (coefficientPower R G (ι := ι) n).map (foxMap R G generators) =
      generatorImage R G generators n := by
  classical
  apply le_antisymm
  · rintro x ⟨a,ha,rfl⟩
    apply Submodule.sum_mem
    intro i _
    exact mul_generator_mem R G generators n i (a i) ((mem_coefficientPower R G n a).mp ha i)
  · apply iSup_le
    intro i
    rintro x ⟨a,ha,rfl⟩
    refine ⟨(fun j => if j = i then a else 0), ?_, ?_⟩
    · apply (mem_coefficientPower R G n _).mpr
      intro j
      split
      · exact ha
      · exact Submodule.zero_mem _
    · change (∑ j, (if j = i then a else 0) * (delta R (generators j)-1)) =
        a * (delta R (generators i)-1)
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp only [if_neg hji, zero_mul]
      · simp

/-- Strictness at every actual augmentation degree, which is the exact
filtration input for the local augmentation short exact sequence. -/
theorem foxMap_strict
    (hgen : Subgroup.closure (Set.range generators) = ⊤) (n : ℕ) :
    (coefficientPower R G (ι := ι) n).map (foxMap R G generators) = power R G (n+1) := by
  rw [map_coefficientPower, power_succ_eq_generatorImage R G generators hgen]

end UnitDistance.GroupAugmentation
