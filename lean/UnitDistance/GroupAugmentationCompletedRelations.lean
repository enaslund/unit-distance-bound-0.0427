module

public import UnitDistance.GroupAugmentationCompletedPresentation

@[expose] public section
set_option backward.privateInPublic true


/-!
# Completed normal closure supplies actual global Fox-row membership

A completed word in the closed normal closure of actual defining relations
has evaluated derivative in their actual left row module. The proof uses
continuity into a finite affine group, so it applies to genuine completed
relators without replacing them by finite words.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.GroupAugmentation
universe u
variable (G : Type u) [Group G] [Finite G]
variable {ι : Type u} [Fintype ι]
local notation "F" => ZMod 2
variable (generators : ι → G)

@[simp] theorem completedFoxDerivative_one :
    completedFoxDerivative G generators (1 : CompletedWords ι) = 0 := by
  simp [completedFoxDerivative,completedFoxLift]

@[simp] theorem completedWordEvaluation_one :
    completedWordEvaluation G generators (1 : CompletedWords ι) = 1 := by
  simp [completedWordEvaluation,completedFoxLift]

theorem completedFoxDerivative_mul (r s : CompletedWords ι) (i : ι) :
    completedFoxDerivative G generators (r*s) i = completedFoxDerivative G generators r i +
      delta F (completedWordEvaluation G generators r) * completedFoxDerivative G generators s i := by
  simp only [completedFoxDerivative,completedWordEvaluation,map_mul]
  rfl

theorem completedWordEvaluation_mul (r s : CompletedWords ι) :
    completedWordEvaluation G generators (r*s) =
      completedWordEvaluation G generators r * completedWordEvaluation G generators s := by
  simp only [completedWordEvaluation,map_mul]
  rfl

theorem completedFoxDerivative_inv (r : CompletedWords ι) (i : ι) :
    completedFoxDerivative G generators r⁻¹ i =
      -(delta F (completedWordEvaluation G generators r)⁻¹ * completedFoxDerivative G generators r i) := by
  simp only [completedFoxDerivative,completedWordEvaluation,map_inv]
  change delta F (completedWordEvaluation G generators r)⁻¹ *
    (-completedFoxDerivative G generators r i) = _
  exact mul_neg _ _

theorem completedWordEvaluation_inv (r : CompletedWords ι) :
    completedWordEvaluation G generators r⁻¹ = (completedWordEvaluation G generators r)⁻¹ := by
  simp only [completedWordEvaluation,map_inv]
  rfl

theorem completedFoxDerivative_conjugate (u r : CompletedWords ι)
    (hr : completedWordEvaluation G generators r = 1) :
    completedFoxDerivative G generators (u*r*u⁻¹) =
      delta F (completedWordEvaluation G generators u) • completedFoxDerivative G generators r := by
  funext i
  simp only [completedFoxDerivative_mul,completedFoxDerivative_inv,
    completedWordEvaluation_mul,hr,mul_one,Pi.smul_apply,smul_eq_mul,mul_neg,
    ← mul_assoc,delta_mul,mul_inv_cancel,delta_one,one_mul]
  abel

variable (M : Submodule (A F G) (ι → A F G))

/-- Actual completed kernel words with rows in a specified algebra submodule. -/
def completedFoxWordsModulo : Subgroup (CompletedWords ι) where
  carrier := {r | completedWordEvaluation G generators r = 1 ∧
    completedFoxDerivative G generators r ∈ M}
  one_mem' := by simp
  mul_mem' {r s} hr hs := by
    refine ⟨by rw [completedWordEvaluation_mul,hr.1,hs.1,mul_one],?_⟩
    have he : completedFoxDerivative G generators (r*s) =
        completedFoxDerivative G generators r + completedFoxDerivative G generators s := by
      ext i
      simp [completedFoxDerivative_mul,hr.1]
    rw [he]
    exact M.add_mem hr.2 hs.2
  inv_mem' {r} hr := by
    refine ⟨by rw [completedWordEvaluation_inv,hr.1,inv_one],?_⟩
    have he : completedFoxDerivative G generators r⁻¹ = -completedFoxDerivative G generators r := by
      ext i
      simp [completedFoxDerivative_inv,hr.1]
    rw [he]
    exact M.neg_mem hr.2

instance completedFoxWordsModulo_normal : (completedFoxWordsModulo G generators M).Normal where
  conj_mem r hr u := by
    refine ⟨?_,?_⟩
    · simp [completedWordEvaluation_mul,completedWordEvaluation_inv,hr.1]
    · rw [completedFoxDerivative_conjugate G generators u r hr.1]
      exact M.smul_mem _ hr.2

/-- Closedness is a proved consequence of the finite discrete affine target. -/
theorem completedFoxWordsModulo_closed :
    IsClosed (completedFoxWordsModulo G generators M : Set (CompletedWords ι)) := by
  let S : Set (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (FoxAffine F G (ι := ι)))) :=
    {a | a.right = 1 ∧ a.left.toAdd ∈ M}
  have hS : IsClosed S := isClosed_discrete S
  exact hS.preimage (completedFoxLift G generators).hom.continuous_toFun

/-- The row of an actual completed normal consequence belongs to the actual
left span of the original rows. This includes the common dyadic row once
the arithmetic presentation establishes the stated closure membership. -/
theorem completedFoxDerivative_mem_of_closed_normalClosure
    (relations : Set (CompletedWords ι))
    (hrel : ∀ r ∈ relations, completedWordEvaluation G generators r = 1)
    (r : CompletedWords ι)
    (hr : r ∈ (Subgroup.normalClosure relations).topologicalClosure) :
    completedFoxDerivative G generators r ∈ completedFoxRelationModule G generators relations := by
  let M := completedFoxRelationModule G generators relations
  have hle : Subgroup.normalClosure relations ≤ completedFoxWordsModulo G generators M := by
    apply Subgroup.normalClosure_le_normal
    intro s hs
    exact ⟨hrel s hs,Submodule.subset_span ⟨s,hs,rfl⟩⟩
  have hc : (Subgroup.normalClosure relations).topologicalClosure ≤
      completedFoxWordsModulo G generators M := by
    apply Subgroup.topologicalClosure_minimal (Subgroup.normalClosure relations) hle
    exact completedFoxWordsModulo_closed G generators M
  exact (hc hr).2

/-- An actual completed relator is a consequence of the displayed relations
in every finite 2-group test. This expresses pro-2 consequence without
requiring membership in the stronger full-profinite closed normal closure. -/
def CompletedProTwoConsequence (relations : Set (CompletedWords ι))
    (r : CompletedWords ι) : Prop :=
  ∀ (N : Subgroup (FreeGroup ι)) [N.Normal] [Finite (FreeGroup ι ⧸ N)],
    IsPGroup 2 (FreeGroup ι ⧸ N) →
    (∀ s ∈ relations, completedFiniteMap (FreeGroup ι ⧸ N) (QuotientGroup.mk' N) s = 1) →
    completedFiniteMap (FreeGroup ι ⧸ N) (QuotientGroup.mk' N) r = 1

/-- A pro-2 consequence already puts the actual completed row in the actual
original row module. Its test quotient is the proved finite affine 2-group
quotient; no assertion about full-profinite normal closure is needed. -/
theorem completedFoxDerivative_mem_of_proTwoConsequence (hG : IsPGroup 2 G)
    (relations : Set (CompletedWords ι))
    (hrel : ∀ s ∈ relations, completedWordEvaluation G generators s = 1)
    (r : CompletedWords ι) (hr : CompletedProTwoConsequence relations r) :
    completedFoxDerivative G generators r ∈ completedFoxRelationModule G generators relations := by
  let M := completedFoxRelationModule G generators relations
  let N := foxWordsModulo F G generators M
  obtain ⟨hfinite,hTwo⟩ := foxWordsModulo_isFiniteTwoQuotient G generators hG M
  letI : Finite (FreeGroup ι ⧸ N) := hfinite
  have hN : ∀ s ∈ relations,
      completedFiniteMap (FreeGroup ι ⧸ N) (QuotientGroup.mk' N) s = 1 := by
    intro s hs
    obtain ⟨w,hwL,hwN⟩ := exists_word_matching_pair
      (FoxAffine F G (ι := ι)) (FreeGroup ι ⧸ N)
      (foxLift F G generators) (QuotientGroup.mk' N) s
    have he := congrArg (fun a : FoxAffine F G (ι := ι) => a.right) hwL
    change (foxLift F G generators w).right = completedWordEvaluation G generators s at he
    rw [foxLift_right,hrel s hs] at he
    have hd := congrArg (fun a : FoxAffine F G (ι := ι) => a.left.toAdd) hwL
    change foxDerivative F G generators w = completedFoxDerivative G generators s at hd
    have hw : w ∈ N := by
      refine ⟨he,?_⟩
      rw [hd]
      exact Submodule.subset_span ⟨s,hs,rfl⟩
    rw [← hwN]
    exact (QuotientGroup.eq_one_iff w).mpr hw
  have hrN := hr N hTwo hN
  obtain ⟨w,hwL,hwN⟩ := exists_word_matching_pair
    (FoxAffine F G (ι := ι)) (FreeGroup ι ⧸ N)
    (foxLift F G generators) (QuotientGroup.mk' N) r
  have hw : w ∈ N := (QuotientGroup.eq_one_iff w).mp (hwN.trans hrN)
  have hd := congrArg (fun a : FoxAffine F G (ι := ι) => a.left.toAdd) hwL
  change foxDerivative F G generators w = completedFoxDerivative G generators r at hd
  rw [← hd]
  exact hw.2

end UnitDistance.GroupAugmentation
