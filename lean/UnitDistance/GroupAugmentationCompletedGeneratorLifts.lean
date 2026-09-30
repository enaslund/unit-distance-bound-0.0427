module

public import UnitDistance.GroupAugmentationRelationBlocks

@[expose] public section
set_option backward.privateInPublic true


/-!
# Literal finite affine lifts of actual completed generator words

Arithmetic generator lifts can be genuine completed words. Density supplies
literal words with identical entire finite affine evaluations. Substitution
of any completed local relator then has exactly the same global evaluated
Fox row. This proves the evaluated-row coverage bridge without identifying
completed words themselves with finite words.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace UnitDistance.GroupAugmentation
universe u
variable {ι κ : Type u}

/-- Continuous substitution by actual completed global generator words. -/
def completedGeneratorSubstitution (lifts : κ → CompletedWords ι) :
    CompletedWords κ ⟶ CompletedWords ι :=
  ProfiniteGrp.ProfiniteCompletion.lift (GrpCat.ofHom (FreeGroup.lift lifts))

@[simp] theorem completedGeneratorSubstitution_word (lifts : κ → CompletedWords ι)
    (w : FreeGroup κ) :
    completedGeneratorSubstitution lifts (wordCompletion κ w) = FreeGroup.lift lifts w := by
  have he := ProfiniteGrp.ProfiniteCompletion.lift_eta
    (P := CompletedWords ι) (GrpCat.ofHom (FreeGroup.lift lifts))
  exact ConcreteCategory.congr_hom he w

variable (P : Type u) [Group P] [Finite P] [Fintype ι]
local notation "F" => ZMod 2
variable (generators : ι → P)

/-- Actual finite affine evaluations of completed generator lifts can all
be matched by ordinary words. -/
theorem exists_literal_affine_lifts (lifts : κ → CompletedWords ι) :
    ∃ words : κ → FreeGroup ι, ∀ j,
      foxLift F P generators (words j) = completedFoxLift P generators (lifts j) := by
  have h (j : κ) := exists_word_matching (FoxAffine F P (ι := ι))
    (foxLift F P generators) (lifts j)
  exact ⟨fun j => (h j).choose,fun j => (h j).choose_spec⟩

/-- Matching generator affine evaluations preserves the full affine
evaluation of every substituted completed local word. -/
theorem completedGeneratorSubstitution_affine_eq
    (lifts : κ → CompletedWords ι) (words : κ → FreeGroup ι)
    (hmatch : ∀ j, foxLift F P generators (words j) = completedFoxLift P generators (lifts j))
    (r : CompletedWords κ) :
    completedFoxLift P generators (completedGeneratorSubstitution lifts r) =
      completedFoxLift P generators (completedSubstitution words r) := by
  have hword (w : FreeGroup κ) :
      completedFoxLift P generators (FreeGroup.lift lifts w) =
        foxLift F P generators (FreeGroup.lift words w) := by
    induction w using FreeGroup.induction_on with
    | one => simp
    | of j => simpa only [FreeGroup.lift_apply_of] using (hmatch j).symm
    | inv_of j hj => simp only [map_inv,hj]
    | mul a b ha hb => simp only [map_mul,ha,hb]
  have he : completedGeneratorSubstitution lifts ≫ completedFoxLift P generators =
      completedSubstitution words ≫ completedFoxLift P generators := by
    apply ProfiniteGrp.ProfiniteCompletion.lift_unique
    apply GrpCat.ext
    intro w
    change completedFoxLift P generators
        (completedGeneratorSubstitution lifts (wordCompletion κ w)) =
      completedFoxLift P generators (completedSubstitution words (wordCompletion κ w))
    rw [completedGeneratorSubstitution_word,completedSubstitution_word]
    simpa only [completedFoxLift,completedFiniteMap_word] using hword w
  have hh := ConcreteCategory.congr_hom he r
  simpa only [ProfiniteGrp.comp_apply] using hh

/-- In particular the actual global completed Fox rows agree exactly. -/
theorem completedGeneratorSubstitution_derivative_eq
    (lifts : κ → CompletedWords ι) (words : κ → FreeGroup ι)
    (hmatch : ∀ j, foxLift F P generators (words j) = completedFoxLift P generators (lifts j))
    (r : CompletedWords κ) :
    completedFoxDerivative P generators (completedGeneratorSubstitution lifts r) =
      completedFoxDerivative P generators (completedSubstitution words r) := by
  exact congrArg (fun a : FoxAffine F P (ι := ι) => a.left.toAdd)
    (completedGeneratorSubstitution_affine_eq P generators lifts words hmatch r)

/-- Actual generator values are also preserved by the literal affine lifts. -/
theorem literal_affine_lifts_evaluation
    (lifts : κ → CompletedWords ι) (words : κ → FreeGroup ι)
    (hmatch : ∀ j, foxLift F P generators (words j) = completedFoxLift P generators (lifts j))
    (j : κ) :
    FreeGroup.lift generators (words j) = completedWordEvaluation P generators (lifts j) := by
  have h := congrArg (fun a : FoxAffine F P (ι := ι) => a.right) (hmatch j)
  change (foxLift F P generators (words j)).right =
    completedWordEvaluation P generators (lifts j) at h
  rw [foxLift_right] at h
  exact h

variable {J : Type*} (κs : J → Type u) [∀ j, Fintype (κs j)]

/-- The actual family of relations substituted using completed, rather than
literal, global generator lifts. -/
def completedGeneratorRelationFamily (lifts : ∀ j, κs j → CompletedWords ι)
    (localRelations : ∀ j, Set (CompletedWords (κs j))) : Set (CompletedWords ι) :=
  {r | ∃ (j : J) (s : CompletedWords (κs j)), s ∈ localRelations j ∧
    completedGeneratorSubstitution (lifts j) s = r}

/-- Actual completed local generator lifts and finite local relation
identities construct literal affine representatives and prove all required
row coverage. The relations themselves remain genuinely completed words. -/
theorem exists_literal_family_row_coverage
    (D : J → Type u) [∀ j, Group (D j)] [∀ j, Finite (D j)]
    (localGenerators : ∀ j, κs j → D j) (localMaps : ∀ j, D j →* P)
    (lifts : ∀ j, κs j → CompletedWords ι)
    (hlifts : ∀ j i, completedWordEvaluation P generators (lifts j i) =
      localMaps j (localGenerators j i))
    (localRelations : ∀ j, Set (CompletedWords (κs j)))
    (hlocalRel : ∀ j s, s ∈ localRelations j →
      completedWordEvaluation (D j) (localGenerators j) s = 1) :
    ∃ words : ∀ j, κs j → FreeGroup ι,
      (∀ j i, FreeGroup.lift generators (words j i) = localMaps j (localGenerators j i)) ∧
      CompletedFoxRowCoverage P generators κs words
        (completedGeneratorRelationFamily κs lifts localRelations) := by
  classical
  have h (j : J) := exists_literal_affine_lifts P generators (lifts j)
  let words : ∀ j, κs j → FreeGroup ι := fun j => (h j).choose
  have hmatch (j : J) : ∀ i, foxLift F P generators (words j i) =
      completedFoxLift P generators (lifts j i) := (h j).choose_spec
  have hwords (j : J) (i : κs j) : FreeGroup.lift generators (words j i) =
      localMaps j (localGenerators j i) :=
    (literal_affine_lifts_evaluation P generators (lifts j) (words j) (hmatch j) i).trans (hlifts j i)
  refine ⟨words,hwords,?_⟩
  rintro r ⟨j,s,hs,rfl⟩
  refine ⟨j,s,?_,?_⟩
  · simp_rw [hwords]
    rw [completedWordEvaluation_naturality,hlocalRel j s hs,map_one]
  · exact completedGeneratorSubstitution_derivative_eq P generators (lifts j) (words j) (hmatch j) s

end UnitDistance.GroupAugmentation
