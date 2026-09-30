module

public import UnitDistance.GroupAugmentationCompletedWords

@[expose] public section
set_option backward.privateInPublic true


/-!
# Naturality of actual Fox derivatives under group homomorphisms

Both literal and genuinely completed relators have compatible Fox rows in
the local and ambient group algebras. The completed statement follows by
simultaneously matching the two finite affine evaluations.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
universe u
variable (R : Type*) (D P : Type u) [CommRing R] [Group D] [Group P]
variable {ι : Type u} (localGenerators : ι → D) (f : D →* P)

/-- Evaluation of literal words commutes with an actual group homomorphism. -/
theorem lift_map_generators (w : FreeGroup ι) :
    FreeGroup.lift (fun i => f (localGenerators i)) w = f (FreeGroup.lift localGenerators w) := by
  have he : FreeGroup.lift (fun i => f (localGenerators i)) = f.comp (FreeGroup.lift localGenerators) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  exact DFunLike.congr_fun he w

/-- The actual evaluated Fox derivative commutes with the induced algebra map. -/
theorem foxDerivative_naturality (w : FreeGroup ι) (i : ι) :
    foxDerivative R P (fun j => f (localGenerators j)) w i =
      induced R D f (foxDerivative R D localGenerators w i) := by
  classical
  induction w using FreeGroup.induction_on with
  | one => simp
  | of j => simp [Pi.single_apply]
  | inv_of j hj =>
    simp only [foxDerivative_inv,map_neg,map_mul,induced_delta,map_inv,lift_map_generators,hj]
  | mul a b ha hb =>
    simp only [foxDerivative_mul,map_add,map_mul,induced_delta,lift_map_generators,ha,hb]

variable [Finite D] [Finite P] [Fintype ι]
local notation "F" => ZMod 2

/-- The same compatibility holds for each actual completed relator. -/
theorem completedFoxDerivative_naturality (r : CompletedWords ι) (i : ι) :
    completedFoxDerivative P (fun j => f (localGenerators j)) r i =
      induced F D f (completedFoxDerivative D localGenerators r i) := by
  obtain ⟨w,hwD,hwP⟩ := exists_word_matching_pair
    (FoxAffine F D (ι := ι)) (FoxAffine F P (ι := ι))
    (foxLift F D localGenerators) (foxLift F P (fun j => f (localGenerators j))) r
  have hD := congrArg (fun a : FoxAffine F D (ι := ι) => a.left.toAdd i) hwD
  have hP := congrArg (fun a : FoxAffine F P (ι := ι) => a.left.toAdd i) hwP
  change foxDerivative F D localGenerators w i = completedFoxDerivative D localGenerators r i at hD
  change foxDerivative F P (fun j => f (localGenerators j)) w i =
    completedFoxDerivative P (fun j => f (localGenerators j)) r i at hP
  rw [← hD,← hP]
  exact foxDerivative_naturality F D P localGenerators f w i

/-- Actual completed word evaluation is natural under finite group maps. -/
theorem completedWordEvaluation_naturality (r : CompletedWords ι) :
    completedWordEvaluation P (fun j => f (localGenerators j)) r =
      f (completedWordEvaluation D localGenerators r) := by
  obtain ⟨w,hwD,hwP⟩ := exists_word_matching_pair
    (FoxAffine F D (ι := ι)) (FoxAffine F P (ι := ι))
    (foxLift F D localGenerators) (foxLift F P (fun j => f (localGenerators j))) r
  have hD := congrArg (fun a : FoxAffine F D (ι := ι) => a.right) hwD
  have hP := congrArg (fun a : FoxAffine F P (ι := ι) => a.right) hwP
  change (foxLift F D localGenerators w).right = completedWordEvaluation D localGenerators r at hD
  change (foxLift F P (fun j => f (localGenerators j)) w).right =
    completedWordEvaluation P (fun j => f (localGenerators j)) r at hP
  rw [foxLift_right] at hD hP
  rw [← hD,← hP,lift_map_generators]

end UnitDistance.GroupAugmentation
