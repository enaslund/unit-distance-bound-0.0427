module

public import UnitDistance.SigmaDyadicFreeMap
public import UnitDistance.DyadicArithmeticPresentation
public import UnitDistance.DyadicGenuineFoxInitial
public import UnitDistance.ProTwoCompletedSubstitution

@[expose] public section
set_option backward.privateInPublic true


/-! A literal completed arithmetic dyadic relation. Its local evaluation,
first Fox row, and actual global kernel membership are all proved from the
constructed local field and its genuine quadratic relation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace UnitDistance.SigmaDyadic
open GroupAugmentation ArithmeticProP

/-- Canonical section of actual full-profinite words onto the actual free
pro-two group; it is only used to select words. -/
def completedLift (d : ℕ) (g : FiniteFreeProTwo.Carrier d) : CompletedWords (Fin d) :=
  Function.surjInv (completionMap_surjective (FiniteFreeProTwo.generator d)
    (FiniteFreeProTwo.isFree d).generates_range) g

@[simp] theorem completedLift_map (d : ℕ) (g : FiniteFreeProTwo.Carrier d) :
    completionMap (FiniteFreeProTwo.generator d) (completedLift d g)=g :=
  Function.surjInv_eq (completionMap_surjective (FiniteFreeProTwo.generator d)
    (FiniteFreeProTwo.isFree d).generates_range) g

def completedABC : CompletedWords (Fin 3) := completedLift 3 genuineRelation

theorem completedABC_detector :
    completedFiniteMap FreeThreeQuadratic.Q FreeThreeQuadratic.wordDetector completedABC=
      FreeThreeQuadratic.relation := by
  let π : LocalSource →ₜ* ProfiniteGrp.ofFiniteGrp (FiniteGrp.of FreeThreeQuadratic.Q) :=
    ⟨PadicTwoQuadraticRelation.detector.toMonoidHom,
      PadicTwoQuadraticRelation.detector.continuous⟩
  have he : π.toMonoidHom.comp (FreeGroup.lift (FiniteFreeProTwo.generator 3))=
      FreeThreeQuadratic.wordDetector := by
    apply FreeGroup.ext_hom
    intro i
    change PadicTwoQuadraticRelation.detector
      (FreeGroup.lift (FiniteFreeProTwo.generator 3) (FreeGroup.of i))=
      FreeGroup.lift FreeThreeQuadratic.basis (FreeGroup.of i)
    rw [FreeGroup.lift_apply_of,FreeGroup.lift_apply_of]
    exact PadicTwoQuadraticRelation.detector_generator i
  have h := finiteMap_comp_completionMap (FiniteFreeProTwo.generator 3)
    FreeThreeQuadratic.Q π completedABC
  rw [he] at h
  rw [←h]
  change PadicTwoQuadraticRelation.detector
    (completionMap (FiniteFreeProTwo.generator 3) (completedLift 3 genuineRelation))=_
  rw [completedLift_map,genuineRelation_detector]

/-- The actual completed relation in the x=b,y=a,z=a*c coordinates. -/
def completedRelation : CompletedWords (Fin 3) :=
  completedSubstitution Dyadic.GenuineFox.inverseWords completedABC

theorem completedRelation_initial :
    completedWordEvaluation Dyadic.D Dyadic.Filtration.gen completedRelation=1 ∧
      ∀i,completedFoxDerivative Dyadic.D Dyadic.Filtration.gen completedRelation i-
        Dyadic.AlgebraD.linearFoxCoefficients i∈Dyadic.AlgebraD.augmentationPower 2 :=
  Dyadic.GenuineFox.completed_initial completedABC completedABC_detector

def localXYZ : Fin 3 → LocalSource := ![Dyadic.ArithmeticPresentation.x,Dyadic.ArithmeticPresentation.y,Dyadic.ArithmeticPresentation.z]

theorem inverseWords_localXYZ :
    (fun i=>FreeGroup.lift localXYZ (Dyadic.GenuineFox.inverseWords i))=FiniteFreeProTwo.generator 3 := by
  funext i
  fin_cases i <;> simp [localXYZ,Dyadic.GenuineFox.inverseWords,Dyadic.ArithmeticPresentation.x,Dyadic.ArithmeticPresentation.y,Dyadic.ArithmeticPresentation.z]

theorem completedRelation_local : completionMap localXYZ completedRelation=genuineRelation := by
  rw [completedRelation,completionMap_substitution,inverseWords_localXYZ]
  exact completedLift_map 3 genuineRelation

def globalXYZ : Fin 3 → GlobalSource := fun i=>toSigmaFree (localXYZ i)

def completedGlobalXYZ : Fin 3 → CompletedWords (Fin 7) :=
  fun i=>completedLift 7 (globalXYZ i)

@[simp] theorem completedGlobalXYZ_map (i : Fin 3) :
    completionMap (FiniteFreeProTwo.generator 7) (completedGlobalXYZ i)=globalXYZ i :=
  completedLift_map 7 (globalXYZ i)

/-- The global completed word is defined by actual completed substitution. -/
def completedGlobalRelation : CompletedWords (Fin 7) :=
  completedGeneratorSubstitution completedGlobalXYZ completedRelation

theorem completedGlobalRelation_free :
    completionMap (FiniteFreeProTwo.generator 7) completedGlobalRelation=
      toSigmaFree genuineRelation := by
  rw [completedGlobalRelation,completionMap_generatorSubstitution]
  simp only [completedGlobalXYZ_map]
  change completionMap (fun i=>toSigmaFree (localXYZ i)) completedRelation=_
  rw [←completionMap_comp_continuous localXYZ toSigmaFree,completedRelation_local]

/-- This is an actual relation in the global arithmetic group. -/
theorem completedGlobalRelation_killed :
    sigmaFreeMap (completionMap (FiniteFreeProTwo.generator 7) completedGlobalRelation)=1 := by
  rw [completedGlobalRelation_free]
  exact genuineRelation_mem_global_kernel

/-- Every finite global quotient admits ordinary generator words with the
same full affine evaluations and hence the exact same global relation row. -/
theorem exists_literal_global_row
    (P : Type) [Group P] [Finite P] (generators : Fin 7 → P) :
    ∃words : Fin 3 → FreeGroup (Fin 7),
      (∀i,FreeGroup.lift generators (words i)=
        completedWordEvaluation P generators (completedGlobalXYZ i)) ∧
      completedFoxDerivative P generators completedGlobalRelation=
        completedFoxDerivative P generators (completedSubstitution words completedRelation) := by
  obtain ⟨words,hw⟩ := exists_literal_affine_lifts P generators completedGlobalXYZ
  exact ⟨words,literal_affine_lifts_evaluation P generators completedGlobalXYZ words hw,
    completedGeneratorSubstitution_derivative_eq P generators completedGlobalXYZ words hw
      completedRelation⟩

end UnitDistance.SigmaDyadic
