module

public import UnitDistance.GroupAugmentationQuadraticFoxMoments
public import UnitDistance.DyadicFirstOrder
public import UnitDistance.DyadicFox
public import UnitDistance.GroupAugmentationCompletedSubstitution
public import UnitDistance.FreeThreeDyadicQuotient

@[expose] public section
set_option backward.privateInPublic true


/-! The genuine arithmetic quadratic initial yields the exact dyadic Fox
row after the actual change from a,b,c to x=b,y=a,z=a*c. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace UnitDistance.Dyadic.GenuineFox
open GroupAugmentation FirstOrder
open scoped BigOperators

def inverseWords : Fin 3 → FreeGroup (Fin 3) :=
  ![FreeGroup.of 1,FreeGroup.of 0,(FreeGroup.of 1)⁻¹*FreeGroup.of 2]

def inverseValues : Fin 3 → D := fun i=>FreeGroup.lift Filtration.gen (inverseWords i)

theorem inverseValues_eq : inverseValues=![D.y,D.x,D.y⁻¹*D.z] := by
  funext i
  fin_cases i <;> simp [inverseValues,inverseWords,Filtration.gen]

theorem inverse_row (c : Fin 3 → AlgebraD) :
    foxSubstitution F D Filtration.gen inverseWords c=
      ![c 1,c 0-c 2*delta F D.y⁻¹,c 2*delta F D.y⁻¹] := by
  funext i
  fin_cases i <;>
    simp [foxSubstitution_apply,Fin.sum_univ_succ,inverseWords,foxDerivative_mul,
      foxDerivative_inv,foxDerivative_of,Filtration.gen,Pi.single_apply,sub_eq_add_neg]

def sourceMoment (j i : Fin 3) : F :=
  ∑k,(character j (inverseValues k)).toAdd*FreeThreeQuadratic.second FreeThreeQuadratic.relation k i

theorem sourceMoment_table : ∀j i,sourceMoment j i=
    ![![0,0,1],![1,1,0],![0,1,0]] j i := by decide +kernel

theorem linear_moment_table : ∀j i,
    moment (character j) (AlgebraD.linearFoxCoefficients i)=
      ![![0,1,1],![1,1,0],![1,0,0]] j i := by
  intro j i
  fin_cases i
  · change moment (character j) ((AlgebraD.delta D.y-1)+(AlgebraD.delta D.z-1))=_
    simp only [map_add,map_sub,←dyadic_delta,moment_delta,moment_one,sub_zero]
    have h : ∀j : Fin 3,(character j D.y).toAdd+(character j D.z).toAdd=
        ![![0,1,1],![1,1,0],![1,0,0]] j 0 := by decide +kernel
    exact h j
  · change moment (character j) ((AlgebraD.delta D.y-1)+(AlgebraD.delta D.x-1))=_
    simp only [map_add,map_sub,←dyadic_delta,moment_delta,moment_one,sub_zero]
    have h : ∀j : Fin 3,(character j D.y).toAdd+(character j D.x).toAdd=
        ![![0,1,1],![1,1,0],![1,0,0]] j 1 := by decide +kernel
    exact h j
  · change moment (character j) (AlgebraD.delta D.x-1)=_
    simp only [map_sub,←dyadic_delta,moment_delta,moment_one,sub_zero]
    have h : ∀j : Fin 3,(character j D.x).toAdd=
        ![![0,1,1],![1,1,0],![1,0,0]] j 2 := by decide +kernel
    exact h j

theorem ordinary_initial (w : FreeGroup (Fin 3))
    (hw : FreeThreeQuadratic.wordDetector w=FreeThreeQuadratic.relation) (i : Fin 3) :
    foxDerivative F D Filtration.gen (FreeGroup.lift inverseWords w) i-
      AlgebraD.linearFoxCoefficients i∈AlgebraD.augmentationPower 2 := by
  let c : Fin 3 → AlgebraD := foxDerivative F D inverseValues w
  have hcaug (k : Fin 3) : augmentation F D (c k)=0 := by
    rw [quadratic_fox_augmentation,hw]
    rfl
  have hcmom (j k : Fin 3) : moment (character j) (c k)=sourceMoment j k := by
    rw [quadratic_fox_moment,hw]
    rfl
  have hrow : foxDerivative F D Filtration.gen (FreeGroup.lift inverseWords w)=
      ![c 1,c 0-c 2*delta F D.y⁻¹,c 2*delta F D.y⁻¹] := by
    rw [foxDerivative_substitution]
    exact inverse_row c
  rw [mem_power_two_iff]
  constructor
  · have hl : augmentation F D (AlgebraD.linearFoxCoefficients i)=0 := by
      rw [dyadic_augmentation]
      exact AlgebraD.augmentation_linearFox i
    rw [map_sub,hl,sub_zero,hrow]
    fin_cases i
    · exact hcaug 1
    · change augmentation F D (c 0-c 2*delta F D.y⁻¹)=0
      rw [map_sub,map_mul,hcaug,hcaug,zero_mul,sub_self]
    · change augmentation F D (c 2*delta F D.y⁻¹)=0
      rw [map_mul,hcaug,zero_mul]
  · intro j
    rw [map_sub,hrow,linear_moment_table]
    fin_cases i
    · change moment (character j) (c 1)-(![![0,1,1],![1,1,0],![1,0,0]] j 0)=0
      rw [hcmom,sourceMoment_table]
      have h : ∀j : Fin 3,(![![0,0,1],![1,1,0],![0,1,0]] j 1 : F)-
          ![![0,1,1],![1,1,0],![1,0,0]] j 0=0 := by decide +kernel
      exact h j
    · change moment (character j) (c 0-c 2*delta F D.y⁻¹)-
        (![![0,1,1],![1,1,0],![1,0,0]] j 1)=0
      simp only [map_sub,moment_mul,hcaug,augmentation_delta,zero_mul,one_mul,zero_add,hcmom,sourceMoment_table]
      have h : ∀j : Fin 3,((![![0,0,1],![1,1,0],![0,1,0]] j 0 : F)-
          ![![0,0,1],![1,1,0],![0,1,0]] j 2)-![![0,1,1],![1,1,0],![1,0,0]] j 1=0 := by decide +kernel
      exact h j
    · change moment (character j) (c 2*delta F D.y⁻¹)-
        (![![0,1,1],![1,1,0],![1,0,0]] j 2)=0
      simp only [moment_mul,hcaug,augmentation_delta,zero_mul,one_mul,zero_add,hcmom,sourceMoment_table]
      have h : ∀j : Fin 3,(![![0,0,1],![1,1,0],![0,1,0]] j 2 : F)-
          ![![0,1,1],![1,1,0],![1,0,0]] j 2=0 := by decide +kernel
      exact h j

theorem inverse_evaluation :
    (FreeGroup.lift Filtration.gen).comp (FreeGroup.lift inverseWords)=
      FreeThreeDyadicQuotient.quotient.comp FreeThreeQuadratic.wordDetector := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply,FreeGroup.lift_apply_of,FreeThreeQuadratic.wordDetector_of,
    FreeThreeDyadicQuotient.quotient_basis]
  change inverseValues i=_
  rw [inverseValues_eq]
  have h : ∀i : Fin 3,(![D.y,D.x,D.y⁻¹*D.z] i)=![D.y,D.x,D.y*D.z] i := by decide +kernel
  exact h i

/-- Actual completed relation: vanishing in D32 and the precise unreduced
linear Fox row follow from its independently computed quadratic image. -/
theorem completed_initial (r : CompletedWords (Fin 3))
    (hr : completedFiniteMap FreeThreeQuadratic.Q FreeThreeQuadratic.wordDetector r=
      FreeThreeQuadratic.relation) :
    completedWordEvaluation D Filtration.gen (completedSubstitution inverseWords r)=1 ∧
      ∀i,completedFoxDerivative D Filtration.gen (completedSubstitution inverseWords r) i-
        AlgebraD.linearFoxCoefficients i∈AlgebraD.augmentationPower 2 := by
  let f : FreeGroup (Fin 3) →* FoxAffine F D (ι := Fin 3) :=
    (foxLift F D Filtration.gen).comp (FreeGroup.lift inverseWords)
  obtain ⟨w,hqw,hfw⟩ := exists_word_matching_pair FreeThreeQuadratic.Q
    (FoxAffine F D (ι := Fin 3)) FreeThreeQuadratic.wordDetector f r
  have hw : FreeThreeQuadratic.wordDetector w=FreeThreeQuadratic.relation := hqw.trans hr
  change foxLift F D Filtration.gen (FreeGroup.lift inverseWords w)=
    completedFiniteMap (FoxAffine F D (ι := Fin 3))
      ((foxLift F D Filtration.gen).comp (FreeGroup.lift inverseWords)) r at hfw
  rw [←completedFiniteMap_substitution inverseWords] at hfw
  have hL := congrArg (fun a : FoxAffine F D (ι := Fin 3) => a.left.toAdd) hfw
  have hR := congrArg (fun a : FoxAffine F D (ι := Fin 3) => a.right) hfw
  change foxDerivative F D Filtration.gen (FreeGroup.lift inverseWords w)=
    completedFoxDerivative D Filtration.gen (completedSubstitution inverseWords r) at hL
  change (foxLift F D Filtration.gen (FreeGroup.lift inverseWords w)).right=
    completedWordEvaluation D Filtration.gen (completedSubstitution inverseWords r) at hR
  rw [foxLift_right] at hR
  have he := DFunLike.congr_fun inverse_evaluation w
  change FreeGroup.lift Filtration.gen (FreeGroup.lift inverseWords w)=
    FreeThreeDyadicQuotient.quotient (FreeThreeQuadratic.wordDetector w) at he
  rw [hw,FreeThreeDyadicQuotient.quotient_relation] at he
  refine ⟨hR.symm.trans he,?_⟩
  intro i
  rw [←hL]
  exact ordinary_initial w hw i

end UnitDistance.Dyadic.GenuineFox
