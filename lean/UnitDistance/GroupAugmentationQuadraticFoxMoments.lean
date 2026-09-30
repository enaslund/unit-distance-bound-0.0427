module

public import UnitDistance.GroupAugmentationMoments
public import UnitDistance.FreeThreeQuadraticTensor

@[expose] public section
set_option backward.privateInPublic true


/-! The actual quadratic detector governs all binary-character moments of
Fox derivatives, for any actual target group and any three generators. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace UnitDistance.GroupAugmentation
open scoped BigOperators
open ClassTwo
variable {G : Type*} [Group G] (generators : Fin 3 → G)
local notation "F" => ZMod 2

theorem quadratic_fox_augmentation (w : FreeGroup (Fin 3)) (i : Fin 3) :
    augmentation F G (foxDerivative F G generators w i)=
      (FreeThreeQuadratic.wordDetector w).base i := by
  have hn : ∀a : F,-a=a := by decide +kernel
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k =>
    rw [foxDerivative_of,FreeThreeQuadratic.wordDetector_of]
    simp only [FreeThreeQuadratic.basis]
    by_cases h : k=i <;> simp [Pi.single_apply,h]
  | inv_of k hk =>
    rw [foxDerivative_inv,map_neg,map_mul,augmentation_delta,one_mul,hk,map_inv]
    rfl
  | mul u v hu hv =>
    rw [foxDerivative_mul,map_add,map_mul,augmentation_delta,one_mul,hu,hv,map_mul]
    rfl

theorem quadratic_word_character (χ : G →* Multiplicative F) (w : FreeGroup (Fin 3)) :
    (χ (FreeGroup.lift generators w)).toAdd=
      ∑k,(χ (generators k)).toAdd*(FreeThreeQuadratic.wordDetector w).base k := by
  rw [←foxDerivative_character G generators χ w]
  apply Finset.sum_congr rfl
  intro k hk
  rw [quadratic_fox_augmentation,mul_comm]

theorem quadratic_fox_moment (χ : G →* Multiplicative F)
    (w : FreeGroup (Fin 3)) (i : Fin 3) :
    moment χ (foxDerivative F G generators w i)=
      ∑k,(χ (generators k)).toAdd*FreeThreeQuadratic.second (FreeThreeQuadratic.wordDetector w) k i := by
  induction w using FreeGroup.induction_on with
  | one => simp [FreeThreeQuadratic.second_one]
  | of j =>
    rw [foxDerivative_of,FreeThreeQuadratic.wordDetector_of]
    simp only [FreeThreeQuadratic.second_basis,mul_zero,Finset.sum_const_zero]
    by_cases h : j=i <;> simp [Pi.single_apply,h]
  | inv_of j hj =>
    have hn : ∀a : F,-a=a := by decide +kernel
    have hneg (a : Multiplicative F) : (a⁻¹).toAdd= -a.toAdd := rfl
    rw [foxDerivative_inv,foxDerivative_of,map_inv,FreeThreeQuadratic.wordDetector_of]
    simp only [FreeThreeQuadratic.second_inv_basis,FreeGroup.lift_apply_of]
    by_cases h : j=i
    · subst i
      simp only [Pi.single_eq_same,mul_one,map_neg,moment_delta,map_inv,hneg,hn]
      simp [Pi.single_apply]
    · simp [Pi.single_apply,h]
  | mul u v hu hv =>
    rw [foxDerivative_mul,map_add,moment_mul,augmentation_delta,one_mul,moment_delta,
      quadratic_fox_augmentation,quadratic_word_character,map_mul,hu,hv]
    simp only [FreeThreeQuadratic.second_mul,mul_add,Finset.sum_add_distrib,
      ←mul_assoc,←Finset.sum_mul]
    ring

end UnitDistance.GroupAugmentation
