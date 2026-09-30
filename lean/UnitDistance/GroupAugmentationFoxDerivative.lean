module

public import UnitDistance.GroupAugmentationGenerators
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.SemidirectProduct

@[expose] public section
set_option backward.privateInPublic true


/-!
# Evaluated Fox derivatives on the actual free group

The derivative is constructed using the free group universal property and
an explicit semidirect product. Its values are vectors in the actual group
algebra, with the multiplication and inverse rules following from the group
law. In particular the fundamental augmentation identity is proved for
every actual free-group word.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (R G : Type*) [CommRing R] [Group G]
variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq ι

/-- Left translation by an actual group element on coefficient vectors. -/
def foxTranslate (g : G) : MulAut (Multiplicative (ι → A R G)) where
  toFun a := Multiplicative.ofAdd (fun i => delta R g * a.toAdd i)
  invFun a := Multiplicative.ofAdd (fun i => delta R g⁻¹ * a.toAdd i)
  left_inv a := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [← mul_assoc]
  right_inv a := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [← mul_assoc]
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext i
    exact mul_add _ _ _

/-- The actual regular action on the additive coefficient-vector group. -/
def foxAction : G →* MulAut (Multiplicative (ι → A R G)) where
  toFun := foxTranslate R G
  map_one' := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    funext i
    simp [foxTranslate]
  map_mul' g h := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    funext i
    simp [foxTranslate,← delta_mul,mul_assoc]

/-- The affine group carrying both word evaluation and evaluated derivative. -/
abbrev FoxAffine :=
  SemidirectProduct (Multiplicative (ι → A R G)) G (foxAction R G)

variable (generators : ι → G)

/-- An actual free-group homomorphism records evaluation and derivative
simultaneously, so reduced-word choices never enter the definition. -/
def foxLift : FreeGroup ι →* FoxAffine R G (ι := ι) := by
  classical
  exact FreeGroup.lift (fun i => ⟨Multiplicative.ofAdd (Pi.single i 1), generators i⟩)

/-- The evaluated Fox derivative, with left coefficients. -/
def foxDerivative (w : FreeGroup ι) : ι → A R G :=
  (foxLift R G generators w).left.toAdd

theorem foxLift_right (w : FreeGroup ι) :
    (foxLift R G generators w).right = FreeGroup.lift generators w := by
  have he : SemidirectProduct.rightHom.comp (foxLift R G generators) =
      FreeGroup.lift generators := by
    apply FreeGroup.ext_hom
    intro i
    simp [foxLift]
  exact DFunLike.congr_fun he w

@[simp] theorem foxDerivative_one : foxDerivative R G generators 1 = 0 := by
  simp [foxDerivative]

@[simp] theorem foxDerivative_of (i : ι) :
    foxDerivative R G generators (FreeGroup.of i) = Pi.single i 1 := by
  classical
  simp [foxDerivative,foxLift]

/-- The actual crossed product rule. -/
theorem foxDerivative_mul (u v : FreeGroup ι) (i : ι) :
    foxDerivative R G generators (u*v) i = foxDerivative R G generators u i +
      delta R (FreeGroup.lift generators u) * foxDerivative R G generators v i := by
  simp [foxDerivative,map_mul,foxAction,foxTranslate,foxLift_right]

/-- The actual inverse rule. -/
theorem foxDerivative_inv (u : FreeGroup ι) (i : ι) :
    foxDerivative R G generators u⁻¹ i =
      -(delta R (FreeGroup.lift generators u)⁻¹ * foxDerivative R G generators u i) := by
  simp [foxDerivative,map_inv,foxAction,foxTranslate,foxLift_right]

variable [Fintype ι]

/-- Fox's fundamental identity in the actual target group algebra. -/
theorem foxDerivative_fundamental (w : FreeGroup ι) :
    foxMap R G generators (foxDerivative R G generators w) =
      delta R (FreeGroup.lift generators w) - 1 := by
  classical
  induction w using FreeGroup.induction_on with
  | one => simp [foxMap]
  | of i => simp [foxMap,Pi.single_apply]
  | inv_of i hi =>
    change (∑ j, foxDerivative R G generators (FreeGroup.of i) j * (delta R (generators j)-1)) = _ at hi
    change (∑ j, foxDerivative R G generators (FreeGroup.of i)⁻¹ j * (delta R (generators j)-1)) = _
    simp only [foxDerivative_inv,neg_mul,Finset.sum_neg_distrib,mul_assoc,
      ← Finset.mul_sum]
    rw [hi]
    simp [mul_sub]
  | mul u v hu hv =>
    change (∑ j, foxDerivative R G generators u j * (delta R (generators j)-1)) = _ at hu
    change (∑ j, foxDerivative R G generators v j * (delta R (generators j)-1)) = _ at hv
    change (∑ j, foxDerivative R G generators (u*v) j * (delta R (generators j)-1)) = _
    simp only [foxDerivative_mul,add_mul,Finset.sum_add_distrib,mul_assoc,
      ← Finset.mul_sum]
    rw [hu,hv]
    simp only [map_mul,← delta_mul]
    noncomm_ring

/-- Every actual kernel word supplies an actual Fox-kernel row. -/
theorem foxDerivative_mem_ker (w : FreeGroup ι) (hw : FreeGroup.lift generators w = 1) :
    foxDerivative R G generators w ∈ (foxMap R G generators).ker := by
  rw [LinearMap.mem_ker,foxDerivative_fundamental,hw]
  simp

end UnitDistance.GroupAugmentation
