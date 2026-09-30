module

public import UnitDistance.GroupAugmentationFoxSubstitution
public import UnitDistance.GroupAugmentationCoefficientInjection

@[expose] public section
set_option backward.privateInPublic true


/-!
# Elementary group characters certify actual strict Fox coordinates

Separating characters on the local generators explicitly construct a left
inverse to the local Fox matrix after augmentation. Thus ordinary genus
characters can certify the required global coordinate injection; an assumed
free pro-2 basis change is unnecessary.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
local notation "F" => ZMod 2
variable (P : Type*) [Group P]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
variable (generators : ι → P)

/-- The augmented Fox derivative evaluates every elementary additive
character on the actual word value. -/
theorem foxDerivative_character (χ : P →* Multiplicative F) (w : FreeGroup ι) :
    ∑ i, augmentation F P (foxDerivative F P generators w i) * (χ (generators i)).toAdd =
      (χ (FreeGroup.lift generators w)).toAdd := by
  classical
  induction w using FreeGroup.induction_on with
  | one => simp
  | of j => simp [Pi.single_apply]
  | inv_of j hj =>
    simp only [foxDerivative_inv,map_neg,map_mul,map_inv,augmentation_delta,
      one_mul,neg_mul,Finset.sum_neg_distrib]
    rw [hj]
    rfl
  | mul u v hu hv =>
    simp only [foxDerivative_mul,map_add,map_mul,augmentation_delta,one_mul,
      add_mul,Finset.sum_add_distrib]
    rw [hu,hv]
    rfl

/-- The reverse coefficient matrix formed from actual elementary characters. -/
def characterFoxRetraction (characters : κ → P →* Multiplicative F) :
    (ι → A F P) →ₗ[A F P] (κ → A F P) where
  toFun a k := ∑ i, a i * ((characters k (generators i)).toAdd • (1 : A F P))
  map_add' a b := by ext k; simp [add_mul,Finset.sum_add_distrib]
  map_smul' a b := by ext k; simp [smul_eq_mul,mul_assoc,Finset.mul_sum]

/-- Augmentation of the explicit reverse matrix is the elementary character
pairing with the actual Fox row. -/
theorem characterFoxRetraction_foxDerivative
    (characters : κ → P →* Multiplicative F) (w : FreeGroup ι) (k : κ) :
    augmentation F P
      (characterFoxRetraction P generators characters (foxDerivative F P generators w) k) =
      (characters k (FreeGroup.lift generators w)).toAdd := by
  change augmentation F P (∑ i, foxDerivative F P generators w i *
    ((characters k (generators i)).toAdd • (1 : A F P))) = _
  simp only [map_sum,map_mul,map_smul,map_one,smul_eq_mul,mul_one]
  exact foxDerivative_character P generators (characters k) w

/-- Actual separating elementary characters give an actual left inverse
after augmentation for the local-to-global Fox matrix. -/
theorem characterFoxRetraction_left
    (words : κ → FreeGroup ι) (characters : κ → P →* Multiplicative F)
    (hcharacters : ∀ j k, (characters k (FreeGroup.lift generators (words j))).toAdd =
      (Pi.single j (1 : F) : κ → F) k) (j k : κ) :
    augmentation F P
      (characterFoxRetraction P generators characters
        (foxSubstitutionAlgebra F P generators words (Pi.single j 1)) k) =
      augmentation F P ((Pi.single j (1 : A F P) : κ → A F P) k) := by
  have hrow : foxSubstitutionAlgebra F P generators words (Pi.single j 1) =
      foxDerivative F P generators (words j) := by
    ext i
    simp [foxSubstitutionAlgebra,Pi.single_apply]
  rw [hrow,characterFoxRetraction_foxDerivative,hcharacters]
  simp [Pi.single_apply]

variable [Finite P]

/-- The actual Fox matrix is injective whenever elementary characters
separate its local generator values. -/
theorem foxSubstitution_injective_of_characters (hP : IsPGroup 2 P)
    (words : κ → FreeGroup ι) (characters : κ → P →* Multiplicative F)
    (hcharacters : ∀ j k, (characters k (FreeGroup.lift generators (words j))).toAdd =
      (Pi.single j (1 : F) : κ → F) k) :
    Function.Injective (foxSubstitution F P generators words) := by
  exact coefficientLinearMap_injective P hP (foxSubstitutionAlgebra F P generators words)
    (characterFoxRetraction P generators characters)
    (characterFoxRetraction_left P generators words characters hcharacters)

end UnitDistance.GroupAugmentation
