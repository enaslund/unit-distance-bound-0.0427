module

public import UnitDistance.GroupAugmentationFoxPresentation
public import UnitDistance.GroupAugmentationHilbertShift

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual local-to-global Fox coefficient maps

A family of actual global words induces its actual Fox matrix. This matrix
preserves the augmentation filtration, commutes with the augmentation maps,
and sends actual local relation rows to the derivatives of the substituted
words. No injectivity or inverse coordinate change is postulated here.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable (R G : Type*) [CommRing R] [Group G]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (generators : ι → G) (words : κ → FreeGroup ι)

/-- The actual local-to-global Fox matrix, linear over the target algebra. -/
def foxSubstitutionAlgebra : (κ → A R G) →ₗ[A R G] (ι → A R G) where
  toFun a i := ∑ j, a j * foxDerivative R G generators (words j) i
  map_add' a b := by ext i; simp [add_mul,Finset.sum_add_distrib]
  map_smul' a b := by ext i; simp [smul_eq_mul,mul_assoc,Finset.mul_sum]

/-- Scalar restriction of the actual Fox matrix. -/
def foxSubstitution : (κ → A R G) →ₗ[R] (ι → A R G) :=
  (foxSubstitutionAlgebra R G generators words).restrictScalars R

@[simp] theorem foxSubstitution_apply (a : κ → A R G) (i : ι) :
    foxSubstitution R G generators words a i =
      ∑ j, a j * foxDerivative R G generators (words j) i := rfl

/-- The matrix preserves every actual coefficient augmentation power. -/
theorem foxSubstitution_filtered (n : ℕ) :
    (coefficientPower R G (ι := κ) n).map (foxSubstitution R G generators words) ≤
      coefficientPower R G (ι := ι) n := by
  rintro a ⟨b,hb,rfl⟩
  apply (mem_coefficientPower R G n _).mpr
  intro i
  apply Submodule.sum_mem
  intro j _
  exact mul_mem_right R G n _ _ ((mem_coefficientPower R G n b).mp hb j)

/-- The chain map identity follows from the fundamental Fox identity. -/
theorem foxMap_foxSubstitution (a : κ → A R G) :
    foxMap R G generators (foxSubstitution R G generators words a) =
      foxMap R G (fun j => FreeGroup.lift generators (words j)) a := by
  change (∑ i, (∑ j, a j * foxDerivative R G generators (words j) i) *
    (delta R (generators i)-1)) = _
  simp only [Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  change (∑ j, a j * foxMap R G generators (foxDerivative R G generators (words j))) = _
  simp only [foxDerivative_fundamental]
  rfl

/-- Actual local augmentation-kernel vectors map into the actual global
augmentation kernel. -/
theorem foxSubstitution_kernel_le :
    ((foxMap R G (fun j => FreeGroup.lift generators (words j))).ker).map
      (foxSubstitution R G generators words) ≤ (foxMap R G generators).ker := by
  rintro a ⟨b,hb,rfl⟩
  rw [LinearMap.mem_ker,foxMap_foxSubstitution]
  exact hb

/-- Actual word evaluation commutes with literal substitution. -/
theorem lift_substitution (w : FreeGroup κ) :
    FreeGroup.lift generators (FreeGroup.lift words w) =
      FreeGroup.lift (fun j => FreeGroup.lift generators (words j)) w := by
  have he : (FreeGroup.lift generators).comp (FreeGroup.lift words) =
      FreeGroup.lift (fun j => FreeGroup.lift generators (words j)) := by
    apply FreeGroup.ext_hom
    intro j
    simp
  exact DFunLike.congr_fun he w

/-- The evaluated chain rule for arbitrary actual local words. -/
theorem foxDerivative_substitution (w : FreeGroup κ) :
    foxDerivative R G generators (FreeGroup.lift words w) =
      foxSubstitution R G generators words
        (foxDerivative R G (fun j => FreeGroup.lift generators (words j)) w) := by
  classical
  induction w using FreeGroup.induction_on with
  | one => simp
  | of j =>
    ext i
    simp [foxSubstitution_apply,Pi.single_apply]
  | inv_of j hj =>
    ext i
    simp only [map_inv,foxDerivative_inv,lift_substitution,foxSubstitution_apply,
      neg_mul,Finset.sum_neg_distrib,mul_assoc,← Finset.mul_sum]
    rw [← foxSubstitution_apply,← hj]
  | mul u v hu hv =>
    ext i
    simp only [map_mul,foxDerivative_mul,lift_substitution,foxSubstitution_apply,
      add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]
    rw [← foxSubstitution_apply,← foxSubstitution_apply,← hu,← hv]

end UnitDistance.GroupAugmentation
