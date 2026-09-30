module

public import UnitDistance.GroupAugmentationGlobalBlocks

@[expose] public section
set_option backward.privateInPublic true


/-!
# General actual local-kernel costs in global Fox coordinates

For every finite local 2-group with compatible actual augmentation layers,
the induced kernel and its global Fox image have the normalized local cost
computed from the local group's independently defined Hilbert polynomial.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
open FilteredHilbert
local notation "F" => ZMod 2
variable (D P : Type*) [Group D] [Group P] [Finite D] [Finite P]

/-- The actual group-algebra Hilbert polynomial has positive value on the
nonnegative axis; its augmentation quotient contributes the constant one. -/
theorem hilbertPolynomial_eval_pos (t : ℝ) (ht : 0 ≤ t) :
    0 < Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial D) := by
  rw [hilbertPolynomial_eval,value]
  have hnonneg (n : ℕ) :
      0 ≤ ((Module.finrank F ↥(power F D n) : ℝ) -
        Module.finrank F ↥(power F D (n+1))) * t^n := by
    apply mul_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast Submodule.finrank_mono (power_succ_le F D n))
    · exact pow_nonneg ht n
  have hzero : ((Module.finrank F ↥(power F D 0) : ℝ) -
      Module.finrank F ↥(power F D (0+1))) * t^0 = 1 := by
    have h : Module.finrank F ↥(power F D 0) =
        Module.finrank F ↥(power F D (0+1)) + 1 := by
      simpa only [Nat.zero_add] using finrank_power_zero_sub_one D
    norm_num only [pow_zero,mul_one]
    exact_mod_cast (show (Module.finrank F ↥(power F D 0) : ℤ) -
      Module.finrank F ↥(power F D (0+1)) = 1 by omega)
  have hcard : 0 < Nat.card D := Nat.card_pos
  have hh := Finset.single_le_sum (fun n (_ : n ∈ Finset.range (Nat.card D)) => hnonneg n)
    (show 0 ∈ Finset.range (Nat.card D) by simpa using hcard)
  rw [hzero] at hh
  linarith

variable (f : D →* P) (hinj : ∀ n, Function.Injective (layerMap F D f n))
variable (hD : IsPGroup 2 D) (hP : IsPGroup 2 P)
variable {κ : Type*} [Fintype κ]
variable (localGenerators : κ → D)

include hD hP hinj in
/-- The exact full induced local-kernel cost is derived from actual filtered
induction and its actual Hilbert polynomial. -/
theorem jennings_induced_kernel_cost
    (hgen : Subgroup.closure (Set.range localGenerators) = ⊤)
    (t : ℝ) (ht : 0 ≤ t) :
    value F (κ → A F P) (foxKernelPower P (fun j => f (localGenerators j))) (Nat.card P+1) t =
      ((Fintype.card κ : ℝ)*t-1+
        1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial D))*
        Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial P) := by
  have hi := jennings_induced_kernel_value D P f hinj hD hP localGenerators hgen t
  have hf := congrArg (Polynomial.eval₂ (Nat.castRingHom ℝ) t)
    (hilbertPolynomial_induction D P f hinj hD hP)
  rw [Polynomial.eval₂_mul] at hf
  have hs : Polynomial.eval₂ (Nat.castRingHom ℝ) t (shiftPolynomial D P f hinj hP) =
      Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial P) /
        Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial D) := by
    exact (eq_div_iff (ne_of_gt (hilbertPolynomial_eval_pos D t ht))).mpr hf.symm
  rw [hi,hs]
  ring

variable {ι : Type*} [Fintype ι]
variable (globalGenerators : ι → P) (words : κ → FreeGroup ι)

include hD hP hinj in
/-- The actual local kernel maps into global coordinates with at most the
exact local normalized cost. This applies uniformly to every odd, infinite,
and unramified-cap block of the arithmetic presentation. -/
theorem global_local_kernel_cost
    (hgen : Subgroup.closure (Set.range localGenerators) = ⊤)
    (hwords : ∀ j, FreeGroup.lift globalGenerators (words j) = f (localGenerators j))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    value F (ι → A F P)
      (fun n => globalFoxBlock P globalGenerators words ⊓ shiftedFoxCoefficientPower P n)
      (Nat.card P+1) t ≤
      ((Fintype.card κ : ℝ)*t-1+
        1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial D))*
        Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial P) := by
  have he := globalFoxBlock_value_le P globalGenerators words hP t ht0 ht1
  simp_rw [hwords] at he
  rw [jennings_induced_kernel_cost D P f hinj hD hP localGenerators hgen t ht0] at he
  exact he

end UnitDistance.GroupAugmentation
