module

public import UnitDistance.FilteredHilbert
public import UnitDistance.GroupAugmentationGenerators
public import UnitDistance.GroupAugmentationHilbert

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual finite augmentation Fox kernel and its Hilbert value

The strict augmentation generator map identifies the Hilbert value of its
actual kernel. All filtrations here are actual augmentation powers and
induced subspace filtrations, before any presentation relators are supplied.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
open FilteredHilbert
variable (G : Type*) [Group G] [Finite G]
local notation "F" => ZMod 2

/-- Evaluation of the actual augmentation quotient Hilbert polynomial
agrees with the real dimension-difference definition. -/
theorem hilbertPolynomial_eval (t : ℝ) :
    Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial G) =
      value F (A F G) (power F G) (Nat.card G) t := by
  unfold hilbertPolynomial value
  simp only [Polynomial.eval₂_finsetSum,Polynomial.eval₂_monomial,finrank_powerLayer]
  apply Finset.sum_congr rfl
  intro n _
  change ((Module.finrank F ↥(power F G n) - Module.finrank F ↥(power F G (n+1)) : ℕ) : ℝ) * t^n = _
  rw [Nat.cast_sub (Submodule.finrank_mono (power_succ_le F G n))]

/-- The degree-zero augmentation quotient has dimension one. -/
theorem finrank_power_zero_sub_one :
    Module.finrank F ↥(power F G 0) = Module.finrank F ↥(power F G 1) + 1 := by
  have hs : Function.Surjective (augmentation F G).toLinearMap := by
    intro r
    exact ⟨r • (1 : A F G), by simp⟩
  have he := (augmentation F G).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs,finrank_top,Module.finrank_self] at he
  have h0 := congrArg (fun S : Submodule F (A F G) => Module.finrank F S) (power_zero F G)
  have h1 := congrArg (fun S : Submodule F (A F G) => Module.finrank F S) (power_one F G)
  rw [finrank_top] at h0
  rw [h0,h1]
  omega

variable {ι : Type*} [Fintype ι]

/-- The coefficient power is the product of the actual power subspaces. -/
def coefficientPowerEquiv (n : ℕ) :
    coefficientPower F G (ι := ι) n ≃ₗ[F] (ι → power F G n) where
  toFun a i := ⟨a.1 i, (mem_coefficientPower F G n a.1).mp a.2 i⟩
  invFun a := ⟨fun i => a i, (mem_coefficientPower F G n _).mpr (fun i => (a i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_coefficientPower (n : ℕ) :
    Module.finrank F ↥(coefficientPower F G (ι := ι) n) =
      Fintype.card ι * Module.finrank F ↥(power F G n) := by
  rw [(coefficientPowerEquiv G (ι := ι) n).finrank_eq,Module.finrank_pi_fintype]
  simp

theorem value_coefficientPower (N : ℕ) (t : ℝ) :
    value F (ι → A F G) (coefficientPower F G) N t =
      Fintype.card ι * value F (A F G) (power F G) N t := by
  unfold value
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [finrank_coefficientPower,Nat.cast_mul]
  ring

variable (generators : ι → G)

/-- The free generator module is shifted by one in the augmentation
sequence. Degree zero repeats degree one, so its Hilbert value has no
constant coefficient. -/
def shiftedFoxCoefficientPower (n : ℕ) : Submodule F (ι → A F G) :=
  coefficientPower F G (n-1)

/-- The actual kernel with the induced shifted augmentation filtration. -/
def foxKernelPower (n : ℕ) : Submodule F (ι → A F G) :=
  shiftedFoxCoefficientPower G n ⊓ (foxMap F G generators).ker

variable (hgen : Subgroup.closure (Set.range generators) = ⊤)
variable (hG : IsPGroup 2 G)

include hgen hG in
/-- The finite filtered Fox kernel has the exact Hilbert value used in the
weighted infinitude inequality. This uses actual group generation and the
proved strict augmentation map, with no relation-row spanning assumption. -/
theorem value_foxKernel (t : ℝ) :
    value F (ι → A F G) (foxKernelPower G generators) (Nat.card G+1) t =
      1 - (1 - (Fintype.card ι : ℝ)*t) *
        Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial G) := by
  have hN : power F G (Nat.card G) = ⊥ := power_card_eq_bot G 2 hG
  have hN1 : power F G (Nat.card G+1) = ⊥ :=
    le_bot_iff.mp ((power_succ_le F G (Nat.card G)).trans hN.le)
  have he := value_map_add_kernel F (ι → A F G) (A F G)
    (shiftedFoxCoefficientPower G) (foxMap F G generators) (Nat.card G+1) t
  have hsource : value F (ι → A F G) (shiftedFoxCoefficientPower G) (Nat.card G+1) t =
      t * (Fintype.card ι : ℝ) * value F (A F G) (power F G) (Nat.card G) t := by
    change value F (ι → A F G) (fun n => coefficientPower F G (n-1)) _ t = _
    rw [value_shift,value_coefficientPower]
    ring
  have himage : value F (A F G)
      (fun n => (shiftedFoxCoefficientPower G n).map (foxMap F G generators))
      (Nat.card G+1) t = value F (A F G) (power F G) (Nat.card G) t - 1 := by
    have hm (n : ℕ) : (shiftedFoxCoefficientPower G n).map (foxMap F G generators) =
        power F G ((n-1)+1) := foxMap_strict F G generators hgen (n-1)
    simp_rw [hm]
    rw [value_shift F (A F G) (fun n => power F G (n+1))]
    have hv := value_succ F (A F G) (power F G) (Nat.card G) t
    rw [value_extend F (A F G) (power F G) (Nat.card G) hN hN1] at hv
    have hd : (Module.finrank F ↥(power F G 0) : ℝ) -
        Module.finrank F ↥(power F G 1) = 1 := by
      have hh := finrank_power_zero_sub_one G
      exact_mod_cast (show (Module.finrank F ↥(power F G 0) : ℤ) -
        Module.finrank F ↥(power F G 1) = 1 by omega)
    rw [hd] at hv
    linarith
  change _ + value F (ι → A F G) (foxKernelPower G generators) _ t = _ at he
  rw [hsource,himage] at he
  rw [hilbertPolynomial_eval]
  nlinarith [he]

end UnitDistance.GroupAugmentation
