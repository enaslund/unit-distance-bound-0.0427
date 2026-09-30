module

public import UnitDistance.GroupAugmentationFoxHilbert
public import UnitDistance.GroupAugmentationFilteredRows

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual augmentation shifts and row costs

A row whose actual coefficients lie in augmentation degree `s-1` induces
an actual filtered map from the group algebra shifted by `s`. The general
finite filtered surjection inequality therefore bounds its actual induced
row-image Hilbert value by `t^s H_A(t)`.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
open FilteredHilbert
variable (G : Type*) [Group G] [Finite G]
local notation "F" => ZMod 2
variable (hG : IsPGroup 2 G)

include hG in
theorem hilbert_power_vanishes_after_card (n : ℕ) (hn : Nat.card G ≤ n) : power F G n = ⊥ :=
  le_bot_iff.mp ((power_antitone F G hn).trans (power_card_eq_bot G 2 hG).le)

include hG in
theorem value_power_shift (s N : ℕ) (hN : Nat.card G+s ≤ N) (t : ℝ) :
    value F (A F G) (fun n => power F G (n-s)) N t =
      t^s * Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial G) := by
  have he : N = (N-s)+s := by omega
  conv_lhs => rw [he]
  rw [value_shift_add]
  rw [value_extend_of_le F (A F G) (power F G) (Nat.card G) (N-s) (by omega)
    (hilbert_power_vanishes_after_card G hG)]
  rw [hilbertPolynomial_eval]

variable {ι : Type*} [Fintype ι]

theorem coefficientPower_bot (n : ℕ) (hn : power F G n = ⊥) :
    coefficientPower F G (ι := ι) n = ⊥ := by
  ext a
  simp only [mem_coefficientPower,hn,Submodule.mem_bot]
  exact ⟨fun h => funext h,fun h i => congrFun h i⟩

theorem shiftedFoxCoefficientPower_antitone : Antitone (shiftedFoxCoefficientPower G (ι := ι)) :=
  fun _ _ h => by
    intro a ha
    exact (mem_coefficientPower F G _ _).mpr (fun i =>
      power_antitone F G (Nat.sub_le_sub_right h 1) ((mem_coefficientPower F G _ _).mp ha i))

@[simp] theorem shiftedFoxCoefficientPower_zero :
    shiftedFoxCoefficientPower G (ι := ι) 0 = ⊤ := by
  ext a
  simp [shiftedFoxCoefficientPower]

include hG in
theorem shiftedFoxCoefficientPower_nilpotent (n : ℕ) (hn : Nat.card G+1 ≤ n) :
    shiftedFoxCoefficientPower G (ι := ι) n = ⊥ :=
  coefficientPower_bot G (n-1) (hilbert_power_vanishes_after_card G hG (n-1) (by omega))

variable (generators : ι → G)

include hG in
theorem foxKernelPower_nilpotent (n : ℕ) (hn : Nat.card G+1 ≤ n) :
    foxKernelPower G generators n = ⊥ := by
  rw [foxKernelPower,shiftedFoxCoefficientPower_nilpotent G hG n hn,bot_inf_eq]

include hG in
theorem value_foxKernel_of_cutoff
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (N : ℕ) (hN : Nat.card G+1 ≤ N) (t : ℝ) :
    value F (ι → A F G) (foxKernelPower G generators) N t =
      1 - (1-(Fintype.card ι : ℝ)*t)*
        Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial G) := by
  rw [value_extend_of_le F (ι → A F G) (foxKernelPower G generators) (Nat.card G+1) N hN
    (foxKernelPower_nilpotent G hG generators)]
  exact value_foxKernel G generators hgen hG t

include hG in
/-- An actual row with coefficients in `I^(s-1)` has at most the cost of
one shifted copy of the actual ambient algebra. -/
theorem value_row_le (c : ι → A F G) (s : ℕ) (hs : 1 ≤ s)
    (hc : ∀ i, c i ∈ power F G (s-1))
    (N : ℕ) (hN : Nat.card G+s ≤ N)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    value F (ι → A F G)
      (fun n => (coefficientRow F G c).range ⊓ shiftedFoxCoefficientPower G n) N t ≤
      t^s * Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial G) := by
  have hmap (n : ℕ) : (power F G (n-s)).map (coefficientRow F G c) ≤
      shiftedFoxCoefficientPower G n := by
    rintro a ⟨b,hb,rfl⟩
    apply (mem_coefficientPower F G (n-1) _).mpr
    intro i
    exact power_antitone F G (by omega : n-1 ≤ (n-s)+(s-1))
      (mul_mem_add F G hb (hc i))
  have he := value_induced_range_le F (A F G) (ι → A F G)
    (fun n => power F G (n-s)) (shiftedFoxCoefficientPower G)
    (fun _ _ h => power_antitone F G (Nat.sub_le_sub_right h s))
    (by simp) (shiftedFoxCoefficientPower_zero G)
    (coefficientRow F G c) hmap N
    (hilbert_power_vanishes_after_card G hG (N-s) (by omega))
    (shiftedFoxCoefficientPower_nilpotent G hG N (by omega)) t ht0 ht1
  rwa [value_power_shift G hG s N hN t] at he

end UnitDistance.GroupAugmentation
