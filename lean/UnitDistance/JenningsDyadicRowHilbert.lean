module

public import UnitDistance.GroupAugmentationRowHilbert
public import UnitDistance.JenningsInducedKernelHilbert

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual normalized induced dyadic common-row cost

The actual local annihilator is the one-dimensional degree-seven socle.
The proved filtered induction transports its Hilbert value exactly, while
strictness places the full row in the actual shifted ambient derivative
module. This gives the optimized common-row cost with no cost hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
open FilteredHilbert Dyadic

/-- The actual local row annihilator has its certified one-dimensional
socle filtration, including every higher-order coefficient perturbation. -/
theorem dyadic_rowKernelPower_finrank (c : Fin 3 → AlgebraD)
    (hc : ∀ i, c i-AlgebraD.linearFoxCoefficients i ∈ AlgebraD.augmentationPower 2) (n : ℕ) :
    Module.finrank F ↥(rowKernelPower D c n) = if n ≤ 7 then 1 else 0 := by
  have hk : (coefficientRow F D c).ker = power F D 7 := by
    rw [dyadic_coefficientRow,AlgebraD.foxRow_kernel c hc,dyadic_power]
  by_cases hn : n ≤ 7
  · rw [if_pos hn]
    have he : rowKernelPower D c n = power F D 7 := by
      rw [rowKernelPower,hk,inf_eq_left.mpr (power_antitone F D hn)]
    rw [congrArg (fun S : Submodule F (A F D) => Module.finrank F S) he,finrank_dyadic_power]
    exact AlgebraD.augmentation_dimensions 7
  · rw [if_neg hn]
    have he : rowKernelPower D c n = ⊥ := by
      rw [rowKernelPower,dyadic_power,AlgebraD.augmentation_nilpotent n (by omega),inf_bot_eq]
    rw [congrArg (fun S : Submodule F (A F D) => Module.finrank F S) he,finrank_bot]

/-- The actual dyadic annihilator Hilbert value is precisely `t^7`. -/
theorem value_dyadic_rowKernel (c : Fin 3 → AlgebraD)
    (hc : ∀ i, c i-AlgebraD.linearFoxCoefficients i ∈ AlgebraD.augmentationPower 2) (x : ℝ) :
    value F (A F D) (rowKernelPower D c) (Nat.card D) x = x^7 := by
  unfold value
  rw [Finset.sum_eq_single 7]
  · rw [dyadic_rowKernelPower_finrank c hc 7,dyadic_rowKernelPower_finrank c hc 8]
    norm_num
  · intro n _ hn
    rw [dyadic_rowKernelPower_finrank c hc n,dyadic_rowKernelPower_finrank c hc (n+1)]
    by_cases hn7 : n ≤ 7
    · have hns : n+1 ≤ 7 := by omega
      simp [hn7,hns]
    · have hns : ¬ n+1 ≤ 7 := by omega
      simp [hn7,hns]
  · intro h
    norm_num [Nat.card_eq_fintype_card,D.card] at h

variable (P : Type*) [Group P] [Finite P] (hP : IsPGroup 2 P)
variable (f : D →* P)
variable (hfirst : Function.Injective (layerMap F D f 1))
variable (hsecond : Function.Injective (layerMap F D f 2))

include hP hfirst hsecond in
/-- The actual induced dyadic common row has exactly the optimized cost
`t²(1-t⁷/P_D)H_A` in the ambient shifted derivative module. The separate
assertion that this row lies in specified global relation blocks is not
assumed or inferred here. -/
theorem dyadic_induced_row_cost (c : Fin 3 → AlgebraD)
    (hc : ∀ i, c i-AlgebraD.linearFoxCoefficients i ∈ AlgebraD.augmentationPower 2)
    (x : ℝ) (hx : 0 ≤ x) :
    value F (Fin 3 → A F P)
      (fun n => (coefficientRow F P (fun i => induced F D f (c i))).range ⊓ shiftedFoxCoefficientPower P n)
      (Nat.card P+1) x =
      x^2*(1-x^7/((1+x)^3*(1+x^2)^2))*
        Polynomial.eval₂ (Nat.castRingHom ℝ) x (hilbertPolynomial P) := by
  have hcoeff : ∀ i, c i ∈ power F D 1 := by
    intro i
    rw [dyadic_power,AlgebraD.augmentationPower_one]
    exact AlgebraD.augmentation_fox_coefficient c hc i
  have hstrict : ∀ n, rowImagePower F D c n =
      (coefficientRow F D c).range ⊓ coefficientPower F D (ι := Fin 3) (n+1) := by
    intro n
    rw [dyadic_rowImagePower,dyadic_coefficientRow,dyadic_coefficientPower]
    exact AlgebraD.foxImageFiltration_eq_induced_all c hc n
  have he := value_induced_row D P (DyadicComplementChoices P f hfirst hsecond) f
    (dyadicFilteredCoordinates P f hfirst hsecond hP)
    (dyadicComplementWeight P f hfirst hsecond hP)
    (dyadicFilteredCoordinates_mul P f hfirst hsecond hP)
    (filteredCoordinates_mem_power_iff D P f (dyadic_layer_injections P f hfirst hsecond)
      dyadic_isTwoGroup hP) c dyadic_isTwoGroup hP hcoeff hstrict x
  rw [value_dyadic_rowKernel c hc] at he
  have hs : (∑ t : DyadicComplementChoices P f hfirst hsecond,
      x^(dyadicComplementWeight P f hfirst hsecond hP t)) =
      Polynomial.eval₂ (Nat.castRingHom ℝ) x (hilbertPolynomial P) / ((1+x)^3*(1+x^2)^2) := by
    change (∑ t : ComplementChoices D P f (dyadic_layer_injections P f hfirst hsecond),
      x^(complementWeight D P f (dyadic_layer_injections P f hfirst hsecond) hP t)) = _
    rw [← shiftPolynomial_eval D P f (dyadic_layer_injections P f hfirst hsecond) hP]
    exact dyadic_shiftPolynomial_eval P hP f hfirst hsecond x hx
  rw [he,hs]
  ring

end UnitDistance.GroupAugmentation
