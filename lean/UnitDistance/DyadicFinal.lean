module

public import UnitDistance.DyadicCertificates
public import UnitDistance.DyadicHilbert

@[expose] public section
set_option backward.privateInPublic true


/-!
# Certified finite dyadic Hilbert polynomial

Unconditional finite-group-algebra conclusions, attached to the actual
augmentation ideal. No identification with a local Galois group or an
infinite pro-2 tower is asserted.
-/

noncomputable section

namespace UnitDistance.Dyadic.AlgebraD

theorem augmentation_dimensions :
    ∀ i : Fin 9, Module.finrank F (augmentationPower i.val) = dimensions i := by
  intro i
  fin_cases i
  · exact finrank_augmentationPower_zero
  · exact (finrank_augmentationPower_eq 1).trans Filtration.finrank_stage_1
  · exact (finrank_augmentationPower_eq 2).trans Filtration.finrank_stage_2
  · exact (finrank_augmentationPower_eq 3).trans Filtration.finrank_stage_3
  · exact (finrank_augmentationPower_eq 4).trans Filtration.finrank_stage_4
  · exact (finrank_augmentationPower_eq 5).trans Filtration.finrank_stage_5
  · exact (finrank_augmentationPower_eq 6).trans Filtration.finrank_stage_6
  · exact (finrank_augmentationPower_eq 7).trans Filtration.finrank_stage_7
  · exact (finrank_augmentationPower_eq 8).trans Filtration.finrank_stage_8

theorem augmentation_eighth_eq_bot : augmentationPower 8 = ⊥ := by
  rw [← stage_eq_augmentationPower]
  apply Submodule.map_injective_of_injective
    (f := Filtration.coefficients.toLinearMap) Filtration.coefficients.injective
  rw [coefficients_stage, Filtration.stage_eight_eq_bot, Submodule.map_bot]

theorem augmentation_nilpotent (n : ℕ) (hn : 8 ≤ n) :
    augmentationPower n = ⊥ :=
  augmentationPower_vanishes augmentation_eighth_eq_bot hn

theorem hilbert_polynomial :
    hilbertPolynomial = (1 + Polynomial.X) ^ 3 * (1 + Polynomial.X ^ 2) ^ 2 :=
  hilbertPolynomial_of_dimensions augmentation_dimensions

theorem socle_degree_seven :
    augmentationPower 7 = Submodule.span F {normSum} ∧ normSum ≠ 0 := by
  constructor
  · rw [seventh_power_eq_socle_of_dimensions (augmentation_dimensions 7)
      augmentation_eighth_eq_bot, socle_eq_span]
  · exact normSum_ne_zero

end UnitDistance.Dyadic.AlgebraD
