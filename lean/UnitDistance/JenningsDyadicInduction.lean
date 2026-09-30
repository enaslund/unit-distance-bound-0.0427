module

public import UnitDistance.JenningsFilteredInduction
public import UnitDistance.GroupAugmentationFilteredRows
public import UnitDistance.DyadicFox

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual dyadic filtered freeness and strict induced Fox rows

Only the first two actual quotient-layer injections are required for the
specified order-32 group. All-degree strictness, the adapted ambient basis,
filtered right-module freeness and strictness of the induced actual row
image are proved consequences. Realizing these injections in the actual
global retained quotient is still a separate structural obligation.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
open Dyadic

theorem dyadic_isTwoGroup : IsPGroup 2 D := by
  apply IsPGroup.of_card (n := 5)
  rw [Nat.card_eq_fintype_card,D.card]
  norm_num

variable (P : Type*) [Group P]
variable (f : D →* P)
variable (hfirst : Function.Injective (layerMap F D f 1))
variable (hsecond : Function.Injective (layerMap F D f 2))

include hfirst hsecond in
/-- The first two concrete actual layer injections imply every actual
layer injection used in the subgroup-compatible Jennings construction. -/
theorem dyadic_layer_injections : ∀ n, Function.Injective (layerMap F D f n) := by
  apply layer_injections_of_comap_dimensionSubgroup_eq F D P f
  intro n
  rw [dyadic_comap_dimensionSubgroup f hfirst hsecond,← dyadic_dimensionSubgroup]

variable [Finite P] (hP : IsPGroup 2 P)

abbrev DyadicComplementChoices := ComplementChoices D P f (dyadic_layer_injections P f hfirst hsecond)

/-- The actual dyadic-to-ambient filtered right-module decomposition. -/
def dyadicFilteredCoordinates : A F P ≃ₗ[F] (DyadicComplementChoices P f hfirst hsecond →₀ AlgebraD) :=
  filteredCoordinates D P f (dyadic_layer_injections P f hfirst hsecond) dyadic_isTwoGroup hP

def dyadicComplementWeight : DyadicComplementChoices P f hfirst hsecond → ℕ :=
  complementWeight D P f (dyadic_layer_injections P f hfirst hsecond) hP

theorem dyadicFilteredCoordinates_mul (a : A F P) (b : AlgebraD)
    (t : DyadicComplementChoices P f hfirst hsecond) :
    dyadicFilteredCoordinates P f hfirst hsecond hP (a*induced F D f b) t =
      dyadicFilteredCoordinates P f hfirst hsecond hP a t*b :=
  filteredCoordinates_mul D P f (dyadic_layer_injections P f hfirst hsecond) dyadic_isTwoGroup hP a b t

/-- Actual ambient powers are exactly shifted copies of the original,
independently certified dyadic augmentation powers. -/
theorem dyadicFilteredCoordinates_mem_power_iff (a : A F P) (n : ℕ) :
    a ∈ power F P n ↔ ∀ t, dyadicFilteredCoordinates P f hfirst hsecond hP a t ∈
      AlgebraD.augmentationPower (n-dyadicComplementWeight P f hfirst hsecond hP t) := by
  simpa only [dyadic_power,dyadicFilteredCoordinates,dyadicComplementWeight] using
    filteredCoordinates_mem_power_iff D P f
    (dyadic_layer_injections P f hfirst hsecond) dyadic_isTwoGroup hP a n

theorem dyadic_coefficientRow (c : Fin 3 → AlgebraD) : coefficientRow F D c = AlgebraD.foxRow c := rfl

theorem dyadic_coefficientPower (n : ℕ) :
    coefficientPower F D (ι := Fin 3) n = AlgebraD.ambientRowSpace n := by
  ext v
  rw [mem_coefficientPower,AlgebraD.mem_ambientRowSpace]
  simp only [dyadic_power]

theorem dyadic_rowImagePower (c : Fin 3 → AlgebraD) (n : ℕ) :
    rowImagePower F D c n = AlgebraD.foxImageFiltration c n := by
  rw [rowImagePower,dyadic_power,dyadic_coefficientRow]
  rfl

include hfirst hsecond hP in
/-- The actual higher-order local Fox row induces with the required
filtration inside every finite ambient 2-group satisfying the two genuine
layer injections. No ambient row strictness or normalized cost is assumed. -/
theorem dyadic_induced_foxImage_strict (c : Fin 3 → AlgebraD)
    (hc : ∀ i, c i-AlgebraD.linearFoxCoefficients i ∈ AlgebraD.augmentationPower 2)
    (n : ℕ) :
    rowImagePower F P (fun i => induced F D f (c i)) n =
      (coefficientRow F P (fun i => induced F D f (c i))).range ⊓
        coefficientPower F P (ι := Fin 3) (n+1) := by
  apply induced_rowImagePower_eq_induced F D P
    (DyadicComplementChoices P f hfirst hsecond) f
    (dyadicFilteredCoordinates P f hfirst hsecond hP)
    (dyadicComplementWeight P f hfirst hsecond hP)
    (dyadicFilteredCoordinates_mul P f hfirst hsecond hP)
    (filteredCoordinates_mem_power_iff D P f (dyadic_layer_injections P f hfirst hsecond)
      dyadic_isTwoGroup hP) c
  · intro i
    rw [dyadic_power,AlgebraD.augmentationPower_one]
    exact AlgebraD.augmentation_fox_coefficient c hc i
  · intro k
    rw [dyadic_rowImagePower,dyadic_coefficientRow,dyadic_coefficientPower]
    exact AlgebraD.foxImageFiltration_eq_induced_all c hc k

end UnitDistance.GroupAugmentation
