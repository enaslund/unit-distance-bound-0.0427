module

public import UnitDistance.DyadicGraded

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual finite Fox-row image and its filtration

This file connects the graded kernel calculation to the image of an arbitrary
actual coefficient row with the prescribed linear terms. In particular the
image filtration agrees with the induced ambient augmentation filtration,
with the stated degree shift. No global induction is assumed or inferred.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace UnitDistance.Dyadic.AlgebraD

def foxRow (c : Fin 3 → AlgebraD) : AlgebraD →ₗ[F] (Fin 3 → AlgebraD) where
  toFun v k := v * c k
  map_add' u v := by ext k; simp [add_mul]
  map_smul' a v := by ext k; simp

theorem augmentation_linearFox (k : Fin 3) : augmentation (linearFoxCoefficients k) = 0 := by
  fin_cases k <;> simp [linearFoxCoefficients]

theorem augmentation_fox_coefficient (c : Fin 3 → AlgebraD)
    (hc : ∀ k, c k - linearFoxCoefficients k ∈ augmentationPower 2) (k : Fin 3) :
    augmentation (c k) = 0 := by
  have hm := augmentationPower_antitone (by decide : 1 ≤ 2) (hc k)
  rw [augmentationPower_one] at hm
  change augmentation (c k - linearFoxCoefficients k) = 0 at hm
  simpa only [map_sub, augmentation_linearFox, sub_zero] using hm

/-- Strict degree shift for the actual row, including every higher-order term. -/
theorem fox_row_mem_power_iff (c : Fin 3 → AlgebraD)
    (hc : ∀ k, c k - linearFoxCoefficients k ∈ augmentationPower 2)
    (n : ℕ) (hn : n ≤ 7) (v : AlgebraD) :
    (∀ k, v * c k ∈ augmentationPower (n + 1)) ↔ v ∈ augmentationPower n := by
  induction n with
  | zero =>
    constructor
    · intro _; trivial
    · intro hv k
      exact power_mul_augmentation 0 v (c k) hv (augmentation_fox_coefficient c hc k)
  | succ n ih =>
    constructor
    · intro h
      have hv : v ∈ augmentationPower n := (ih (by omega)).mp (fun k =>
        augmentationPower_antitone (Nat.le_succ (n + 1)) (h k))
      exact (fox_row_graded_kernel c hc n (by omega) v hv).mp h
    · intro hv k
      exact power_mul_augmentation (n + 1) v (c k) hv (augmentation_fox_coefficient c hc k)

/-- The ordinary kernel of the actual row is exactly the seventh augmentation power. -/
theorem foxRow_kernel (c : Fin 3 → AlgebraD)
    (hc : ∀ k, c k - linearFoxCoefficients k ∈ augmentationPower 2) :
    (foxRow c).ker = augmentationPower 7 := by
  ext v
  rw [← fox_row_mem_power_iff c hc 7 (by decide) v, augmentation_eighth_eq_bot]
  change (fun k => v * c k) = 0 ↔ ∀ k, v * c k = 0
  exact funext_iff

/-- The ambient product augmentation filtration on the three coefficient coordinates. -/
def ambientRowSpace (n : ℕ) : Submodule F (Fin 3 → AlgebraD) :=
  ⨅ k : Fin 3, (augmentationPower n).comap (LinearMap.proj k)

theorem mem_ambientRowSpace (n : ℕ) (v : Fin 3 → AlgebraD) :
    v ∈ ambientRowSpace n ↔ ∀ k, v k ∈ augmentationPower n := by
  simp [ambientRowSpace]

def foxImageFiltration (c : Fin 3 → AlgebraD) (n : ℕ) :
    Submodule F (Fin 3 → AlgebraD) := (augmentationPower n).map (foxRow c)

/-- The image filtration is exactly the induced ambient filtration shifted by
one coefficient degree. The derivative basis has an additional degree one. -/
theorem foxImageFiltration_eq_induced (c : Fin 3 → AlgebraD)
    (hc : ∀ k, c k - linearFoxCoefficients k ∈ augmentationPower 2)
    (n : ℕ) (hn : n ≤ 7) :
    foxImageFiltration c n = (foxRow c).range ⊓ ambientRowSpace (n + 1) := by
  ext v
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, (mem_ambientRowSpace _ _).mpr
      ((fox_row_mem_power_iff c hc n hn a).mpr ha)⟩
  · rintro ⟨⟨a, rfl⟩, ha⟩
    exact ⟨a, (fox_row_mem_power_iff c hc n hn a).mp
      ((mem_ambientRowSpace _ _).mp ha), rfl⟩

theorem ambientRowSpace_eq_bot (n : ℕ) (hn : 8 ≤ n) : ambientRowSpace n = ⊥ := by
  ext v
  simp only [mem_ambientRowSpace, augmentation_nilpotent n hn, Submodule.mem_bot]
  exact funext_iff.symm

/-- The induced-filtration identification also holds beyond the nilpotence
length, where both sides vanish. -/
theorem foxImageFiltration_eq_induced_all (c : Fin 3 → AlgebraD)
    (hc : ∀ k, c k - linearFoxCoefficients k ∈ augmentationPower 2) (n : ℕ) :
    foxImageFiltration c n = (foxRow c).range ⊓ ambientRowSpace (n + 1) := by
  by_cases hn : n ≤ 7
  · exact foxImageFiltration_eq_induced c hc n hn
  · rw [ambientRowSpace_eq_bot (n + 1) (by omega), inf_bot_eq]
    simp [foxImageFiltration, augmentation_nilpotent n (by omega : 8 ≤ n)]

theorem finrank_foxImageFiltration (c : Fin 3 → AlgebraD)
    (hc : ∀ k, c k - linearFoxCoefficients k ∈ augmentationPower 2)
    (n : ℕ) (hn : n ≤ 7) :
    Module.finrank F (foxImageFiltration c n) =
      Module.finrank F (augmentationPower n) - 1 := by
  let f := (foxRow c).comp (augmentationPower n).subtype
  have hr : f.range = foxImageFiltration c n := by
    rw [LinearMap.range_comp]
    simp [foxImageFiltration]
  have hk : f.ker = (augmentationPower 7).comap (augmentationPower n).subtype := by
    rw [LinearMap.ker_comp, foxRow_kernel c hc]
  have hd := f.finrank_range_add_finrank_ker
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe (augmentationPower_antitone hn)).finrank_eq] at hd
  have h7 : Module.finrank F (augmentationPower 7) = 1 := augmentation_dimensions 7
  rw [h7] at hd
  exact Nat.eq_sub_of_add_eq hd

theorem foxImageFiltration_vanishes (c : Fin 3 → AlgebraD) (n : ℕ) (hn : 8 ≤ n) :
    foxImageFiltration c n = ⊥ := by
  simp [foxImageFiltration, augmentation_nilpotent n hn]

/-- The Hilbert polynomial of the actual image filtration, with coefficient
shift one and derivative-basis shift one. -/
def foxImageHilbertPolynomial (c : Fin 3 → AlgebraD) : ℤ[X] :=
  ∑ n ∈ Finset.range 8, Polynomial.monomial (n + 2)
    ((Module.finrank F (foxImageFiltration c n) : ℤ) -
      (Module.finrank F (foxImageFiltration c (n + 1)) : ℤ))

theorem foxImageFiltration_antitone (c : Fin 3 → AlgebraD) :
    Antitone (foxImageFiltration c) := by
  intro m n h
  exact Submodule.map_mono (augmentationPower_antitone h)

/-- Ordinary successive quotients of the actual image filtration. -/
abbrev foxImageLayer (c : Fin 3 → AlgebraD) (n : ℕ) :=
  foxImageFiltration c n ⧸
    (foxImageFiltration c (n + 1)).comap (foxImageFiltration c n).subtype

theorem finrank_foxImageLayer (c : Fin 3 → AlgebraD) (n : ℕ) :
    Module.finrank F (foxImageLayer c n) =
      Module.finrank F (foxImageFiltration c n) -
      Module.finrank F (foxImageFiltration c (n + 1)) := by
  have hle := foxImageFiltration_antitone c (Nat.le_succ n)
  have hd := Submodule.finrank_quotient_add_finrank
    ((foxImageFiltration c (n + 1)).comap (foxImageFiltration c n).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at hd
  exact Nat.eq_sub_of_add_eq hd

theorem foxImageHilbertPolynomial_eq_quotient_sum (c : Fin 3 → AlgebraD) :
    foxImageHilbertPolynomial c = ∑ n ∈ Finset.range 8,
      Polynomial.monomial (n + 2) (Module.finrank F (foxImageLayer c n) : ℤ) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [finrank_foxImageLayer, Nat.cast_sub
    (Submodule.finrank_mono (foxImageFiltration_antitone c (Nat.le_succ n)))]

/-- The exact finite row-image numerator appearing in Lemma `tw:new-local-fox`.
The two shifts are included, and the polynomial is built from actual image
quotient dimensions. -/
theorem foxImageHilbertPolynomial_eq (c : Fin 3 → AlgebraD)
    (hc : ∀ k, c k - linearFoxCoefficients k ∈ augmentationPower 2) :
    foxImageHilbertPolynomial c =
      X ^ 2 * ((1 + X) ^ 3 * (1 + X ^ 2) ^ 2 - X ^ 7) := by

  have h0 : Module.finrank F (foxImageFiltration c 0) = 31 := by
    rw [finrank_foxImageFiltration c hc 0 (by decide),
      show Module.finrank F (augmentationPower 0) = 32 from augmentation_dimensions 0]
  have h1 : Module.finrank F (foxImageFiltration c 1) = 30 := by
    rw [finrank_foxImageFiltration c hc 1 (by decide),
      show Module.finrank F (augmentationPower 1) = 31 from augmentation_dimensions 1]
  have h2 : Module.finrank F (foxImageFiltration c 2) = 27 := by
    rw [finrank_foxImageFiltration c hc 2 (by decide),
      show Module.finrank F (augmentationPower 2) = 28 from augmentation_dimensions 2]
  have h3 : Module.finrank F (foxImageFiltration c 3) = 22 := by
    rw [finrank_foxImageFiltration c hc 3 (by decide),
      show Module.finrank F (augmentationPower 3) = 23 from augmentation_dimensions 3]
  have h4 : Module.finrank F (foxImageFiltration c 4) = 15 := by
    rw [finrank_foxImageFiltration c hc 4 (by decide),
      show Module.finrank F (augmentationPower 4) = 16 from augmentation_dimensions 4]
  have h5 : Module.finrank F (foxImageFiltration c 5) = 8 := by
    rw [finrank_foxImageFiltration c hc 5 (by decide),
      show Module.finrank F (augmentationPower 5) = 9 from augmentation_dimensions 5]
  have h6 : Module.finrank F (foxImageFiltration c 6) = 3 := by
    rw [finrank_foxImageFiltration c hc 6 (by decide),
      show Module.finrank F (augmentationPower 6) = 4 from augmentation_dimensions 6]
  have h7 : Module.finrank F (foxImageFiltration c 7) = 0 := by
    rw [finrank_foxImageFiltration c hc 7 (by decide),
      show Module.finrank F (augmentationPower 7) = 1 from augmentation_dimensions 7]
  have h8 : Module.finrank F (foxImageFiltration c 8) = 0 := by
    rw [foxImageFiltration_vanishes c 8 (by decide), finrank_bot]
  simp only [foxImageHilbertPolynomial, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  norm_num only
  simp only [← Polynomial.C_mul_X_pow_eq_monomial]
  norm_num
  ring

end UnitDistance.Dyadic.AlgebraD
