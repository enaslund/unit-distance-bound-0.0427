module

public import UnitDistance.PairMassCellCertificate
public import UnitDistance.RationalPowerBounds

@[expose] public section
set_option backward.privateInPublic true


/-!
# Degree-12 finite certificate for the normalized pair mass

This file specializes the generic cell majorant to the published `8 × 8`
partition.  All table entries are exact rationals.  The only nonrational
quantities left by the finite contractions are eight endpoint powers and the
36 symmetric cell-center powers.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Set

namespace UnitDistance.Witness

def pairMassGridPoint (i : Fin 9) : ℝ := (i : ℝ) / 8

def pairMassCellLower (i j : Fin 8) : ℝ :=
  polynomial ((i : ℝ) / 8) ((j : ℝ) / 8)

def pairMassCellUpper (i j : Fin 8) : ℝ :=
  polynomial (((i : ℕ) + 1 : ℝ) / 8) (((j : ℕ) + 1 : ℝ) / 8)

def pairMassCellCenter (i j : Fin 8) : ℝ :=
  (pairMassCellLower i j + pairMassCellUpper i j) / 2

def pairMassCellRadius (i j : Fin 8) : ℝ :=
  (pairMassCellUpper i j - pairMassCellLower i j) /
    (pairMassCellUpper i j + pairMassCellLower i j)

def pairMassCellBracket (i j : Fin 8) : Polynomial (Polynomial ℝ) :=
  pairCellBracketPolynomial (pairMassCellCenter i j) (pairMassCellRadius i j) 12

def pairMassCellContraction (i j : Fin 8) : ℝ :=
  betaMonomialRectangleContraction (6 / 5 : ℝ)
    ((i : ℝ) / 8) (((i : ℕ) + 1 : ℝ) / 8)
    ((j : ℝ) / 8) (((j : ℕ) + 1 : ℝ) / 8)
    (nestedSupport (pairMassCellBracket i j))
    (nestedCoeff (pairMassCellBracket i j))

private theorem pairMassGrid_left_nonneg (i : Fin 8) :
    0 ≤ (i : ℝ) / 8 := by
  positivity

private theorem pairMassGrid_left_le_one (i : Fin 8) :
    (i : ℝ) / 8 ≤ 1 := by
  have hi : ((i : ℕ) : ℝ) < 8 := by exact_mod_cast i.isLt
  norm_num
  linarith

private theorem pairMassGrid_left_le_right (i : Fin 8) :
    (i : ℝ) / 8 ≤ ((i : ℕ) + 1 : ℝ) / 8 := by
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 8)).2
  norm_num

private theorem pairMassGrid_right_le_one (i : Fin 8) :
    ((i : ℕ) + 1 : ℝ) / 8 ≤ 1 := by
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).2
  norm_num
  exact_mod_cast (Nat.succ_le_iff.mpr i.isLt)

theorem pairMassCellCenter_pos (i j : Fin 8) : 0 < pairMassCellCenter i j := by
  have hl : (1 : ℝ) ≤ pairMassCellLower i j := by
    exact (polynomial_bounds (pairMassGrid_left_nonneg i)
      (pairMassGrid_left_le_one i) (pairMassGrid_left_nonneg j)
      (pairMassGrid_left_le_one j)).1
  have hu : (1 : ℝ) ≤ pairMassCellUpper i j := by
    exact (polynomial_bounds (by positivity) (pairMassGrid_right_le_one i)
      (by positivity) (pairMassGrid_right_le_one j)).1
  unfold pairMassCellCenter
  linarith

theorem pairMassCellRadius_nonneg (i j : Fin 8) : 0 ≤ pairMassCellRadius i j := by
  have hm := polynomial_cell_bounds
    (l := (i : ℝ) / 8) (r := ((i : ℕ) + 1 : ℝ) / 8)
    (b := (j : ℝ) / 8) (top := ((j : ℕ) + 1 : ℝ) / 8)
    (x := ((i : ℕ) + 1 : ℝ) / 8) (y := ((j : ℕ) + 1 : ℝ) / 8)
    (pairMassGrid_left_nonneg i) (pairMassGrid_left_le_right i) le_rfl
    (pairMassGrid_right_le_one i) (pairMassGrid_left_nonneg j)
    (pairMassGrid_left_le_right j) le_rfl (pairMassGrid_right_le_one j)
  have hlu : pairMassCellLower i j ≤ pairMassCellUpper i j := by
    simpa [pairMassCellLower, pairMassCellUpper] using hm.1
  have hc := pairMassCellCenter_pos i j
  unfold pairMassCellRadius
  exact div_nonneg (sub_nonneg.mpr hlu) (by
    unfold pairMassCellCenter at hc
    linarith)

theorem pairMassCellRadius_lt_one (i j : Fin 8) : pairMassCellRadius i j < 1 := by
  have hl : 0 < pairMassCellLower i j := by
    have h := (polynomial_bounds (t := (i : ℝ) / 8) (u := (j : ℝ) / 8)
      (pairMassGrid_left_nonneg i) (pairMassGrid_left_le_one i)
      (pairMassGrid_left_nonneg j) (pairMassGrid_left_le_one j)).1
    change 0 < polynomial ((i : ℝ) / 8) ((j : ℝ) / 8)
    linarith
  have hu : 0 < pairMassCellUpper i j := by
    have h := (polynomial_bounds
      (t := ((i : ℕ) + 1 : ℝ) / 8) (u := ((j : ℕ) + 1 : ℝ) / 8)
      (by positivity) (pairMassGrid_right_le_one i)
      (by positivity) (pairMassGrid_right_le_one j)).1
    change 0 < polynomial (((i : ℕ) + 1 : ℝ) / 8)
      (((j : ℕ) + 1 : ℝ) / 8)
    linarith
  unfold pairMassCellRadius
  exact (div_lt_one (by linarith)).mpr (by linarith)

theorem pairMassCell_radius_bound (i j : Fin 8)
    {t u : ℝ} (ht : t ∈ Icc ((i : ℝ) / 8) (((i : ℕ) + 1 : ℝ) / 8))
    (hu : u ∈ Icc ((j : ℝ) / 8) (((j : ℕ) + 1 : ℝ) / 8)) :
    |polynomial t u / pairMassCellCenter i j - 1| ≤ pairMassCellRadius i j := by
  have hb := polynomial_cell_bounds
    (l := (i : ℝ) / 8) (r := ((i : ℕ) + 1 : ℝ) / 8)
    (b := (j : ℝ) / 8) (top := ((j : ℕ) + 1 : ℝ) / 8)
    (x := t) (y := u) (pairMassGrid_left_nonneg i) ht.1 ht.2
    (pairMassGrid_right_le_one i) (pairMassGrid_left_nonneg j) hu.1 hu.2
    (pairMassGrid_right_le_one j)
  have hl : 0 < pairMassCellLower i j := by
    have h := (polynomial_bounds (t := (i : ℝ) / 8) (u := (j : ℝ) / 8)
      (pairMassGrid_left_nonneg i) (pairMassGrid_left_le_one i)
      (pairMassGrid_left_nonneg j) (pairMassGrid_left_le_one j)).1
    change 0 < polynomial ((i : ℝ) / 8) ((j : ℝ) / 8)
    linarith
  have hlu : pairMassCellLower i j ≤ pairMassCellUpper i j := by
    change polynomial ((i : ℝ) / 8) ((j : ℝ) / 8) ≤
      polynomial (((i : ℕ) + 1 : ℝ) / 8) (((j : ℕ) + 1 : ℝ) / 8)
    exact hb.1.trans hb.2
  apply normalized_center_abs_le hl hlu
  · simpa [pairMassCellLower] using hb.1
  · simpa [pairMassCellUpper] using hb.2

theorem pairMass_cell_integral_le (i j : Fin 8) :
    (∫ t in Icc ((i : ℝ) / 8) (((i : ℕ) + 1 : ℝ) / 8),
      ∫ u in Icc ((j : ℝ) / 8) (((j : ℕ) + 1 : ℝ) / 8),
        betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
          (polynomial t u) ^ p) ≤
      pairMassCellContraction i j * pairMassCellCenter i j ^ p := by
  apply pairCell_integral_le_contraction (N := 12) (by norm_num)
    (pairMassGrid_left_nonneg i) (pairMassGrid_left_le_right i)
    (pairMassGrid_right_le_one i) (pairMassGrid_left_nonneg j)
    (pairMassGrid_left_le_right j) (pairMassGrid_right_le_one j)
    (pairMassCellCenter_pos i j) (pairMassCellRadius_nonneg i j)
      (pairMassCellRadius_lt_one i j)
  intro t ht u hu
  exact pairMassCell_radius_bound i j ht hu

end UnitDistance.Witness
