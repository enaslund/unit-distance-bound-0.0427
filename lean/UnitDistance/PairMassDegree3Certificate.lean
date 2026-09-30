module

public import UnitDistance.PairMassDegree12Certificate

@[expose] public section
set_option backward.privateInPublic true


/-! Degree-3 specialization of the cell majorant, used by the relaxed
pair-functional certificate. -/

noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace UnitDistance.Witness

def pairMassCellBracket3 (i j : Fin 8) : Polynomial (Polynomial ℝ) :=
  pairCellBracketPolynomial (pairMassCellCenter i j) (pairMassCellRadius i j) 3

def pairMassCellContraction3 (i j : Fin 8) : ℝ :=
  betaMonomialRectangleContraction (6 / 5 : ℝ)
    ((i : ℝ) / 8) (((i : ℕ) + 1 : ℝ) / 8)
    ((j : ℝ) / 8) (((j : ℕ) + 1 : ℝ) / 8)
    (nestedSupport (pairMassCellBracket3 i j))
    (nestedCoeff (pairMassCellBracket3 i j))

theorem pairMass_cell_integral_le3 (i j : Fin 8) :
    (∫ t in Icc ((i : ℝ) / 8) (((i : ℕ) + 1 : ℝ) / 8),
      ∫ u in Icc ((j : ℝ) / 8) (((j : ℕ) + 1 : ℝ) / 8),
        betaDensity (6 / 5 : ℝ) t * betaDensity (6 / 5 : ℝ) u *
          (polynomial t u) ^ p) ≤
      pairMassCellContraction3 i j * pairMassCellCenter i j ^ p := by
  have hilr : (i : ℝ) / 8 ≤ ((i : ℕ) + 1 : ℝ) / 8 := by
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 8)).2
    norm_num
  have hir1 : ((i : ℕ) + 1 : ℝ) / 8 ≤ 1 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    norm_num
    exact_mod_cast (Nat.succ_le_iff.mpr i.isLt)
  have hjlr : (j : ℝ) / 8 ≤ ((j : ℕ) + 1 : ℝ) / 8 := by
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 8)).2
    norm_num
  have hjr1 : ((j : ℕ) + 1 : ℝ) / 8 ≤ 1 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    norm_num
    exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
  apply pairCell_integral_le_contraction (N := 3) (by norm_num)
    (by positivity) hilr hir1 (by positivity) hjlr hjr1
    (pairMassCellCenter_pos i j) (pairMassCellRadius_nonneg i j)
      (pairMassCellRadius_lt_one i j)
  intro t ht u hu
  exact pairMassCell_radius_bound i j ht hu

end UnitDistance.Witness
