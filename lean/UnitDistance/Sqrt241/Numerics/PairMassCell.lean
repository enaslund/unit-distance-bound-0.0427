module

public import UnitDistance.Sqrt241.Numerics.PairMassRat
public import UnitDistance.Sqrt241.Numerics.RatLogRounded
public import UnitDistance.Sqrt241.Numerics.PairMassNormalization
public import UnitDistance.PairMassCellCertificate

@[expose] public section
set_option backward.privateInPublic true


/-!
# Soundness of the cell certificate for the pair mass

For a grid `N`, enclosures `XL k ≤ (k/N)^q ≤ XU k`, cell centers `h` and
bounds `H ≥ h^p`, the literal beta integral of `P^p` over the unit square is at
most the rational `massTotal` of `PairMassRat.lean`. On each cell,
`P^p = h^p (1+w)^p` with `w = P/h − 1`, `|w| ≤ ρ < 1` (monotonicity of `P`),
and the generalized binomial series of `(1+w)^p` truncated after degree three
plus its uniform tail is a polynomial majorant (`generalizedBinomial_truncation_error`
of the ℚ development). Its exact integral against the two beta densities is a
finite contraction of beta moments, bounded by directed rational enclosures.
-/

noncomputable section

open MeasureTheory Set
open UnitDistance.Sqrt241.Numerics

namespace UnitDistance.Sqrt241.Witness.MassCert

/-- The beta density `q t^(q-1)` of the mass normalization. -/
abbrev βq (t : ℝ) : ℝ := _root_.UnitDistance.Witness.betaDensity pairBetaExponent t

theorem p_eq_pQ : p = ((pQ : ℚ) : ℝ) := by
  norm_num [p, increment, pQ]

theorem q_eq_qQ : pairBetaExponent = ((qQ : ℚ) : ℝ) := by
  norm_num [pairBetaExponent, qQ]

theorem gchoose_cast (x : ℚ) (k : ℕ) :
    Ring.choose ((x : ℚ) : ℝ) k = ((gchoose x k : ℚ) : ℝ) := by
  induction k with
  | zero => simp [gchoose]
  | succ k ih =>
    rw [_root_.UnitDistance.Witness.generalizedChoose_succ, ih, gchoose]
    push_cast
    ring

theorem PQ_cast (x y : ℚ) : ((PQ x y : ℚ) : ℝ) = polynomial (x : ℝ) (y : ℝ) := by
  rw [polynomial_eq_table, PQ, sumRange_cast]
  apply Finset.sum_congr rfl
  intro i _
  rw [sumRange_cast]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-! ## The polynomial majorant -/

theorem binomial_eq_powers (h : ℚ) (hh : h ≠ 0) (P : ℝ) :
    (∑ k ∈ Finset.range 4, ((gchoose pQ k : ℚ) : ℝ) * (P / (h : ℝ) - 1) ^ k) =
      ∑ m ∈ Finset.range 4, ((binA h m : ℚ) : ℝ) * P ^ m := by
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, binA]
  push_cast
  field_simp
  ring

theorem majorant_eq_bivariate (h ρ : ℚ) (hh : h ≠ 0) (t u : ℝ) :
    (∑ k ∈ Finset.range 4, ((gchoose pQ k : ℚ) : ℝ) * (polynomial t u / (h : ℝ) - 1) ^ k) +
        ((tailQ ρ : ℚ) : ℝ) =
      _root_.UnitDistance.Witness.bivariatePolynomial (Finset.range 10 ×ˢ Finset.range 10)
        (fun a b => ((cellCoeff h ρ a b : ℚ) : ℝ)) t u := by
  rw [binomial_eq_powers h hh]
  have hpow : ∀ m ∈ Finset.range 4, ((binA h m : ℚ) : ℝ) * polynomial t u ^ m =
      ∑ i ∈ Finset.range 10, ∑ j ∈ Finset.range 10,
        ((binA h m : ℚ) : ℝ) * ((cPow m i j : ℚ) : ℝ) * t ^ i * u ^ j := by
    intro m hm
    rw [polynomial_pow_eq_table m (by simp only [Finset.mem_range] at hm; omega),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Finset.sum_congr rfl hpow, Finset.sum_comm]
  unfold _root_.UnitDistance.Witness.bivariatePolynomial
  rw [Finset.sum_product]
  have htail : ((tailQ ρ : ℚ) : ℝ) =
      ∑ i ∈ Finset.range 10, ∑ j ∈ Finset.range 10,
        ((if i = 0 ∧ j = 0 then tailQ ρ else 0 : ℚ) : ℝ) * t ^ i * u ^ j := by
    rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hj
      simp at hj
    · intro i _ hi
      apply Finset.sum_eq_zero
      intro j _
      simp [hi]
    · intro hi
      simp at hi
  rw [htail, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [cellCoeff]
  push_cast
  rw [sumRange_cast, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
  push_cast
  rfl

/-! ## Cells -/

theorem cell_bounds_of_grid {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i < N) :
    0 ≤ (i : ℝ) / N ∧ (i : ℝ) / N ≤ ((i : ℝ) + 1) / N ∧ ((i : ℝ) + 1) / N ≤ 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  refine ⟨by positivity, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hN'.le
  · rw [div_le_one hN']
    exact hi'

theorem cast_div_grid (N i : ℕ) : (((i : ℚ) / N : ℚ) : ℝ) = (i : ℝ) / N := by
  push_cast; ring

theorem cast_div_grid_succ (N i : ℕ) : ((((i : ℚ) + 1) / N : ℚ) : ℝ) = ((i : ℝ) + 1) / N := by
  push_cast; ring

/-- On a cell, `|P/h − 1| ≤ cellRho`. -/
theorem cell_radius_bound {N : ℕ} (hN : 0 < N) {i j : ℕ} (hi : i < N) (hj : j < N)
    {h : ℚ} (hh : 0 < h) {t u : ℝ}
    (ht : t ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N))
    (hu : u ∈ Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)) :
    |polynomial t u / (h : ℝ) - 1| ≤
      ((cellRho h (cellLo N i j) (cellHi N i j) : ℚ) : ℝ) := by
  obtain ⟨hi0, hilr, hi1⟩ := cell_bounds_of_grid hN hi
  obtain ⟨hj0, hjlr, hj1⟩ := cell_bounds_of_grid hN hj
  have hb := _root_.UnitDistance.Witness.polynomial_cell_bounds hi0 ht.1 ht.2 hi1
    hj0 hu.1 hu.2 hj1
  rw [← polynomial_eq_manuscript] at hb
  have hlo : ((cellLo N i j : ℚ) : ℝ) = polynomial ((i : ℝ) / N) ((j : ℝ) / N) := by
    rw [cellLo, PQ_cast, cast_div_grid, cast_div_grid]
  have hhi : ((cellHi N i j : ℚ) : ℝ) =
      polynomial (((i : ℝ) + 1) / N) (((j : ℝ) + 1) / N) := by
    rw [cellHi, PQ_cast, cast_div_grid_succ, cast_div_grid_succ]
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hρ1 : ((cellHi N i j : ℚ) : ℝ) / h - 1 ≤ ((cellRho h (cellLo N i j) (cellHi N i j) : ℚ) : ℝ) := by
    have := le_max_left ((cellHi N i j) / h - 1) (1 - (cellLo N i j) / h)
    exact_mod_cast this
  have hρ2 : 1 - ((cellLo N i j : ℚ) : ℝ) / h ≤ ((cellRho h (cellLo N i j) (cellHi N i j) : ℚ) : ℝ) := by
    have := le_max_right ((cellHi N i j) / h - 1) (1 - (cellLo N i j) / h)
    exact_mod_cast this
  rw [hlo] at hρ2
  rw [hhi] at hρ1
  have hdiv1 : polynomial t u / h ≤ polynomial (((i : ℝ) + 1) / N) (((j : ℝ) + 1) / N) / h :=
    div_le_div_of_nonneg_right hb.2 hh'.le
  have hdiv2 : polynomial ((i : ℝ) / N) ((j : ℝ) / N) / h ≤ polynomial t u / h :=
    div_le_div_of_nonneg_right hb.1 hh'.le
  rw [abs_le]
  constructor <;> linarith

/-- Pointwise majorant of `P^p` on a cell. -/
theorem cell_pointwise_majorant {N : ℕ} (hN : 0 < N) {i j : ℕ} (hi : i < N) (hj : j < N)
    {h : ℚ} (hh : 0 < h) (hρ : cellRho h (cellLo N i j) (cellHi N i j) < 1) {t u : ℝ}
    (ht : t ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N))
    (hu : u ∈ Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)) :
    polynomial t u ^ p ≤ (h : ℝ) ^ p *
      _root_.UnitDistance.Witness.bivariatePolynomial (Finset.range 10 ×ˢ Finset.range 10)
        (fun a b => ((cellCoeff h (cellRho h (cellLo N i j) (cellHi N i j)) a b : ℚ) : ℝ)) t u := by
  set ρ := cellRho h (cellLo N i j) (cellHi N i j) with hρdef
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hw := cell_radius_bound hN hi hj hh ht hu
  rw [← hρdef] at hw
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := (abs_nonneg _).trans hw
  have hρ1 : (ρ : ℝ) < 1 := by exact_mod_cast hρ
  obtain ⟨hi0, hilr, hi1⟩ := cell_bounds_of_grid hN hi
  obtain ⟨hj0, hjlr, hj1⟩ := cell_bounds_of_grid hN hj
  have hP := (polynomial_bounds (hi0.trans ht.1) (ht.2.trans hi1)
    (hj0.trans hu.1) (hu.2.trans hj1)).1
  have hp12 : (1 : ℝ) ≤ p ∧ p ≤ 2 := by norm_num [p, increment]
  have htrunc := _root_.UnitDistance.Witness.generalizedBinomial_truncation_error
    (p := p) (x := polynomial t u / h - 1) (r := ρ) hp12.1 hp12.2 (N := 3) (by norm_num)
    hρ0 hρ1 hw
  have hupper : (1 + (polynomial t u / h - 1)) ^ p ≤
      (∑ k ∈ Finset.range 4, Ring.choose p k * (polynomial t u / h - 1) ^ k) +
        |Ring.choose p 4| * (ρ : ℝ) ^ 4 / (1 - ρ) := by
    have := le_abs_self ((1 + (polynomial t u / h - 1)) ^ p -
      ∑ k ∈ Finset.range (3 + 1), Ring.choose p k * (polynomial t u / h - 1) ^ k)
    norm_num at htrunc this ⊢
    linarith
  have hsum : (∑ k ∈ Finset.range 4, Ring.choose p k * (polynomial t u / h - 1) ^ k) +
      |Ring.choose p 4| * (ρ : ℝ) ^ 4 / (1 - ρ) =
      (∑ k ∈ Finset.range 4, ((gchoose pQ k : ℚ) : ℝ) * (polynomial t u / (h : ℝ) - 1) ^ k) +
        ((tailQ ρ : ℚ) : ℝ) := by
    simp only [p_eq_pQ, gchoose_cast, tailQ]
    push_cast
    ring
  rw [← majorant_eq_bivariate h ρ hh.ne', ← hsum]
  have hfac : polynomial t u = (h : ℝ) * (1 + (polynomial t u / h - 1)) := by
    field_simp
    ring
  calc
    polynomial t u ^ p = ((h : ℝ) * (1 + (polynomial t u / h - 1))) ^ p := by
      rw [← hfac]
    _ = (h : ℝ) ^ p * (1 + (polynomial t u / h - 1)) ^ p :=
      Real.mul_rpow hh'.le (by
        have : 0 ≤ polynomial t u / h := div_nonneg (by linarith) hh'.le
        linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left hupper (Real.rpow_nonneg hh'.le p)

/-! ## Integration -/

theorem continuous_betaDensity : Continuous βq := by
  have hq : (0 : ℝ) ≤ pairBetaExponent - 1 := by norm_num [pairBetaExponent]
  unfold βq _root_.UnitDistance.Witness.betaDensity
  exact continuous_const.mul (Real.continuous_rpow_const hq)

theorem continuous_polynomial2 : Continuous (fun tu : ℝ × ℝ => polynomial tu.1 tu.2) := by
  unfold polynomial bernstein3
  fun_prop

theorem continuous_massIntegrand :
    Continuous (Function.uncurry fun t u => βq t * βq u * polynomial t u ^ p) := by
  have hp : 0 ≤ p := witness_basic.2.2.1.le
  have hr : Continuous (fun tu : ℝ × ℝ => (polynomial tu.1 tu.2) ^ p) :=
    continuous_polynomial2.rpow_const (fun _ => Or.inr hp)
  exact ((continuous_betaDensity.comp continuous_fst).mul
    (continuous_betaDensity.comp continuous_snd)).mul hr

theorem continuous_bivariate (S : Finset (ℕ × ℕ)) (c : ℕ → ℕ → ℝ) :
    Continuous (fun tu : ℝ × ℝ =>
      _root_.UnitDistance.Witness.bivariatePolynomial S c tu.1 tu.2) := by
  unfold _root_.UnitDistance.Witness.bivariatePolynomial
  fun_prop

theorem iterated_setIntegral_mono {l r b top : ℝ} {F G : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G))
    (hle : ∀ t ∈ Icc l r, ∀ u ∈ Icc b top, F t u ≤ G t u) :
    (∫ t in Icc l r, ∫ u in Icc b top, F t u) ≤ ∫ t in Icc l r, ∫ u in Icc b top, G t u := by
  apply setIntegral_mono_on
  · exact (continuous_parametric_integral_of_continuous hF isCompact_Icc).integrableOn_Icc
  · exact (continuous_parametric_integral_of_continuous hG isCompact_Icc).integrableOn_Icc
  · exact measurableSet_Icc
  · intro t ht
    apply setIntegral_mono_on
    · exact (hF.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
    · exact (hG.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
    · exact measurableSet_Icc
    · intro u hu
      exact hle t ht u hu

/-- The exact integral of `P^p` over a cell is at most `h^p` times the beta
contraction of the majorant coefficients. -/
theorem cell_integral_le_contraction {N : ℕ} (hN : 0 < N) {i j : ℕ} (hi : i < N) (hj : j < N)
    {h : ℚ} (hh : 0 < h) (hρ : cellRho h (cellLo N i j) (cellHi N i j) < 1) :
    (∫ t in Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N),
      ∫ u in Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N), βq t * βq u * polynomial t u ^ p) ≤
      (h : ℝ) ^ p * _root_.UnitDistance.Witness.betaMonomialRectangleContraction
        pairBetaExponent ((i : ℝ) / N) (((i : ℝ) + 1) / N) ((j : ℝ) / N) (((j : ℝ) + 1) / N)
        (Finset.range 10 ×ˢ Finset.range 10)
        (fun a b => ((cellCoeff h (cellRho h (cellLo N i j) (cellHi N i j)) a b : ℚ) : ℝ)) := by
  set c := fun a b => ((cellCoeff h (cellRho h (cellLo N i j) (cellHi N i j)) a b : ℚ) : ℝ)
  obtain ⟨hi0, hilr, hi1⟩ := cell_bounds_of_grid hN hi
  obtain ⟨hj0, hjlr, hj1⟩ := cell_bounds_of_grid hN hj
  have hq : 0 < pairBetaExponent := pairBetaExponent_pos
  have hcontG : Continuous (Function.uncurry fun t u => βq t * βq u *
      ((h : ℝ) ^ p * _root_.UnitDistance.Witness.bivariatePolynomial
        (Finset.range 10 ×ˢ Finset.range 10) c t u)) := by
    have hB := continuous_bivariate (Finset.range 10 ×ˢ Finset.range 10) c
    exact ((continuous_betaDensity.comp continuous_fst).mul
      (continuous_betaDensity.comp continuous_snd)).mul (continuous_const.mul hB)
  calc
    _ ≤ ∫ t in Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N),
        ∫ u in Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N), βq t * βq u *
          ((h : ℝ) ^ p * _root_.UnitDistance.Witness.bivariatePolynomial
            (Finset.range 10 ×ˢ Finset.range 10) c t u) := by
      apply iterated_setIntegral_mono continuous_massIntegrand hcontG
      intro t ht u hu
      have hβt : 0 ≤ βq t := by
        unfold βq _root_.UnitDistance.Witness.betaDensity
        exact mul_nonneg hq.le (Real.rpow_nonneg (hi0.trans ht.1) _)
      have hβu : 0 ≤ βq u := by
        unfold βq _root_.UnitDistance.Witness.betaDensity
        exact mul_nonneg hq.le (Real.rpow_nonneg (hj0.trans hu.1) _)
      exact mul_le_mul_of_nonneg_left (cell_pointwise_majorant hN hi hj hh hρ ht hu)
        (mul_nonneg hβt hβu)
    _ = (h : ℝ) ^ p * ∫ t in Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N),
        ∫ u in Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N), βq t * βq u *
          _root_.UnitDistance.Witness.bivariatePolynomial
            (Finset.range 10 ×ˢ Finset.range 10) c t u := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro t _
      simp only
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro u _
      simp only
      ring
    _ = _ := by
      rw [_root_.UnitDistance.Witness.beta_bivariate_monomial_rectangle_integral hq hi0 hilr
        hj0 hjlr]

/-! ## Directed evaluation of the contraction -/

/-- The beta moment of `t^m` on `[k/N, (k+1)/N]`. -/
def muReal (N k m : ℕ) : ℝ :=
  pairBetaExponent * (((((k : ℝ) + 1) / N) ^ (pairBetaExponent + m) -
    ((k : ℝ) / N) ^ (pairBetaExponent + m)) / (pairBetaExponent + m))

theorem rpow_q_add (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    x ^ (pairBetaExponent + m) = x ^ pairBetaExponent * x ^ m := by
  rw [Real.rpow_add' hx (by have := pairBetaExponent_pos; positivity), Real.rpow_natCast]

theorem muReal_bounds {N : ℕ} (hN : 0 < N) (XL XU : ℕ → ℚ)
    (hX : ∀ k ≤ N, ((XL k : ℚ) : ℝ) ≤ ((k : ℝ) / N) ^ pairBetaExponent ∧
      ((k : ℝ) / N) ^ pairBetaExponent ≤ ((XU k : ℚ) : ℝ))
    {k : ℕ} (hk : k < N) (m : ℕ) :
    ((muLo N XL XU k m : ℚ) : ℝ) ≤ muReal N k m ∧ muReal N k m ≤ ((muHi N XL XU k m : ℚ) : ℝ) := by
  obtain ⟨hk0, hklr, hk1⟩ := cell_bounds_of_grid hN hk
  have hq : 0 < pairBetaExponent := pairBetaExponent_pos
  have hqm : 0 < pairBetaExponent + m := by positivity
  have hXk := hX k hk.le
  have hXk1 := hX (k + 1) hk
  push_cast at hXk1
  have hr0 : 0 ≤ ((k : ℝ) + 1) / N := hk0.trans hklr
  have hmu : muReal N k m = pairBetaExponent / (pairBetaExponent + m) *
      ((((k : ℝ) + 1) / N) ^ m * (((k : ℝ) + 1) / N) ^ pairBetaExponent -
        ((k : ℝ) / N) ^ m * ((k : ℝ) / N) ^ pairBetaExponent) := by
    rw [muReal, rpow_q_add _ hr0, rpow_q_add _ hk0]
    field_simp
  have hcoef : 0 ≤ pairBetaExponent / (pairBetaExponent + m) := by positivity
  have hpr : 0 ≤ (((k : ℝ) + 1) / N) ^ m := by positivity
  have hpl : 0 ≤ ((k : ℝ) / N) ^ m := by positivity
  have hnonneg : 0 ≤ muReal N k m := by
    rw [muReal]
    apply mul_nonneg hq.le
    apply div_nonneg _ hqm.le
    rw [sub_nonneg]
    exact Real.rpow_le_rpow hk0 hklr hqm.le
  constructor
  · rw [muLo]
    push_cast
    rw [← q_eq_qQ]
    apply max_le hnonneg
    rw [hmu]
    apply mul_le_mul_of_nonneg_left _ hcoef
    have h1 := mul_le_mul_of_nonneg_left hXk1.1 hpr
    have h2 := mul_le_mul_of_nonneg_left hXk.2 hpl
    linarith
  · rw [muHi]
    push_cast
    rw [← q_eq_qQ, hmu]
    apply mul_le_mul_of_nonneg_left _ hcoef
    have h1 := mul_le_mul_of_nonneg_left hXk1.2 hpr
    have h2 := mul_le_mul_of_nonneg_left hXk.1 hpl
    linarith

theorem muLo_nonneg (N : ℕ) (XL XU : ℕ → ℚ) (k m : ℕ) : 0 ≤ muLo N XL XU k m :=
  le_max_left _ _

theorem dirU_bound {d : ℚ} {x0 x1 y0 y1 : ℚ} {x y : ℝ}
    (hx0 : 0 ≤ x0) (hy0 : 0 ≤ y0) (hx : (x0 : ℝ) ≤ x ∧ x ≤ x1) (hy : (y0 : ℝ) ≤ y ∧ y ≤ y1) :
    (d : ℝ) * x * y ≤ ((dirU d x0 x1 y0 y1 : ℚ) : ℝ) := by
  have hx0' : (0 : ℝ) ≤ x0 := by exact_mod_cast hx0
  have hy0' : (0 : ℝ) ≤ y0 := by exact_mod_cast hy0
  unfold dirU
  split_ifs with hd
  · have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast
    have hxy : x * y ≤ (x1 : ℝ) * y1 :=
      mul_le_mul hx.2 hy.2 (hy0'.trans hy.1) ((hx0'.trans hx.1).trans hx.2)
    nlinarith [mul_le_mul_of_nonneg_left hxy hd']
  · have hd' : (d : ℝ) ≤ 0 := by
      have : d < 0 := lt_of_not_ge hd
      exact_mod_cast this.le
    push_cast
    have hxy : (x0 : ℝ) * y0 ≤ x * y := mul_le_mul hx.1 hy.1 hy0' (hx0'.trans hx.1)
    nlinarith [mul_le_mul_of_nonpos_left hxy hd']

theorem contraction_le_cellEbar {N : ℕ} (hN : 0 < N) (XL XU : ℕ → ℚ)
    (hX : ∀ k ≤ N, ((XL k : ℚ) : ℝ) ≤ ((k : ℝ) / N) ^ pairBetaExponent ∧
      ((k : ℝ) / N) ^ pairBetaExponent ≤ ((XU k : ℚ) : ℝ))
    {i j : ℕ} (hi : i < N) (hj : j < N) (h : ℚ) :
    _root_.UnitDistance.Witness.betaMonomialRectangleContraction
        pairBetaExponent ((i : ℝ) / N) (((i : ℝ) + 1) / N) ((j : ℝ) / N) (((j : ℝ) + 1) / N)
        (Finset.range 10 ×ˢ Finset.range 10)
        (fun a b => ((cellCoeff h (cellRho h (cellLo N i j) (cellHi N i j)) a b : ℚ) : ℝ)) ≤
      ((cellEbar N XL XU i j h : ℚ) : ℝ) := by
  unfold _root_.UnitDistance.Witness.betaMonomialRectangleContraction cellEbar
  rw [Finset.sum_product, sumRange_cast]
  apply Finset.sum_le_sum
  intro a _
  rw [sumRange_cast]
  apply Finset.sum_le_sum
  intro b _
  have ha := muReal_bounds hN XL XU hX hi a
  have hb := muReal_bounds hN XL XU hX hj b
  have h := dirU_bound (d := cellCoeff h (cellRho h (cellLo N i j) (cellHi N i j)) a b)
    (muLo_nonneg N XL XU i a) (muLo_nonneg N XL XU j b) ha hb
  unfold muReal at h
  simpa only [mul_assoc] using h

/-! ## Summation over the grid -/

theorem integral_Icc_eq_sum_cells {N : ℕ} (hN : 0 < N) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ t in Icc (0 : ℝ) 1, f t) =
      ∑ i ∈ Finset.range N, ∫ t in Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N), f t := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => (n : ℝ) / N) (n := N) (μ := (volume : Measure ℝ))
    (f := f) (fun k _ => hf.intervalIntegrable ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N))
  have hle (k : ℕ) : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N := by
    apply div_le_div_of_nonneg_right _ hN'.le
    push_cast; linarith
  simp_rw [intervalIntegral.integral_of_le (hle _), ← integral_Icc_eq_integral_Ioc] at h
  simp only [Nat.cast_zero, zero_div, div_self hN'.ne'] at h
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rfl

theorem pairMassBetaIntegral_eq_sum_cells {N : ℕ} (hN : 0 < N) :
    pairMassBetaIntegral = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      ∫ t in Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N),
        ∫ u in Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N), βq t * βq u * polynomial t u ^ p := by
  have hcont := continuous_massIntegrand
  have houter : Continuous (fun t => ∫ u in Icc (0 : ℝ) 1, βq t * βq u * polynomial t u ^ p) :=
    continuous_parametric_integral_of_continuous hcont isCompact_Icc
  have hinner (t : ℝ) : Continuous (fun u => βq t * βq u * polynomial t u ^ p) :=
    hcont.comp (continuous_const.prodMk continuous_id)
  rw [pairMassBetaIntegral_eq_iterated]
  change (∫ t in Icc (0 : ℝ) 1, ∫ u in Icc (0 : ℝ) 1, βq t * βq u * polynomial t u ^ p) = _
  rw [integral_Icc_eq_sum_cells hN houter]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [integral_Icc_eq_sum_cells hN (hinner _)]
  apply integral_finsetSum
  intro j _
  have hc : Continuous (fun t => ∫ u in Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N),
      βq t * βq u * polynomial t u ^ p) :=
    continuous_parametric_integral_of_continuous hcont isCompact_Icc
  exact hc.integrableOn_Icc

/-- The certificate theorem: finitely many rational inequalities, all decided
by kernel evaluation, bound the normalized pair mass. -/
theorem pairMassBetaIntegral_le_of_checks (N : ℕ) (hN : 0 < N) (XL XU : ℕ → ℚ)
    (hTab HTab : ℕ → ℕ → ℚ) (M : ℚ)
    (hend : XL 0 = 0 ∧ XU 0 = 0 ∧ XL N = 1 ∧ XU N = 1)
    (hgrid : ∀ k, k < N → 0 < k →
      0 < XL k ∧ 0 < XU k ∧ logHiR (XL k) ≤ qQ * logLoR ((k : ℚ) / N) ∧
        qQ * logHiR ((k : ℚ) / N) ≤ logLoR (XU k))
    (hcell : ∀ i, i < N → ∀ j, j < N →
      0 < hTab i j ∧ cellRho (hTab i j) (cellLo N i j) (cellHi N i j) < 1 ∧
        0 < HTab i j ∧ pQ * logHiR (hTab i j) ≤ logLoR (HTab i j))
    (htotal : massTotal N XL XU hTab HTab ≤ M) :
    pairMassBetaIntegral ≤ (M : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hq0 : (0 : ℚ) ≤ qQ := by norm_num [qQ]
  -- grid enclosures of `(k/N)^q`
  have hX : ∀ k ≤ N, ((XL k : ℚ) : ℝ) ≤ ((k : ℝ) / N) ^ pairBetaExponent ∧
      ((k : ℝ) / N) ^ pairBetaExponent ≤ ((XU k : ℚ) : ℝ) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hend.1, hend.2.1]
      simp [Real.zero_rpow pairBetaExponent_pos.ne']
    rcases lt_or_eq_of_le hk with hkN | rfl
    · obtain ⟨hL, hU, hlo, hhi⟩ := hgrid k hkN hk0
      have hy : (0 : ℚ) < (k : ℚ) / N := by
        have : (0 : ℚ) < k := by exact_mod_cast hk0
        have : (0 : ℚ) < N := by exact_mod_cast hN
        positivity
      have h1 := le_rpow_of_logsR hy hL hq0 hlo
      have h2 := rpow_le_of_logsR hy hU hq0 hhi
      rw [cast_div_grid, ← q_eq_qQ] at h1 h2
      exact ⟨h1, h2⟩
    · rw [hend.2.2.1, hend.2.2.2]
      simp [div_self hN'.ne']
  -- sum of the cell bounds
  have hsum := pairMassBetaIntegral_eq_sum_cells (N := N) hN
  rw [hsum]
  refine le_trans ?_ (Rat.cast_le.mpr htotal)
  rw [massTotal, sumRange_cast]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mem_range] at hi
  rw [sumRange_cast]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mem_range] at hj
  obtain ⟨hh, hρ, hH, hlog⟩ := hcell i hi j hj
  have hint := cell_integral_le_contraction hN hi hj hh hρ
  have hcon := contraction_le_cellEbar hN XL XU hX hi hj (hTab i j)
  have hh' : (0 : ℝ) < hTab i j := by exact_mod_cast hh
  have hpow : (hTab i j : ℝ) ^ p ≤ HTab i j := by
    rw [p_eq_pQ]
    exact rpow_le_of_logsR hh hH (by norm_num [pQ]) hlog
  have hpow0 : 0 ≤ (hTab i j : ℝ) ^ p := Real.rpow_nonneg hh'.le p
  have hH' : (0 : ℝ) ≤ HTab i j := by exact_mod_cast hH.le
  calc
    _ ≤ (hTab i j : ℝ) ^ p * ((cellEbar N XL XU i j (hTab i j) : ℚ) : ℝ) :=
      hint.trans (mul_le_mul_of_nonneg_left hcon hpow0)
    _ ≤ (hTab i j : ℝ) ^ p * max ((cellEbar N XL XU i j (hTab i j) : ℚ) : ℝ) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hpow0
    _ ≤ (HTab i j : ℝ) * max ((cellEbar N XL XU i j (hTab i j) : ℚ) : ℝ) 0 :=
      mul_le_mul_of_nonneg_right hpow (le_max_right _ _)
    _ = _ := by push_cast; rfl

end UnitDistance.Sqrt241.Witness.MassCert
