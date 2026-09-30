module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.LSeries.Positivity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual relative zeta value at one

The relative value is the positive quotient of the ordinary Dedekind-zeta
residues. It is proved to be the right limit of the actual quotient above one;
it is not a quotient of the totalized pole values. The coefficient-counting
argument reuses Mathlib's ideal-counting asymptotic and class-number formula.
This supplies the finite-field analytic normalization used in analytic.tex
and geometry.tex. No bound along a growing field family is assumed or proved
by defining this value.
-/

noncomputable section
open Filter Topology Asymptotics NumberField NumberField.InfinitePlace NumberField.Units
open scoped BigOperators ComplexOrder

namespace UnitDistance.NumberFieldAnalysis

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

/-- The actual number of integral ideals of a specified absolute norm. -/
def idealCount (n : ℕ) : ℝ := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

theorem idealCount_summatory_limit :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, idealCount K k) / (n : ℝ))
      atTop (𝓝 (dedekindZeta_residue K)) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, idealCount, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ =>
      Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem dedekindZeta_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) s := by
  apply LSeriesSummable_of_sum_norm_bigO_and_nonneg _
    (fun n => Nat.cast_nonneg _) zero_le_one hs
  exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (by simpa [idealCount] using idealCount_summatory_limit K)

theorem dedekindZeta_abscissa_le_one :
    LSeries.abscissaOfAbsConv (fun n => (idealCount K n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
  intro x hx
  exact dedekindZeta_summable K (by simpa using hx)

@[simp] theorem idealCount_one : idealCount K 1 = 1 := by
  simp [idealCount, Ideal.absNorm_eq_one_iff]

/-- On the real half-line of absolute convergence the actual zeta function
is real and positive, not just nonzero as a complex number. -/
theorem dedekindZeta_positive {s : ℝ} (hs : 1 < s) : 0 < dedekindZeta K s := by
  change 0 < LSeries (fun n => (idealCount K n : ℂ)) s
  apply LSeries.positive
  · intro n
    change (0 : ℂ) ≤ (idealCount K n : ℂ)
    simp [idealCount]
  · simp
  · exact (dedekindZeta_abscissa_le_one K).trans_lt (by exact_mod_cast hs)

theorem dedekindZeta_im_eq_zero {s : ℝ} (hs : 1 < s) :
    (dedekindZeta K s).im = 0 :=
  ((Complex.pos_iff.mp (dedekindZeta_positive K hs)).2).symm

theorem dedekindZeta_eq_ofReal_re {s : ℝ} (hs : 1 < s) :
    dedekindZeta K s = ((dedekindZeta K s).re : ℂ) := by
  apply Complex.ext <;> simp [dedekindZeta_im_eq_zero K hs]

theorem dedekindZeta_re_pos {s : ℝ} (hs : 1 < s) :
    0 < (dedekindZeta K s).re :=
  (Complex.pos_iff.mp (dedekindZeta_positive K hs)).1

/-- The residue quotient, independently defined using actual number fields. -/
def relativeResidue : ℝ := dedekindZeta_residue K / dedekindZeta_residue F

/-- The actual zeta quotient away from its poles. -/
def relativeZeta (s : ℂ) : ℂ := dedekindZeta K s / dedekindZeta F s

theorem relativeZeta_eq_ofReal_div {s : ℝ} (hs : 1 < s) :
    relativeZeta K F s =
      (((dedekindZeta K s).re / (dedekindZeta F s).re : ℝ) : ℂ) := by
  unfold relativeZeta
  conv_lhs => rw [dedekindZeta_eq_ofReal_re K hs, dedekindZeta_eq_ofReal_re F hs]
  exact Complex.ofReal_div _ _ |>.symm

theorem relativeZeta_positive {s : ℝ} (hs : 1 < s) : 0 < relativeZeta K F s := by
  rw [relativeZeta_eq_ofReal_div K F hs]
  exact Complex.zero_lt_real.mpr
    (div_pos (dedekindZeta_re_pos K hs) (dedekindZeta_re_pos F hs))

theorem relativeZeta_im_eq_zero {s : ℝ} (hs : 1 < s) :
    (relativeZeta K F s).im = 0 :=
  ((Complex.pos_iff.mp (relativeZeta_positive K F hs)).2).symm

theorem relativeResidue_pos : 0 < relativeResidue K F :=
  div_pos (dedekindZeta_residue_pos K) (dedekindZeta_residue_pos F)

theorem tendsto_relativeZeta_nhdsGT :
    Tendsto (fun s : ℝ => relativeZeta K F s) (𝓝[>] 1)
      (𝓝 (relativeResidue K F : ℂ)) := by
  have h := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).div
    (tendsto_sub_one_mul_dedekindZeta_nhdsGT F)
    (by exact_mod_cast dedekindZeta_residue_ne_zero F)
  simp only [relativeResidue, Complex.ofReal_div]
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : ((s : ℂ)-1) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hs))
  simp only [Pi.div_apply, relativeZeta, mul_div_mul_left _ _ hne]

theorem tendsto_log_relativeZeta_re_nhdsGT :
    Tendsto (fun s : ℝ => Real.log (relativeZeta K F s).re) (𝓝[>] 1)
      (𝓝 (Real.log (relativeResidue K F))) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_relativeZeta_nhdsGT K F)
  exact (Real.continuousAt_log (relativeResidue_pos K F).ne').tendsto.comp h

end UnitDistance.NumberFieldAnalysis
