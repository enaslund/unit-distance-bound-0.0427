module

public import UnitDistance.SIntegerCRT
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual finite-place valuation normalization and period volume -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain WithZero MeasureTheory

namespace UnitDistance.SIntegerCRT

/-- A surjective integer-valued valuation is uniquely determined by its
valuation comparison relation. -/
theorem discreteValuation_eq_of_isEquiv {E : Type*} [Field E]
    (v w : Valuation E ℤᵐ⁰) (hv : Function.Surjective v) (hw : Function.Surjective w)
    (h : v.IsEquiv w) : v = w := by
  have least (z : ℤᵐ⁰) (hz : 1 < z) : WithZero.exp 1 ≤ z := by
    have hn : z ≠ 0 := ne_of_gt (lt_trans zero_lt_one hz)
    rw [← WithZero.exp_log hn, WithZero.exp_le_exp]
    have hh : (0 : ℤ) < WithZero.log z := by
      rw [← WithZero.exp_lt_exp, WithZero.exp_zero, WithZero.exp_log hn]
      exact hz
    omega
  obtain ⟨π, hπ⟩ := hv (WithZero.exp 1)
  have hπgt : 1 < v π := by rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hwπgt : 1 < w π := h.one_lt_iff_one_lt.mp hπgt
  have hwπ : w π = WithZero.exp 1 := by
    apply le_antisymm _ (least _ hwπgt)
    obtain ⟨z, hz⟩ := hw (WithZero.exp 1)
    have hzgt : 1 < w z := by rw [hz, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hvz := least _ (h.one_lt_iff_one_lt.mpr hzgt)
    have hh : v π ≤ v z := by rwa [hπ]
    simpa only [hz] using h.le_iff_le.mp hh
  ext x
  by_cases hx : v x = 0
  · exact hx.trans (h.eq_zero.mp hx).symm
  have hp : v (π ^ WithZero.log (v x)) = v x := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, Int.zsmul_eq_mul, mul_one, WithZero.exp_log hx]
  have hwp := h.eq_iff.mp hp
  rw [map_zpow₀, hwπ, ← WithZero.exp_zsmul, Int.zsmul_eq_mul, mul_one,
    WithZero.exp_log hx] at hwp
  exact hwp

variable {K : Type} [Field K] [NumberField K]

/-- The canonical integer normalization in the Haar module is exactly the
actual extended prime valuation on the completion. -/
theorem canonical_intValuation_eq (v : HeightOneSpectrum (𝓞 K)) :
    Local.ValuedHaar.intValuation (v.adicCompletion K) =
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) := by
  apply discreteValuation_eq_of_isEquiv _ _ (Local.ValuedHaar.intValuation_surjective _)
    (HeightOneSpectrum.valuedAdicCompletion_surjective K v)
  apply Valuation.isEquiv_of_val_le_one
  intro x
  rw [Local.ValuedHaar.intValuation_le_one_iff]
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).le_one_iff_le_one

/-- Actual completion valuation balls are the canonical Haar balls. -/
theorem actualBall_eq (v : HeightOneSpectrum (𝓞 K)) (a : ℤ) :
    {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp a} =
      (Local.ValuedHaar.ball (v.adicCompletion K) a : Set (v.adicCompletion K)) := by
  ext x
  change _ ↔ Local.ValuedHaar.intValuation (v.adicCompletion K) x ≤ _
  rw [canonical_intValuation_eq]
  rfl

/-- The measure of an actual local valuation ball is the ordinary prime
ideal norm raised to its signed radius exponent. -/
theorem actualBall_volume (v : HeightOneSpectrum (𝓞 K)) (a : ℤ) :
    (Local.ValuedHaar.normalizedHaar (v.adicCompletion K)).real
      {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp a} =
        (Ideal.absNorm v.asIdeal : ℝ) ^ a := by
  rw [actualBall_eq, Local.ValuedHaar.normalizedHaar_ball,
    Local.AdicResidue.residueCard_eq_absNorm]

variable {T : Type*} [Fintype T]

/-- Exact rational norm of the actual signed-exponent period ideal. -/
theorem periodIdeal_absNorm (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) :
    FractionalIdeal.absNorm (periodIdeal P a).val =
      ∏ t, (Ideal.absNorm (P t).asIdeal : ℚ) ^ a t := by
  simp only [periodIdeal, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    map_prod, map_zpow₀, primeIdealUnit_coe, FractionalIdeal.coeIdeal_absNorm]

local instance localMeasurableSpace (P : T → HeightOneSpectrum (𝓞 K)) (t : T) :
    MeasurableSpace ((P t).adicCompletion K) := borel ((P t).adicCompletion K)
local instance localBorelSpace (P : T → HeightOneSpectrum (𝓞 K)) (t : T) :
    BorelSpace ((P t).adicCompletion K) := ⟨rfl⟩

/-- Product of the actual local additive Haar measures, each normalized on
its valuation ring. -/
def localProductHaar (P : T → HeightOneSpectrum (𝓞 K)) : Measure (LocalProduct P) :=
  Measure.pi fun t ↦ Local.ValuedHaar.normalizedHaar ((P t).adicCompletion K)

instance localProductHaar_sigmaFinite (P : T → HeightOneSpectrum (𝓞 K)) :
    SigmaFinite (localProductHaar P) := by
  unfold localProductHaar
  infer_instance

theorem finitePeriod_eq_pi (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) :
    (finitePeriod P a : Set (LocalProduct P)) =
      Set.univ.pi (fun t ↦ {x : (P t).adicCompletion K | Valued.v x ≤ WithZero.exp (-a t)}) := by
  ext x
  simp only [Set.mem_univ_pi]
  rfl

theorem finitePeriod_measurable (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) :
    MeasurableSet (finitePeriod P a : Set (LocalProduct P)) := by
  rw [finitePeriod_eq_pi]
  apply MeasurableSet.univ_pi
  intro t
  rw [actualBall_eq]
  exact Local.ValuedHaar.ball_measurable _ _

theorem finitePeriod_compact (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) :
    IsCompact (finitePeriod P a : Set (LocalProduct P)) := by
  rw [finitePeriod_eq_pi]
  apply isCompact_univ_pi
  intro t
  rw [actualBall_eq]
  exact Local.ValuedHaar.ball_compact _ _

theorem finitePeriod_open (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) :
    IsOpen (finitePeriod P a : Set (LocalProduct P)) := by
  rw [finitePeriod_eq_pi]
  apply isOpen_set_pi Set.finite_univ
  intro t _
  rw [actualBall_eq]
  exact (Local.ValuedHaar.ball_clopen _ _).isOpen

/-- The exact volume of an arbitrary rectangular finite period. -/
theorem finitePeriod_volume (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) :
    (localProductHaar P).real (finitePeriod P a) =
      ∏ t, (Ideal.absNorm (P t).asIdeal : ℝ) ^ (-a t) := by
  rw [measureReal_def, localProductHaar, finitePeriod_eq_pi, Measure.pi_pi,
    ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun t _ ↦ actualBall_volume (P t) (-a t))

/-- The manuscript period identity uses the norm of the literal fractional
ideal, with every signed exponent and every local normalization fixed. -/
theorem finitePeriod_volume_eq_inv_norm (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) :
    (localProductHaar P).real (finitePeriod P a) =
      (FractionalIdeal.absNorm (periodIdeal P a).val : ℝ)⁻¹ := by
  rw [finitePeriod_volume, periodIdeal_absNorm]
  simp only [Rat.cast_prod, Rat.cast_zpow, Rat.cast_natCast, zpow_neg, Finset.prod_inv_distrib]

end UnitDistance.SIntegerCRT
