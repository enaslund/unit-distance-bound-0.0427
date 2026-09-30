module

public import UnitDistance.HeckeSignedGammaIntegral
public import UnitDistance.Upstream.AINTLIB.CompletedZeta.Existence

@[expose] public section
set_option backward.privateInPublic true


/-! Explicit normalization of the signed Hecke gamma product. The elementary
normalization follows the attributed AINTLIB `Existence.lean` computation;
see third-party/aintlib for its pin and Apache-2.0 license. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open scoped Real Classical ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- The signed place product splits into shifted real and ordinary complex factors. -/
theorem prod_place_signed_gamma (σ : ℝ) :
    (∏ w : InfinitePlace K, π ^ (-((mult w : ℝ) * σ + heckeRealHalfShift K w)) * Real.Gamma ((mult w : ℝ) * σ + heckeRealHalfShift K w))
      = (π ^ (-(σ + 1/2)) * Real.Gamma (σ + 1/2)) ^ (nrRealPlaces K)
        * (π ^ (-(2 * σ)) * Real.Gamma (2 * σ)) ^ (nrComplexPlaces K) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype IsReal (fun w : InfinitePlace K =>
    π ^ (-((mult w : ℝ) * σ + heckeRealHalfShift K w)) * Real.Gamma ((mult w : ℝ) * σ + heckeRealHalfShift K w))]
  congr 1
  · rw [show (π ^ (-(σ + 1/2)) * Real.Gamma (σ + 1/2)) ^ (nrRealPlaces K)
      = ∏ _w : {w : InfinitePlace K // IsReal w}, (π ^ (-(σ + 1/2)) * Real.Gamma (σ + 1/2)) by
      rw [Finset.prod_const, Finset.card_univ]]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [show (mult (w : InfinitePlace K) : ℝ) = 1 by
      rw [mult, if_pos w.2]
      norm_num]
    simp [heckeRealHalfShift, w.property]
  · rw [show (π ^ (-(2 * σ)) * Real.Gamma (2 * σ)) ^ (nrComplexPlaces K)
      = ∏ _w : {w : InfinitePlace K // ¬ IsReal w},
          (π ^ (-(2 * σ)) * Real.Gamma (2 * σ)) by
      rw [Finset.prod_const, Finset.card_univ]
      congr 1
      exact ((Fintype.card_congr (Equiv.subtypeEquivRight
        (fun w : InfinitePlace K => not_isReal_iff_isComplex))).trans rfl).symm]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [show (mult (w : InfinitePlace K) : ℝ) = 2 by
      rw [mult, if_neg w.2]
      norm_num]

    simp [heckeRealHalfShift, w.property]

/-- Archimedean and discriminant prefactor for the sign character of all real places. -/
def signedHeckePrefactor (s : ℂ) : ℂ :=
  ((|discr K| : ℝ) : ℂ) ^ (s/2) *
    (Complex.Gammaℝ (s+1) ^ nrRealPlaces K * Complex.Gammaℂ s ^ nrComplexPlaces K)

/-- The same fixed adjustment as for the ordinary class theta normalizes the signed
Mellin constant; the only change is the real Gamma shift. -/
theorem signedGamma_normalization (s : ℝ) :
    ((heckeBeta K ^ (-(s/2)) * (((heckeJacobian K : ℝ≥0) : ℝ) *
      ∏ w : InfinitePlace K, Real.pi ^ (-((mult w : ℝ) * (s/2) + heckeRealHalfShift K w)) *
        Real.Gamma ((mult w : ℝ) * (s/2) + heckeRealHalfShift K w)) : ℝ) : ℂ) =
      (heckeAdjust K : ℂ) * signedHeckePrefactor K (s : ℂ) := by
  have hD : (|discr K| : ℝ) = (((discr K).natAbs : ℕ) : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have hDpos := natAbs_discr_pos K
  have hpre : signedHeckePrefactor K (s : ℂ) =
      (((((discr K).natAbs : ℕ) : ℝ) ^ (s/2) *
        ((Real.pi ^ (-((s+1)/2)) * Real.Gamma ((s+1)/2)) ^ nrRealPlaces K *
          (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s) ^ nrComplexPlaces K) : ℝ) : ℂ) := by
    unfold signedHeckePrefactor
    rw [show (s : ℂ)+1 = ((s+1 : ℝ) : ℂ) by push_cast; rfl]
    rw [show ((s : ℂ) / 2) = ((s/2 : ℝ) : ℂ) by push_cast; rfl]
    rw [show ((|discr K| : ℝ) : ℂ) = ((((discr K).natAbs : ℕ) : ℝ) : ℂ) by rw [hD]]
    rw [← Complex.ofReal_cpow (by positivity), Gammaℝ_ofReal, Gammaℂ_ofReal]
    push_cast
    ring
  rw [hpre, ← Complex.ofReal_mul]
  congr 1
  have h2s : 2 * (s/2) = s := by ring
  have hhalf : s/2+1/2 = (s+1)/2 := by ring
  rw [prod_place_signed_gamma K (s/2), h2s, hhalf]
  have hβsplit : (heckeBeta K) ^ (-(s/2)) =
      ((2 : ℝ) ^ (-s)) ^ nrComplexPlaces K *
        (((discr K).natAbs : ℕ) : ℝ) ^ (s/2) := by
    rw [heckeBeta, Real.div_rpow (by positivity) hDpos.le]
    rw [div_eq_mul_inv, ← Real.rpow_neg hDpos.le]
    congr 1
    · rw [← Real.rpow_natCast (4 : ℝ) (nrComplexPlaces K), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast ((2 : ℝ) ^ (-s)) (nrComplexPlaces K),
        ← Real.rpow_mul (by norm_num)]
      rw [show (4 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]; norm_num]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    · ring_nf
  rw [hβsplit, heckeAdjust]
  have h2π : (2 * Real.pi) ^ (-s) = (2 : ℝ) ^ (-s) * Real.pi ^ (-s) :=
    Real.mul_rpow (by norm_num) Real.pi_pos.le
  rw [h2π]
  rw [show 2 * ((2 : ℝ) ^ (-s) * Real.pi ^ (-s)) * Real.Gamma s =
    (2 * (Real.pi ^ (-s) * Real.Gamma s)) * (2 : ℝ) ^ (-s) by ring_nf]
  rw [mul_pow (2 * (Real.pi ^ (-s) * Real.Gamma s)) ((2 : ℝ) ^ (-s)) (nrComplexPlaces K),
    mul_pow (2 : ℝ) (Real.pi ^ (-s) * Real.Gamma s) (nrComplexPlaces K)]
  field_simp

end UnitDistance.NumberFieldAnalysis
