module

public import UnitDistance.RelativeHeckeEntireComparison

@[expose] public section
set_option backward.privateInPublic true


/-! Raising the discriminant parameter preserves the actual comparison. -/
noncomputable section
open Filter Set Complex NumberField NumberField.InfinitePlace DedekindResidue
open scoped Topology
namespace UnitDistance.NumberFieldAnalysis
variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

theorem relativeCompletedReal_change_ell (ell₀ ell s : ℝ) :
    relativeCompletedReal K F ell s =
      Real.exp (((nrRealPlaces F:ℝ)+2*(nrComplexPlaces F:ℝ))*s/2*(ell-ell₀)) *
        relativeCompletedReal K F ell₀ s := by
  unfold relativeCompletedReal
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  unfold relativeGammaLog
  ring

theorem relativeCompletedReal_monotoneOn_raise_ell {ell₀ ell : ℝ} (hle : ell₀ ≤ ell)
    (hmono : MonotoneOn (relativeCompletedReal K F ell₀) (Ici 1)) :
    MonotoneOn (relativeCompletedReal K F ell) (Ici 1) := by
  intro s hs t ht hst
  rw [relativeCompletedReal_change_ell K F ell₀ ell s,
    relativeCompletedReal_change_ell K F ell₀ ell t]
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    have hc : 0 ≤ ((nrRealPlaces F:ℝ)+2*(nrComplexPlaces F:ℝ))/2*(ell-ell₀) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hst hc]
  · exact hmono hs ht hst
  · exact (relativeCompletedReal_pos K F ell₀ hs).le
  · exact Real.exp_nonneg _

/-- An upper bound on the actual discriminant ratio suffices; equality with
the common family parameter is not needed. -/
theorem relativeCompletedReal_monotoneOn_of_entire_factor_discr_le {L : ℂ → ℂ}
    (hL : Differentiable ℂ L)
    (hfactor : ∀ s, completedDedekindZetaEntire K s = completedDedekindZetaEntire F s*L s)
    {ell : ℝ} (hreal : nrRealPlaces K = 0)
    (hcomplex : nrComplexPlaces K = nrRealPlaces F+2*nrComplexPlaces F)
    (hdiscr : Real.log |(discr K : ℝ)|-Real.log |(discr F : ℝ)| ≤
      (Module.finrank ℚ F : ℝ)*ell) :
    MonotoneOn (relativeCompletedReal K F ell) (Ici 1) := by
  have hd : (0:ℝ) < Module.finrank ℚ F := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  let ell₀ := (Real.log |(discr K : ℝ)|-Real.log |(discr F : ℝ)|)/(Module.finrank ℚ F : ℝ)
  apply relativeCompletedReal_monotoneOn_raise_ell K F (ell₀ := ell₀)
  · exact (div_le_iff₀ hd).mpr (by simpa [mul_comm] using hdiscr)
  · apply relativeCompletedReal_monotoneOn_of_entire_factor K F hL hfactor hreal hcomplex
    dsimp [ell₀]
    field_simp

end UnitDistance.NumberFieldAnalysis
