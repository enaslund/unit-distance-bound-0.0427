module

public import UnitDistance.HeckeSignedBochner
public import UnitDistance.HeckeSignedMassDifference

@[expose] public section
set_option backward.privateInPublic true


/-! Agreement of the genuine complex Mellin integral of the actual signed
class theta sum with the ordinary norm-character Dirichlet series. -/
noncomputable section
open NumberField DedekindResidue MeasureTheory
open scoped Real Classical
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- The actual signed theta Mellin transform has exactly the shifted completed
norm-character normalization, at every real point of absolute convergence. -/
theorem mellin_heckeOddSignedTotalG_real (r : K) (hr : r^2=7)
    {s : ℝ} (hs : 1 < s) :
    mellin (fun t : ℝ => (heckeOddSignedTotalG K t : ℂ)) ((s:ℂ)/2) =
      (heckeAdjust K:ℂ)*signedHeckePrefactor K (s:ℂ)*chiFourIdealSeries K (s:ℂ) := by
  rw [show (s:ℂ)/2 = ((s/2:ℝ):ℂ) by push_cast; rfl, mellin_ofReal_real]
  rw [(mellin_real_heckeOddSignedTotalG K r hr (show 1 < 2*(s/2) by linarith)).2]
  exact heckeOddSignedTotalMass_difference_complex K r hr hs

/-- The canonical signed completion constructed from the actual class theta sum. -/
def heckeSignedCompletion (s : ℂ) : ℂ :=
  (heckeAdjust K:ℂ)⁻¹ * mellin (fun t : ℝ => (heckeOddSignedTotalG K t:ℂ)) (s/2)

theorem heckeSignedCompletion_real (r : K) (hr : r^2=7) {s : ℝ} (hs : 1 < s) :
    heckeSignedCompletion K (s:ℂ) = signedHeckePrefactor K (s:ℂ)*chiFourIdealSeries K (s:ℂ) := by
  rw [heckeSignedCompletion, mellin_heckeOddSignedTotalG_real K r hr hs]
  have hn : (heckeAdjust K:ℂ) ≠ 0 := by exact_mod_cast (heckeAdjust_pos K).ne'
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end UnitDistance.NumberFieldAnalysis
