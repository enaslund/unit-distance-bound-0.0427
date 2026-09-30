module

public import UnitDistance.StudentFourierEnvelope
public import UnitDistance.FourierGaussianRegularization

@[expose] public section
set_option backward.privateInPublic true


/-! The original Student envelope supplies the actual Schwartz regularizations. -/

open MeasureTheory FourierTransform Filter

namespace UnitDistance.Witness

theorem fourierTubeConstant_pos : 0 < fourierTubeConstant := by
  have hq : (0:ℝ) ≤ (fourierTubeLoss:ℝ) := by exact_mod_cast fourierTubeLoss_nonneg
  unfold fourierTubeConstant
  positivity

/-- Every fixed loss greater than one holds uniformly in frequency for the
actual published-profile Schwartz approximants. There is no remaining
original Fourier-envelope hypothesis. -/
theorem pairSchwartzApprox_student_fourier_envelope_eventually {η : ℝ} (hη : 1 < η) :
    ∀ᶠ n in atTop, ∀ ξ : StudentEuclideanPair,
      ‖𝓕 (pairSchwartzApprox n) ξ‖ ≤
        η*(fourierTubeConstant*pairMass)*
          Real.exp (-studentFourierSigma*(‖(WithLp.ofLp ξ).1‖+‖(WithLp.ofLp ξ).2‖)) :=
  pairSchwartzApprox_coordinate_fourier_envelope_eventually
    (mul_pos fourierTubeConstant_pos pairMass_pos).le studentFourierSigma_pos.le
    pairProfile_fourier_envelope hη

end UnitDistance.Witness
