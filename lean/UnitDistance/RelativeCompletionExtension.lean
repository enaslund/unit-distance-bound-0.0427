module

public import UnitDistance.RelativeCompletionContinuity

@[expose] public section
set_option backward.privateInPublic true


/-! # Extension on the explicit uniform-space completions -/

noncomputable section
set_option maxHeartbeats 400000
open scoped NumberField nonZeroDivisors Classical Topology
open NumberField IsDedekindDomain WithZero

namespace UnitDistance.RelativeCompletion

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

local instance valuedCopyTopologicalRing (v : HeightOneSpectrum (𝓞 K)) :
    IsTopologicalRing (WithVal (v.valuation K)) :=
  Valued.instIsTopologicalRing (Γ₀ := ℤᵐ⁰)

local instance completedCopyTopologicalRing (v : HeightOneSpectrum (𝓞 K)) :
    IsTopologicalRing (UniformSpace.Completion (WithVal (v.valuation K))) :=
  UniformSpace.Completion.topologicalRing

/-- The actual involution as a uniform equivalence of the two valued copies. -/
def valuedUniformEquiv (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    WithVal (v.valuation K) ≃ᵤ WithVal (w.valuation K) where
  toEquiv := (valuedInvolution ι v w).toEquiv
  uniformContinuous_toFun := uniformContinuous_addMonoidHom_of_continuous
    (valuedInvolution_continuous ι v w hw)
  uniformContinuous_invFun := uniformContinuous_addMonoidHom_of_continuous
    (valuedInvolution_symm_continuous ι v w hw)

/-- The literal uniform extension to completions. -/
def completedUniformEquiv (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    UniformSpace.Completion (WithVal (v.valuation K)) ≃ᵤ
      UniformSpace.Completion (WithVal (w.valuation K)) :=
  UniformSpace.Completion.mapEquiv (valuedUniformEquiv ι v w hw)

/-- The uniform extension is an actual ring equivalence, by density. -/
def completedValuedInvolution (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    UniformSpace.Completion (WithVal (v.valuation K)) ≃+*
      UniformSpace.Completion (WithVal (w.valuation K)) :=
  UniformSpace.Completion.mapRingEquiv (valuedInvolution ι v w)
    (valuedInvolution_continuous ι v w hw) (valuedInvolution_symm_continuous ι v w hw)

@[simp] theorem completedValuedInvolution_coe (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal)
    (x : WithVal (v.valuation K)) :
    completedValuedInvolution ι v w hw (x : UniformSpace.Completion _) =
      (valuedInvolution ι v w x : UniformSpace.Completion _) :=
  UniformSpace.Completion.mapRingHom_coe (valuedInvolution_continuous ι v w hw) x

end UnitDistance.RelativeCompletion
