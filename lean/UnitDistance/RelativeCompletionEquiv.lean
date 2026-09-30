module

public import UnitDistance.RelativeCompletionExtension

@[expose] public section
set_option backward.privateInPublic true


/-! # The actual involution between partner prime completions -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical Topology
open NumberField IsDedekindDomain WithZero

namespace UnitDistance.RelativeCompletion

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- The actual involution extends to an actual field equivalence between
conjugate prime completions. -/
def completionInvolution (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    v.adicCompletion K ≃+* w.adicCompletion K :=
  (HeightOneSpectrum.adicCompletion.equiv K v).trans
    ((completedValuedInvolution ι v w hw).trans
        (HeightOneSpectrum.adicCompletion.equiv K w).symm)

/-- The completed equivalence is exactly the field involution on the dense
actual field embeddings. -/
theorem completionInvolution_field (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal)
    (x : K) :
    completionInvolution ι v w hw (algebraMap K (v.adicCompletion K) x) =
      algebraMap K (w.adicCompletion K) (ι x) := by
  change HeightOneSpectrum.adicCompletion.ofCompletion
    (completedValuedInvolution ι v w hw
        (((WithVal.equiv (v.valuation K)).symm x : WithVal (v.valuation K)) :
          UniformSpace.Completion (WithVal (v.valuation K)))) = _
  rw [completedValuedInvolution_coe]
  rfl

theorem completionInvolution_continuous (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    Continuous (completionInvolution ι v w hw) := by
  exact (HeightOneSpectrum.adicCompletion.uniformEquiv K w).symm.continuous.comp
    ((completedUniformEquiv ι v w hw).continuous.comp
      (HeightOneSpectrum.adicCompletion.uniformEquiv K v).continuous)

theorem completionInvolution_symm_continuous (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    Continuous (completionInvolution ι v w hw).symm := by
  exact (HeightOneSpectrum.adicCompletion.uniformEquiv K v).symm.continuous.comp
    ((completedUniformEquiv ι v w hw).symm.continuous.comp
      (HeightOneSpectrum.adicCompletion.uniformEquiv K w).continuous)

/-- The actual completed field equivalence, with both continuity directions. -/
def completionHomeomorph (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    v.adicCompletion K ≃ₜ w.adicCompletion K where
  toEquiv := (completionInvolution ι v w hw).toEquiv
  continuous_toFun := completionInvolution_continuous ι v w hw
  continuous_invFun := completionInvolution_symm_continuous ι v w hw

open scoped WithZeroTopology in
/-- The completed equivalence preserves the actual extended integer valuation. -/
theorem completionInvolution_valuation (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal)
    (x : v.adicCompletion K) :
    (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰) (completionInvolution ι v w hw x) =
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) x := by
  have he := (v.denseRange_algebraMap K).equalizer
    ((Valued.continuous_valuation_of_surjective
      (HeightOneSpectrum.valuedAdicCompletion_surjective K w)).comp
        (completionInvolution_continuous ι v w hw))
    (Valued.continuous_valuation_of_surjective
      (HeightOneSpectrum.valuedAdicCompletion_surjective K v))
    (show (fun x ↦ (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰)
        (completionInvolution ι v w hw x)) ∘ algebraMap K (v.adicCompletion K) =
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) ∘ algebraMap K (v.adicCompletion K) from by
        funext a
        simp only [Function.comp_apply, completionInvolution_field,
          SIntegerCRT.valued_field, valuation_involution ι v w hw])
  exact congrFun he x

/-- Canonical Haar valuation normalization is also preserved exactly. -/
theorem completionInvolution_intValuation (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal)
    (x : v.adicCompletion K) :
    Local.ValuedHaar.intValuation (w.adicCompletion K) (completionInvolution ι v w hw x) =
      Local.ValuedHaar.intValuation (v.adicCompletion K) x := by
  rw [SIntegerCRT.canonical_intValuation_eq, SIntegerCRT.canonical_intValuation_eq]
  exact completionInvolution_valuation ι v w hw x

end UnitDistance.RelativeCompletion
