module

public import UnitDistance.RelativeCompletionValuation

@[expose] public section
set_option backward.privateInPublic true


/-! # Continuity of the actual valuation-preserving field maps -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical Topology
open NumberField IsDedekindDomain WithZero

namespace UnitDistance.RelativeCompletion

/-- Exact valuation preservation gives continuity of an actual ring map
between fields with surjective integer valuations. -/
theorem continuous_of_valuation_preserving {E L : Type*} [Field E] [Field L]
    [Valued E ℤᵐ⁰] [Valued L ℤᵐ⁰] (f : E →+* L)
    (hE : Function.Surjective (Valued.v : Valuation E ℤᵐ⁰))
    (hf : ∀ x, (Valued.v : Valuation L ℤᵐ⁰) (f x) = Valued.v x) : Continuous f := by
  apply continuous_of_continuousAt_zero f
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
  let r : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
  have hr : r ≠ 0 := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  obtain ⟨b, hb⟩ := hE r
  have hopen : IsOpen {x : E | Valued.v x < r} := by
    have hh := Valued.isOpen_ball E ((Valued.v : Valuation E ℤᵐ⁰).restrict b)
    simpa only [Valuation.restrict_lt_iff, hb] using hh
  have hzero : (0 : E) ∈ {x : E | Valued.v x < r} := by
    simpa only [Set.mem_setOf_eq, map_zero] using
      MonoidWithZeroHom.ValueGroup₀.embedding_unit_pos γ
  apply Filter.mem_of_superset (hopen.mem_nhds hzero)
  intro x hx
  apply hγ
  change (Valued.v : Valuation L ℤᵐ⁰).restrict (f x) < γ.val
  rw [Valuation.restrict_lt_iff_lt_embedding, hf]
  exact hx

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- Actual field involution viewed between the two valued copies of K. -/
def valuedInvolution (ι : K ≃ₐ[F] K) (v w : HeightOneSpectrum (𝓞 K)) :
    WithVal (v.valuation K) ≃+* WithVal (w.valuation K) :=
  WithVal.congr (v.valuation K) (w.valuation K) ι.toRingEquiv

theorem valuedInvolution_continuous (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    Continuous (valuedInvolution ι v w) := by
  apply continuous_of_valuation_preserving (valuedInvolution ι v w).toRingHom
  · exact (v.valuation_surjective K).comp (WithVal.equiv (v.valuation K)).surjective
  · intro x
    exact valuation_involution ι v w hw ((WithVal.equiv (v.valuation K)) x)

theorem valuedInvolution_symm_continuous (ι : K ≃ₐ[F] K)
    (v w : HeightOneSpectrum (𝓞 K)) (hw : w.asIdeal = RelativeIdealCosets.conjugateIdeal ι v.asIdeal) :
    Continuous (valuedInvolution ι v w).symm := by
  apply continuous_of_valuation_preserving (valuedInvolution ι v w).symm.toRingHom
  · exact (w.valuation_surjective K).comp (WithVal.equiv (w.valuation K)).surjective
  · intro x
    change v.valuation K (ι.symm ((WithVal.equiv (w.valuation K)) x)) =
      w.valuation K ((WithVal.equiv (w.valuation K)) x)
    simpa only [AlgEquiv.apply_symm_apply] using
      (valuation_involution ι v w hw (ι.symm ((WithVal.equiv (w.valuation K)) x))).symm

end UnitDistance.RelativeCompletion
