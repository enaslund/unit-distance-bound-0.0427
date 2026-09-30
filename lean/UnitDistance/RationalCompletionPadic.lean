module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.Comparison
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalizedValuation
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

@[expose] public section
set_option backward.privateInPublic true


/-! The actual rational norm completion and the usual p-adic field. -/
noncomputable section
open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
namespace UnitDistance.ArithmeticProP

private local instance rationalCompletionPrimeFact (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private noncomputable instance rationalAdicCompletionAlgebra
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (HeightOneSpectrum.adicAbv ℚ v).Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := ℚ)
    (HeightOneSpectrum.adicAbv ℚ v)

/-- The absolute-value completion at a rational prime is the usual p-adic field,
with the actual scalar map and both topologies preserved. -/
def rationalCompletionPadic (v : HeightOneSpectrum (𝓞 ℚ)) :
    (HeightOneSpectrum.adicAbv ℚ v).Completion ≃A[ℚ]
      ℚ_[Rat.HeightOneSpectrum.primesEquiv v] := by
  let e : (HeightOneSpectrum.adicAbv ℚ v).Completion ≃ᵢ v.adicCompletion ℚ :=
    { toEquiv := relativeFinitePlaceCompletionRingEquiv v
      isometry_toFun := relativeFinitePlaceCompletionRingHom_isometry v }
  let a : (HeightOneSpectrum.adicAbv ℚ v).Completion ≃A[ℚ] v.adicCompletion ℚ :=
    { toAlgEquiv := (relativeFinitePlaceCompletionRingEquiv v).toRatAlgEquiv
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  exact a.trans (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)

@[simp]
theorem rationalCompletionPadic_apply (v : HeightOneSpectrum (𝓞 ℚ))
    (x : (HeightOneSpectrum.adicAbv ℚ v).Completion) :
    rationalCompletionPadic v x =
      Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
        (relativeFinitePlaceCompletionAlgEquiv v x) := rfl

/-- The canonical comparison preserves the unit ball exactly. -/
theorem rationalCompletionPadic_norm_le_one_iff (v : HeightOneSpectrum (𝓞 ℚ))
    (x : (HeightOneSpectrum.adicAbv ℚ v).Completion) :
    ‖rationalCompletionPadic v x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have he (y : v.adicCompletion ℚ) :
      ‖e y‖ ≤ 1 ↔ y ∈ v.adicCompletionIntegers ℚ := by
    have h := Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v
    constructor
    · intro hy
      obtain ⟨z,hz,hzy⟩ := h.surjOn hy
      exact e.injective hzy ▸ hz
    · intro hy
      exact h.mapsTo hy
  rw [rationalCompletionPadic_apply, he]
  constructor
  · intro hx
    have hn := norm_le_one_of_mem_adicCompletionIntegers v hx
    simpa only [show (relativeFinitePlaceCompletionAlgEquiv v : _ → _) =
      relativeFinitePlaceCompletionRingEquiv v from rfl,
      relativeFinitePlaceCompletionRingEquiv_norm] using hn
  · intro hx
    apply mem_adicCompletionIntegers_of_norm_le_one v
    simpa only [show (relativeFinitePlaceCompletionAlgEquiv v : _ → _) =
      relativeFinitePlaceCompletionRingEquiv v from rfl,
      relativeFinitePlaceCompletionRingEquiv_norm] using hx

/-- The intrinsic valuation ring on the norm completion maps to the usual
p-adic integer unit ball. -/
theorem rationalCompletionPadic_mem_integers_iff (v : HeightOneSpectrum (𝓞 ℚ))
    (x : (HeightOneSpectrum.adicAbv ℚ v).Completion) :
    letI := finitePlaceCompletionValuativeRel (HeightOneSpectrum.adicAbv ℚ v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv ℚ v)
    x ∈ 𝒪[(HeightOneSpectrum.adicAbv ℚ v).Completion] ↔
      ‖rationalCompletionPadic v x‖ ≤ 1 := by
  rw [finitePlaceCompletion_mem_integers_iff_norm_le_one,
    rationalCompletionPadic_norm_le_one_iff]

/-- The explicit complete-DVF valuation ring on Qp is exactly its unit ball. -/
theorem mem_padicCompleteDVF_valuationSubring_iff (p : ℕ) [Fact p.Prime]
    (x : ℚ_[p]) : x ∈ (padicCompleteDVF p).valuation.valuationSubring ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro hx
    obtain ⟨z,hz⟩ := (padicIntEquivValuationSubring p).surjective ⟨x,hx⟩
    have he : (z : ℚ_[p]) = x := congrArg Subtype.val hz
    rw [← he]
    exact z.property
  · intro hx
    exact (padicIntEquivValuationSubring p ⟨x,hx⟩).property

/-- The actual valuation subrings agree through the p-adic comparison. -/
theorem rationalCompletionPadic_valuationSubring (v : HeightOneSpectrum (𝓞 ℚ))
    (x : (HeightOneSpectrum.adicAbv ℚ v).Completion) :
    letI := finitePlaceCompletionValuativeRel (HeightOneSpectrum.adicAbv ℚ v)
      (HeightOneSpectrum.isNonarchimedean_adicAbv ℚ v)
    x ∈ 𝒪[(HeightOneSpectrum.adicAbv ℚ v).Completion] ↔
      rationalCompletionPadic v x ∈
        (padicCompleteDVF (Rat.HeightOneSpectrum.primesEquiv v)).valuation.valuationSubring := by
  rw [rationalCompletionPadic_mem_integers_iff,
    mem_padicCompleteDVF_valuationSubring_iff]

end UnitDistance.ArithmeticProP
