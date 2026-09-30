module

public import UnitDistance.SigmaRamification
public import UnitDistance.MaximalProTwoSigma

@[expose] public section
set_option backward.privateInPublic true


/-! Every actual finite Galois field embedded in the constructed maximal
Sigma extension is unramified away from the literal integer30030. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain
namespace UnitDistance.ArithmeticProP
open QuadraticRamification ClassFieldTower.Sawin
variable (K : Type*) [Field K] [NumberField K]

/-- The actual finite-place support predicate also implies the literal
integer-support predicate, including its zero-prime case. -/
theorem unramifiedAway_of_unramifiedOutsideSigma
    (h : IsUnramifiedAtFinitePlacesOutside ℚ K sigmaPrimeSupport) : UnramifiedAway K 30030 := by
  intro P hP hN
  by_cases hP0 : P=⊥
  · subst P
    exact Algebra.isUnramifiedAt_bot
  let W : HeightOneSpectrum (𝓞 K) := ⟨P,hP,hP0⟩
  let V := finitePlaceBelow (K := ℚ) W
  have hv : V∉sigmaPrimeSupport := by
    rw [mem_sigmaPrimeSupport_iff]
    intro hVN
    apply hN
    change algebraMap (𝓞 ℚ) (𝓞 K) 30030∈P at hVN
    simpa only [map_ofNat,Int.cast_ofNat] using hVN
  letI : P.LiesOver V.asIdeal := ⟨rfl⟩
  letI : V.asIdeal.IsPrime := V.isPrime
  letI : Algebra.IsUnramifiedAt (𝓞 ℚ) P := h W hv
  letI : Algebra.IsUnramifiedAt ℤ V.asIdeal :=
    unramifiedAway_rat 1 V.asIdeal (by
      intro h
      apply V.isPrime.ne_top
      exact (Ideal.eq_top_iff_one _).mpr (by simpa only [Int.cast_one] using h))
  exact Algebra.IsUnramifiedAt.comp V.asIdeal P

variable [IsGalois ℚ K]

/-- Actual containment in the maximal extension supplies its finite support;
no ramification hypothesis on the finite field is assumed. -/
theorem unramifiedAway_of_embedding_maximalSigma
    (j : K →ₐ[ℚ] maximalSigmaProTwo) : UnramifiedAway K 30030 := by
  let f : K →ₐ[ℚ] AlgebraicClosure ℚ := maximalSigmaProTwo.val.comp j
  let E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    { toIntermediateField := f.fieldRange
      finiteDimensional := f.equivFieldRange.toLinearEquiv.finiteDimensional
      isGalois := IsGalois.of_algEquiv f.equivFieldRange }
  letI : Module.Finite ℚ E.toIntermediateField := E.finiteDimensional
  letI : NumberField E := NumberField.of_module_finite ℚ E
  have hE : E.toIntermediateField≤maximalSigmaProTwo := by
    rintro _ ⟨x,rfl⟩
    exact (j x).property
  have hu := (finiteLayer_le_maximalSigmaProTwo_iff E).mp hE
  have hr : UnramifiedAway E 30030 := unramifiedAway_of_unramifiedOutsideSigma E hu.2
  exact hr.of_algEquiv f.equivFieldRange.symm

end UnitDistance.ArithmeticProP
