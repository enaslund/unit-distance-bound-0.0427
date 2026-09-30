module

public import UnitDistance.RelativeDiscriminant
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.NumberTheory.RamificationInertia.Galois

@[expose] public section
set_option backward.privateInPublic true


/-! Relative finite unramifiedness from equality of actual absolute ramification indices. -/
noncomputable section
open NumberField IsDedekindDomain
namespace UnitDistance.NumberFieldAnalysis
variable (M K : Type*) [Field M] [NumberField M] [Field K] [NumberField K] [Algebra M K]

/-- Equality of actual absolute ramification indices forces every relative
ramification index to be one, hence actual finite unramifiedness. -/
theorem finiteUnramified_of_absolute_ramificationIdx_eq
    (h : ∀ P : HeightOneSpectrum (𝓞 K),
      P.asIdeal.ramificationIdx ℤ = (P.under (𝓞 M)).asIdeal.ramificationIdx ℤ) :
    FiniteUnramified M K := by
  intro P hP
  letI := hP
  by_cases hP0 : P=⊥
  · subst P
    exact Algebra.isUnramifiedAt_bot
  let W : HeightOneSpectrum (𝓞 K) := ⟨P,hP.isPrime,hP0⟩
  let V := W.under (𝓞 M)
  letI : P.LiesOver V.asIdeal := ⟨rfl⟩
  letI := V.isPrime
  have ht := Ideal.ramificationIdx_tower (R := ℤ) V.asIdeal P
  have he := h W
  have hp : 0 < V.asIdeal.ramificationIdx ℤ := Ideal.ramificationIdx_pos V.asIdeal ℤ
  have hrel : P.ramificationIdx (𝓞 M)=1 := by
    change P.ramificationIdx ℤ=V.asIdeal.ramificationIdx ℤ at he
    rw [he] at ht
    nlinarith
  exact Ideal.ramificationIdx_eq_one_iff.mp hrel

end UnitDistance.NumberFieldAnalysis
