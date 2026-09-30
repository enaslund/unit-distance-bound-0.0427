module

public import UnitDistance.Sqrt241.DyadicLink.Comparison
public import UnitDistance.Sqrt241.Retained.Concrete
public import UnitDistance.Sqrt241.Retained.Field
public import UnitDistance.Sqrt241.Discriminant.RootDiscriminant

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# `√β₁ ∈ M` and the root discriminant of the retained field (dyadic link, step 5)

For every `I : Retained.Input`, the retained field `M = Ω^core` contains `√β₁`:
`core ≤ retainedKer`, and `ρ_B = I.retainedMap` satisfies `ρ_B ∘ freeMap = retainedFree`,
so its kernel fixes `√β₁` (`fixes_sqrtBeta_of_retained`). With the algebra
`E → M` (`Retained.Input.genusAlgebra`), `√β₁` is a square root of
`Discriminant.beta₁ ∈ E` in `M` (`sqrtBetaM_sq`), and
`log_rootDiscriminant_le_of_sqrt_beta₁` (`Discriminant/`) gives the root-discriminant bound
`hdiscM` of `target_of_tower_data`, from the ramification indices of `M`
(`e = 8, 2, 2, 2` at `2, 3, 5, 241`, unramified elsewhere; computed in `Levels/`).
-/

open scoped NumberField
open NumberField

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.DyadicLink

open Tower CanonicalGenus UnitDistance.NumberFieldAnalysis

/-- `Discriminant.beta₁ ∈ E` is `β₁` in the closure. -/
theorem coe_beta₁ : ((Discriminant.beta₁ : CanonicalGenus.Carrier) : Closure) = beta := by
  simp only [Discriminant.beta₁, Discriminant.rootE, Discriminant.genusE, beta,
    IntermediateField.coe_add, IntermediateField.coe_mul, IntermediateField.coe_neg]
  push_cast
  rfl

variable (I : Retained.Input)

/-- Elements of `retainedKer` fix `√β₁`. -/
theorem retainedKer_fixes_tOm {σ : Ghat} (hσ : σ ∈ I.retainedKer) : σ tOm = tOm := by
  obtain ⟨hB, h1⟩ := (I.mem_retainedKer_iff σ).mp hσ
  exact fixes_sqrtBeta_of_retained I.retainedMap.toMonoidHom I.retainedMap_freeMap h1

/-- **`√β₁ ∈ M`.** -/
theorem tOm_mem_M : tOm ∈ I.M :=
  (I.mem_M_iff tOm).mpr fun _ hσ => retainedKer_fixes_tOm I (I.core_le_retainedKer hσ)

/-- `√β₁` as an element of the retained field `M`. -/
def sqrtBetaM : I.M := ⟨tOm, tOm_mem_M I⟩

@[simp] theorem coe_sqrtBetaM : (((sqrtBetaM I : I.M) : Omega) : Closure) = sqrtBeta := rfl

/-- `(√β₁)² = β₁` in `M`, with `β₁ ∈ E` mapped by `genusToM`. -/
theorem sqrtBetaM_sq : sqrtBetaM I ^ 2 = I.genusToM Discriminant.beta₁ := by
  apply Subtype.ext
  apply Subtype.ext
  rw [IntermediateField.coe_pow, IntermediateField.coe_pow, coe_sqrtBetaM,
    Retained.Input.coe_genusToM, sqrtBeta_sq, coe_beta₁]

/-- **Root discriminant of the retained field** (`hdiscM`), from the ramification indices
of `M` (computed in `Levels/`). -/
theorem log_rootDiscriminant_M_le
    (he2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 I.M) = 8)
    (he3 : (rationalPrimeIdeal 3).ramificationIdxIn (𝓞 I.M) = 2)
    (he5 : (rationalPrimeIdeal 5).ramificationIdxIn (𝓞 I.M) = 2)
    (he241 : (rationalPrimeIdeal 241).ramificationIdxIn (𝓞 I.M) = 2)
    (hunr : ∀ p : ℕ, p.Prime → p ∉ ({2, 3, 5, 241} : Finset ℕ) →
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 I.M) = 1) :
    Real.log (rootDiscriminant I.M) ≤ Witness.logRD := by
  let _ : Algebra CanonicalGenus.Carrier I.M := I.genusAlgebra
  exact log_rootDiscriminant_le_of_sqrt_beta₁ I.M (sqrtBetaM I) (sqrtBetaM_sq I) he2 he3 he5 he241
    hunr

/-- **`hdiscM` for the concrete retained field** `Retained.input.M` (built from
`Local.localElements`). -/
theorem log_rootDiscriminant_input_M_le
    (he2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 Retained.input.M) = 8)
    (he3 : (rationalPrimeIdeal 3).ramificationIdxIn (𝓞 Retained.input.M) = 2)
    (he5 : (rationalPrimeIdeal 5).ramificationIdxIn (𝓞 Retained.input.M) = 2)
    (he241 : (rationalPrimeIdeal 241).ramificationIdxIn (𝓞 Retained.input.M) = 2)
    (hunr : ∀ p : ℕ, p.Prime → p ∉ ({2, 3, 5, 241} : Finset ℕ) →
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 Retained.input.M) = 1) :
    Real.log (rootDiscriminant Retained.input.M) ≤ Witness.logRD :=
  log_rootDiscriminant_M_le Retained.input he2 he3 he5 he241 hunr

end UnitDistance.Sqrt241.DyadicLink
