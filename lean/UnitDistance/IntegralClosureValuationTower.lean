module

public import UnitDistance.FiniteInertiaRestriction

@[expose] public section
set_option backward.privateInPublic true


/-! Compatibility of the actual valuations in a finite integral-closure tower.
The upper valuation need not have been chosen by spectral norm. -/
noncomputable section
open scoped ValuativeRel
namespace UnitDistance.ArithmeticProP
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField

/-- If both valuation rings are the actual integral closures of the same base,
the upper valuation extends the intermediate valuation. -/
theorem valuation_hasExtension_of_integralClosure_tower
    (K E L : Type) [Field K] [ValuativeRel K]
    [Field E] [ValuativeRel E] [Field L] [ValuativeRel L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E)]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[E] 𝒪[K] E] [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Valuation.HasExtension (ValuativeRel.valuation E) (ValuativeRel.valuation L) := by
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change algebraMap E L x ∈ 𝒪[L] ↔ x ∈ 𝒪[E]
  have he : x ∈ 𝒪[E] ↔ IsIntegral 𝒪[K] x := by
    constructor
    · intro hx
      exact (IsIntegralClosure.isIntegral_iff (A := 𝒪[E]) (R := 𝒪[K]) (B := E)).2
        ⟨⟨x,hx⟩,rfl⟩
    · intro hx
      obtain ⟨y,hy⟩ := (IsIntegralClosure.isIntegral_iff
        (A := 𝒪[E]) (R := 𝒪[K]) (B := E)).1 hx
      exact hy ▸ y.property
  have hl : algebraMap E L x ∈ 𝒪[L] ↔ IsIntegral 𝒪[K] (algebraMap E L x) := by
    constructor
    · intro hx
      exact (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2
        ⟨⟨algebraMap E L x,hx⟩,rfl⟩
    · intro hx
      obtain ⟨y,hy⟩ := (IsIntegralClosure.isIntegral_iff
        (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).1 hx
      exact hy ▸ y.property
  rw [he,hl]
  exact isIntegral_algebraMap_iff (R := 𝒪[K]) (A := E) (B := L)

end UnitDistance.ArithmeticProP
