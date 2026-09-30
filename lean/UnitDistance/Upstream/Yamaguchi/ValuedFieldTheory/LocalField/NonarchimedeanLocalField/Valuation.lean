/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNorm
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm

@[expose] public section
set_option backward.privateInPublic true

/-!
# Integer-valued valuations

Relates membership in the valuation ring to the ambient valuation and exposes
the associated surjective multiplicative valuation with a uniformizer.
-/

set_option autoImplicit false

namespace LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open DiscreteValuationField
open scoped ValuativeRel

/-- An element belongs to the valuation ring exactly when its valuation is at most one. -/
theorem valuation_integer_membership
    (K : Type u) [Field K] [ValuativeRel K] (x : K) :
    x ∈ 𝒪[K] ↔ ValuativeRel.valuation K x ≤ 1 :=
  (Valuation.mem_integer_iff (ValuativeRel.valuation K) x).symm

/-- The normalized integer valuation, packaged as the
`MultiplicativeIntegerValuation` used by the value-group layer. -/
def multiplicativeIntegerValuation
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    MultiplicativeIntegerValuation Kˣ where
  val x := LocalFieldTheory.IsNonarchimedeanLocalField.v K (Additive.ofMul x)
  map_one := by
    exact LocalFieldTheory.IsNonarchimedeanLocalField.v_one K
  map_mul x y := by
    exact LocalFieldTheory.IsNonarchimedeanLocalField.v_mul K x y

/-- The multiplicative integer valuation records the additive integer exponent of the original
valuation. -/
@[simp] theorem multiplicativeIntegerValuation_val
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) :
    (multiplicativeIntegerValuation K).val x =
      LocalFieldTheory.IsNonarchimedeanLocalField.v K (Additive.ofMul x) :=
  rfl

/-- The normalized integer valuation is onto `ℤ`. -/
theorem multiplicativeIntegerValuation_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Surjective (multiplicativeIntegerValuation K).val := by
  intro n
  rcases LocalFieldTheory.IsNonarchimedeanLocalField.v_surjective K n with ⟨x, hx⟩
  refine ⟨Additive.toMul x, ?_⟩
  simpa [multiplicativeIntegerValuation] using hx

/-- A nonarchimedean local field has a multiplicative element of normalized value one
for the value-group API. -/
theorem multiplicativeIntegerValuation_exists_uniformizer
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ ϖ : Kˣ, (multiplicativeIntegerValuation K).IsUniformizer ϖ :=
  (multiplicativeIntegerValuation K).exists_uniformizer_of_surjective
    (multiplicativeIntegerValuation_surjective K)

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
