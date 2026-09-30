module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois

@[expose] public section
set_option backward.privateInPublic true


/-! Intrinsic inertia depends on the actual automorphism of the top valued
field, and is unchanged when only its fixed base field is reidentified. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ValuativeRel
namespace UnitDistance.ArithmeticProP
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
universe u
variable (K B L : Type u) [Field K] [ValuativeRel K] [Field B] [ValuativeRel B]
  [Field L] [ValuativeRel L] [Algebra K L] [Algebra B L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [Valuation.HasExtension (ValuativeRel.valuation B) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [IsIntegralClosure 𝒪[L] 𝒪[B] L]

theorem intrinsicInertia_iff_of_same_action (σ : Gal(L/K)) (τ : Gal(L/B))
    (h : ∀x,σ x=τ x) :
    σ∈(galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      τ∈(galoisGroupResidueAlgEquivHomOfIsIntegralClosure B L).ker := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal,
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal]
  apply forall_congr'
  intro x
  have he : galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x=
      galoisGroupIntegerRingEquivOfIsIntegralClosure B L τ x := by
    apply Subtype.ext
    exact h x
  rw [he]

end UnitDistance.ArithmeticProP
