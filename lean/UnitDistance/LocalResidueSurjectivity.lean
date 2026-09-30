module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension

@[expose] public section
set_option backward.privateInPublic true


/-! Surjectivity of the actual residue action for every finite Galois local extension. -/
noncomputable section
open scoped ValuativeRel
namespace UnitDistance.ArithmeticProP
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

theorem intrinsicResidueInertia_index :
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker.index=
      Module.finrank 𝓀[K] 𝓀[L] := by
  let r := galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L
  have hc := r.ker.card_mul_index
  have hd := maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank_of_isIntegralClosure K L
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (IsDiscreteValuationRing.not_a_field 𝒪[K]),
    ← galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_ramificationIdx K L,
    ← IsGalois.card_aut_eq_finrank K L] at hd
  have hp : 0<Nat.card r.ker := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hp (hc.trans hd.symm)

/-- No unramifiedness hypothesis is needed for surjectivity onto residue automorphisms. -/
theorem intrinsicResidueAction_surjective :
    Function.Surjective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L) := by
  let r := galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.eq_top_of_card_eq
  rw [← Subgroup.index_ker,intrinsicResidueInertia_index,residueAlgEquiv_card_eq_finrank]

end UnitDistance.ArithmeticProP
