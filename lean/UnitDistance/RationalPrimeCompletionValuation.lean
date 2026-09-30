module

public import UnitDistance.RationalPrimeCompletion
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceInertiaTransport
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF

@[expose] public section
set_option backward.privateInPublic true


/-! The tame-field valuation agrees with the intrinsic local-field valuation
above the actual rational finite-place completion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open scoped NumberField ValuativeRel
namespace UnitDistance.PrimeCompletion
open ClassFieldTower.Martinet.Shafarevich
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open ValuationTheory.DiscreteValuationField.ValuedExtension
attribute [local instance] primeFact baseRationalAlgebra

instance baseLocalField (p : Nat.Primes) : IsNonarchimedeanLocalField (Base p) :=
  finitePlaceNormCompletionIsNonarchimedeanLocalField ℚ (place p)

variable (p : Nat.Primes) (L : Type) [Field L] [Algebra ℚ_[p.val] L]
  [FiniteDimensional ℚ_[p.val] L] [IsGalois ℚ_[p.val] L]
  [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation (Base p)) (ValuativeRel.valuation L)]

omit [FiniteDimensional ℚ_[p.val] L] [IsGalois ℚ_[p.val] L] in
theorem padicBase_hasExtension :
    (PadicFiniteGalois.base (p.val)).valuation.HasExtension
      (ValuativeRel.valuation L) := by
  apply Valuation.HasExtension.ofComapInteger
  ext q
  obtain ⟨x,rfl⟩ := (equiv p).surjective q
  change (ValuativeRel.valuation L)
      (algebraMap ℚ_[p.val] L (equiv p x))≤1 ↔
    (PadicFiniteGalois.base (p.val)).valuation (equiv p x)≤1
  have hmap : algebraMap (Base p) L x=
      algebraMap ℚ_[p.val] L (equiv p x) := rfl
  rw [←hmap,Valuation.HasExtension.val_map_le_one_iff
    (ValuativeRel.valuation (Base p)) (ValuativeRel.valuation L)]
  exact equiv_integers p x

/-- Uniqueness of valuation extension identifies the actual tame valuation
with any intrinsic valuation extending the genuine completion. -/
theorem intrinsicCompatible :
    (PadicFiniteGalois.target (p.val) L).valuation.Compatible := by
  letI := padicBase_hasExtension p L
  have h := valuation_isEquiv_of_finite_separable
    (PadicFiniteGalois.base (p.val))
    (PadicFiniteGalois.target (p.val) L) (ValuativeRel.valuation L)
  refine ⟨fun x y ↦ ?_⟩
  exact (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation L) x y).trans (h x y).symm

end UnitDistance.PrimeCompletion
