/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.HilbertRamification.RamificationDepth
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Compatibility of valuation-ring actions with Galois restriction

For a normal field tower `M / L / K` with uniquely extended discrete
valuations, the valuation-ring action of an automorphism of `M / K` on an
element coming from `L` is the image of the valuation-ring action of its
restriction to `L / K`.
-/

noncomputable section

universe u v w x y z

namespace RamificationTheory.HilbertRamification
namespace Higher

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} {L : Type w} {M : Type y}
variable [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra K M] [Algebra L M]
variable [IsScalarTower K L M] [Normal K L]
variable {base : DVF.{u, v} K}
variable {middle : DVF.{w, x} L}
variable {target : DVF.{y, z} M}
variable [base.valuation.HasExtension middle.valuation]
variable [middle.valuation.HasExtension target.valuation]
variable [base.valuation.HasExtension target.valuation]

/-- Acting on an integral element from a normal intermediate field and then
viewing it in the top valuation ring agrees with first restricting the
Galois automorphism and acting in the intermediate valuation ring. -/
theorem
    valuationSubringAutOfUniqueExtension_integerMap_restrictNormal
    (hmiddle :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base middle)
    (htarget :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base target)
    (σ : Gal(M / K)) (a : middle.valuationSubring) :
    valuationSubringAutOfUniqueExtension
          (base := base) (target := target) htarget σ
          (integerMap middle target a) =
      integerMap middle target
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := middle) hmiddle
          (σ.restrictNormal L) a) := by
  apply Subtype.ext
  change
    σ (algebraMap L M (a : L)) =
      algebraMap L M ((σ.restrictNormal L) (a : L))
  exact (AlgEquiv.restrictNormal_commutes σ L (a : L)).symm

end Higher
end RamificationTheory.HilbertRamification

end
