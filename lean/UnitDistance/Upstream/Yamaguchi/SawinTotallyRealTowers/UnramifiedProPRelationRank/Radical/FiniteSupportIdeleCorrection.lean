/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch. The Mathlib
4.35 Denumerable import relocation is recorded in
third-party/yamaguchi/lean-v4.35-migration.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportLocalReciprocityIdeleCharacter
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdeleFiniteValuationCharacters
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.IdeleCharacterGlobalLift

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false
/-!
# Global correction of a finite local character family

If the local reciprocity functional annihilates the ideal-power radical, exactness of
finite-valuation localization expresses it as a valuation functional. Subtracting the
corresponding continuous idele character kills all principal ideles. Global reciprocity then
gives an actual maximal abelian character agreeing with the prescribed family on local
integral units; the valuation correction changes only the unramified part.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology Classical

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP GlobalClassFieldTheory.Reciprocity

variable (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]

local instance finiteSupportIdeleCorrectionTopology : TopologicalSpace (ZMod p) := ⊥
local instance finiteSupportIdeleCorrectionDiscreteTopology : DiscreteTopology (ZMod p) :=
  discreteTopology_bot _

variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (chi : ∀ v : ↥S, ContinuousH1ZMod (p := p)
  (G := Field.absoluteGaloisGroup (v.1.adicCompletion F)))

/-- The local reciprocity product corrected by an algebraic valuation functional. -/
def finiteSupportValuationCorrectedIdeleCharacter
    (φ : Module.Dual (ZMod p) (FiniteValuationDefectModP F p)) :
    IdeleGroup F →ₜ* Multiplicative (ZMod p) where
  toFun x := finiteSupportLocalReciprocityIdeleCharacter F p S chi x /
    ideleValuationCharacter F p φ x
  map_one' := by
    simp only [map_one]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_div, toAdd_one, sub_self]
  map_mul' x y := by
    simp only [map_mul]
    exact mul_div_mul_comm _ _ _ _
  continuous_toFun :=
    (finiteSupportLocalReciprocityIdeleCharacter F p S chi).continuous_toFun.div'
      (ideleValuationCharacter F p φ).continuous_toFun

/-- A functional explaining the principal values makes the corrected character principal-trivial. -/
theorem finiteSupportValuationCorrectedIdeleCharacter_principal
    (φ : Module.Dual (ZMod p) (FiniteValuationDefectModP F p))
    (hφ : finiteValuationLocalizationDual F p φ =
      finiteSupportLocalReciprocityPowerClassFunctional F p S chi) (a : Fˣ) :
    finiteSupportValuationCorrectedIdeleCharacter F p S chi φ
      (IdeleGroup.principalIdele F a) = 1 := by
  apply Multiplicative.toAdd.injective
  change (finiteSupportLocalReciprocityIdeleCharacter F p S chi
      (IdeleGroup.principalIdele F a) /
      ideleValuationCharacter F p φ (IdeleGroup.principalIdele F a)).toAdd = 0
  rw [toAdd_div, finiteSupportLocalReciprocityIdeleCharacter_principal_functional,
    ideleValuationCharacter_principalIdele, hφ, sub_self]

/-- Valuation correction preserves every prescribed local integral-unit value. -/
theorem finiteSupportValuationCorrectedIdeleCharacter_finitePlace_integral
    (φ : Module.Dual (ZMod p) (FiniteValuationDefectModP F p))
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (ha : a ∈ (v.adicCompletionIntegers F).units) :
    finiteSupportValuationCorrectedIdeleCharacter F p S chi φ
        (IdeleGroup.finitePlaceIdele v a) =
      finiteSupportLocalReciprocityIdeleCharacter F p S chi
        (IdeleGroup.finitePlaceIdele v a) := by
  change _ / ideleValuationCharacter F p φ (IdeleGroup.finitePlaceIdele v a) = _
  rw [ideleValuationCharacter_finitePlace_integral F p φ v a ha]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_div, toAdd_one]
  exact sub_zero _

/-- Annihilating the ideal-power radical supplies a genuine global reciprocity character
with the same integral-unit values as the finite local family. -/
theorem exists_maximalAbelianCharacter_of_finiteSupport_radical_annihilator
    (hchi : absolutePowerClassDualRestriction F p
      (finiteSupportLocalReciprocityPowerClassFunctional F p S chi) = 0) :
    ∃ psi : Gal(maximalAbelianExtension F / F) →ₜ* Multiplicative (ZMod p),
      ∀ (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ),
        a ∈ (v.adicCompletionIntegers F).units →
          psi (maximalAbelianGlobalArtin F (IdeleGroup.finitePlaceIdeleClass v a)) =
            finiteSupportLocalReciprocityIdeleCharacter F p S chi
              (IdeleGroup.finitePlaceIdele v a) := by
  have hmem : finiteSupportLocalReciprocityPowerClassFunctional F p S chi ∈
      LinearMap.range (finiteValuationLocalizationDual F p) := by
    rw [finiteValuationLocalizationDual_range F p, LinearMap.mem_ker]
    exact hchi
  obtain ⟨φ, hφ⟩ := hmem
  let psi := finiteSupportValuationCorrectedIdeleCharacter F p S chi φ
  have hpsi : ∀ a : Fˣ, psi (IdeleGroup.principalIdele F a) = 1 :=
    finiteSupportValuationCorrectedIdeleCharacter_principal F p S chi φ hφ
  refine ⟨ideleCharacterMaximalAbelianLift F p psi hpsi, ?_⟩
  intro v a ha
  rw [ideleCharacterMaximalAbelianLift_artin]
  change psi (IdeleGroup.finitePlaceIdele v a) = _
  exact finiteSupportValuationCorrectedIdeleCharacter_finitePlace_integral F p S chi φ v a ha

end ClassFieldTower.Martinet.Shafarevich
