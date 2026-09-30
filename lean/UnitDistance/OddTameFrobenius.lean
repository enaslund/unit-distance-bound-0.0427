module

public import UnitDistance.OddTameCharacter
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.HilbertRamification.CompleteDVF
public import Mathlib.FieldTheory.Finite.Extension

@[expose] public section
set_option backward.privateInPublic true


/-! Actual Frobenius lifts for complete discretely valued fields with finite residue fields. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w x
namespace UnitDistance.OddTame
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField.ResidueField
open ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
  (base : CompleteDVF.{u,v} K) (target : CompleteDVF.{w,x} L)
  [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] [IsGalois K L]

theorem completeUnique : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
    base.toDVF target.toDVF :=
  ValuedExtension.hasUniqueValuationExtension_of_finite_separable base target

theorem residueAction_apply_residue (σ : Gal(L/K)) (a : target.valuationSubring) :
    RamificationTheory.HilbertRamification.CompleteDVF.residueAction
      (base:=base) (target:=target) σ (target.residueMap a) =
      target.residueMap (valuationSubringAutOfUniqueExtension (completeUnique base target) σ a) := by
  rfl

/-- A genuine automorphism lifting arithmetic Frobenius, with its actual action
on every integral residue and hence on every residue unit. -/
theorem exists_frobenius [Finite base.residueField] [Finite target.residueField] :
    ∃ φ : Gal(L/K), ∀ a : target.valuationSubring,
      target.residueMap (valuationSubringAutOfUniqueExtension (completeUnique base target) φ a)=
        (target.residueMap a)^(Nat.card base.residueField) := by
  letI := Fintype.ofFinite base.residueField
  let F := FiniteField.frobeniusAlgEquivOfAlgebraic base.residueField target.residueField
  obtain ⟨φ,hφ⟩ := RamificationTheory.HilbertRamification.CompleteDVF.residueAction_surjective_of_isGalois
    (base:=base) (target:=target) F
  refine ⟨φ, fun a ↦ ?_⟩
  rw [← residueAction_apply_residue, hφ]
  simp [F, Nat.card_eq_fintype_card]

theorem exists_frobenius_unit [Finite base.residueField] [Finite target.residueField] :
    ∃ φ : Gal(L/K), ∀ a : target.valuationSubringˣ,
      residueUnit (dvfValuationSubringUnitAut (completeUnique base target) φ a)=
        (residueUnit a)^(Nat.card base.residueField) := by
  obtain ⟨φ,hφ⟩ := exists_frobenius base target
  refine ⟨φ, fun a ↦ Units.ext ?_⟩
  exact hφ a

/-- Actual tame inertia generators and Frobenius lifts in the given local field. -/
theorem exists_tame_pair [Finite base.residueField] [Finite target.residueField]
    (p : ℕ) (hG : IsPGroup p Gal(L/K)) (hpq : p.Coprime (Nat.card base.residueField))
    (hq : (Nat.card base.residueField : target.valuationSubring)∈target.maximalIdeal)
    (pi : target.valuationSubring) (hpi : target.valuation.IsUniformizer (pi : L)) :
    ∃ τ φ : Gal(L/K),
      Subgroup.zpowers τ = lowerRamificationGroup (base:=base.toDVF) (target:=target.toDVF)
        (completeUnique base target) ((0 : ℕ) : ℝ) ∧
      φ*τ*φ⁻¹=τ^(Nat.card base.residueField) := by
  letI : Algebra.IsSeparable base.residueField target.residueField := inferInstance
  letI := inertia_isCyclic (completeUnique base target) p (Nat.card base.residueField)
    hG hpq hq pi hpi
  obtain ⟨τ,hτ⟩ := IsCyclic.exists_generator
    (α := lowerRamificationGroup (base:=base.toDVF) (target:=target.toDVF)
      (completeUnique base target) ((0 : ℕ) : ℝ))
  obtain ⟨φ,hφ⟩ := exists_frobenius_unit base target
  refine ⟨τ,φ,?_,frobenius_conj_eq_pow (completeUnique base target) p
    (Nat.card base.residueField) hG hpq hq pi hpi φ hφ τ⟩
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr τ.property
  · intro σ hσ
    obtain ⟨n,hn⟩ := hτ ⟨σ,hσ⟩
    exact ⟨n, congrArg Subtype.val hn⟩

end UnitDistance.OddTame
