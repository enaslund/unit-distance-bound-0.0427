module

public import UnitDistance.OddTameRamification

@[expose] public section
set_option backward.privateInPublic true


/-! The uniformizer character of actual tame inertia, valued in residue-field units. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w x
namespace UnitDistance.OddTame
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField.ResidueField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
  {base : ValuationTheory.DiscreteValuationField.DVF.{u,v} K}
  {target : ValuationTheory.DiscreteValuationField.DVF.{w,x} L}
  [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] [IsGalois K L]
  (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u,v,w,x,x}
    base target)

abbrev residueUnit : target.valuationSubringˣ →* target.residueFieldˣ :=
  Units.map target.residueMap.toMonoidHom

theorem residueUnit_aut_of_inertia
    (σ : lowerRamificationGroup (base:=base) (target:=target) huniq ((0 : ℕ) : ℝ))
    (a : target.valuationSubringˣ) :
    residueUnit (dvfValuationSubringUnitAut huniq (σ : Gal(L/K)) a)=residueUnit a := by
  apply Units.ext
  change target.residueMap (valuationSubringAutOfUniqueExtension huniq (σ : Gal(L/K)) a) =
    target.residueMap a
  apply sub_eq_zero.mp
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff]
  simpa using (mem_lowerRamificationGroup_nat_iff huniq 0 σ).mp σ.property a

theorem uniformizerQuotient_one
    (pi : target.valuationSubring) (hpi : target.valuation.IsUniformizer (pi : L)) :
    dvfUniformizerQuotientUnit huniq pi hpi 1=1 := by
  apply Units.ext
  have hpi0 : pi ≠ 0 := fun h ↦ hpi.ne_zero (congrArg Subtype.val h)
  apply mul_right_cancel₀ hpi0
  rw [← dvfUniformizerQuotientUnit_mul_uniformizer]
  simp

/-- The actual residue of `σ(π)/π` on inertia. -/
def inertiaCharacter
    (pi : target.valuationSubring) (hpi : target.valuation.IsUniformizer (pi : L)) :
    lowerRamificationGroup (base:=base) (target:=target) huniq ((0 : ℕ) : ℝ) →* target.residueFieldˣ where
  toFun σ := residueUnit (dvfUniformizerQuotientUnit huniq pi hpi (σ : Gal(L/K)))
  map_one' := by rw [Subgroup.coe_one, uniformizerQuotient_one, map_one]
  map_mul' σ τ := by
    rw [Subgroup.coe_mul, dvfUniformizerQuotientUnit_mul_eq, map_mul,
      residueUnit_aut_of_inertia huniq σ, mul_comm]

theorem residueUnit_eq_one_iff (a : target.valuationSubringˣ) :
    residueUnit a=1 ↔ a∈dvfHigherPrincipalUnitGroup target 1 := by
  rw [Units.ext_iff, mem_dvfHigherPrincipalUnitGroup_iff]
  change target.residueMap (a : target.valuationSubring)=1 ↔ _
  rw [← sub_eq_zero, ← map_one target.residueMap, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, pow_one]

variable [Algebra.IsSeparable base.residueField target.residueField]

theorem inertiaCharacter_injective_of_wild_eq_bot
    (pi : target.valuationSubring) (hpi : target.valuation.IsUniformizer (pi : L))
    (hwild : lowerRamificationGroup (base:=base) (target:=target) huniq 1=⊥) :
    Function.Injective (inertiaCharacter huniq pi hpi) := by
  apply (injective_iff_map_eq_one _).mpr
  intro σ hσ
  have hunit : dvfUniformizerQuotientUnit huniq pi hpi (σ : Gal(L/K)) ∈
      dvfHigherPrincipalUnitGroup target 1 := (residueUnit_eq_one_iff _).mp hσ
  have hgraded := (uniformizerGradedHom_mk_eq_one_iff huniq pi hpi 0 σ).mpr hunit
  have hquot := (uniformizerGradedHom_injective_of_residue_isSeparable huniq pi hpi 0)
    (hgraded.trans (map_one _).symm)
  have hw : (σ : Gal(L/K))∈lowerRamificationGroup (base:=base) (target:=target) huniq 1 :=
    by simpa only [Subgroup.mem_subgroupOf, Nat.reduceAdd, Nat.cast_one] using
      (QuotientGroup.eq_one_iff σ).mp hquot
  apply Subtype.ext
  exact Subgroup.mem_bot.mp (hwild ▸ hw)

theorem inertiaCharacter_injective
    (p q : ℕ) (hG : IsPGroup p Gal(L/K)) (hpq : p.Coprime q)
    (hq : (q : target.valuationSubring)∈target.maximalIdeal)
    (pi : target.valuationSubring) (hpi : target.valuation.IsUniformizer (pi : L)) :
    Function.Injective (inertiaCharacter huniq pi hpi) :=
  inertiaCharacter_injective_of_wild_eq_bot huniq pi hpi
    (wild_eq_bot huniq p q hG hpq hq pi hpi)

/-- Tame inertia is cyclic, as an actual subgroup of the finite residue-field units. -/
theorem inertia_isCyclic [Finite target.residueField]
    (p q : ℕ) (hG : IsPGroup p Gal(L/K)) (hpq : p.Coprime q)
    (hq : (q : target.valuationSubring)∈target.maximalIdeal)
    (pi : target.valuationSubring) (hpi : target.valuation.IsUniformizer (pi : L)) :
    IsCyclic (lowerRamificationGroup (base:=base) (target:=target) huniq ((0 : ℕ) : ℝ)) :=
  isCyclic_of_injective (inertiaCharacter huniq pi hpi)
    (inertiaCharacter_injective huniq p q hG hpq hq pi hpi)

theorem valuationUnitAut_mul (σ τ : Gal(L/K)) (a : target.valuationSubringˣ) :
    dvfValuationSubringUnitAut huniq (σ*τ) a =
      dvfValuationSubringUnitAut huniq σ (dvfValuationSubringUnitAut huniq τ a) := by
  apply Units.ext
  exact valuationSubringAutOfUniqueExtension_mul_apply huniq σ τ a

/-- The character transforms by the actual Frobenius residue action. -/
theorem inertiaCharacter_conj_frobenius
    (pi : target.valuationSubring) (hpi : target.valuation.IsUniformizer (pi : L))
    (q : ℕ) (φ : Gal(L/K))
    (hφ : ∀ a : target.valuationSubringˣ,
      residueUnit (dvfValuationSubringUnitAut huniq φ a)=(residueUnit a)^q)
    (τ : lowerRamificationGroup (base:=base) (target:=target) huniq ((0 : ℕ) : ℝ)) :
    inertiaCharacter huniq pi hpi
      ⟨φ*(τ : Gal(L/K))*φ⁻¹, Subgroup.Normal.conj_mem inferInstance _ τ.property φ⟩ =
      (inertiaCharacter huniq pi hpi τ)^q := by
  let u := dvfUniformizerQuotientUnit huniq pi hpi
  have hinv : (residueUnit (u φ⁻¹))^q * residueUnit (u φ)=1 := by
    rw [← hφ, ← map_mul, ← dvfUniformizerQuotientUnit_mul_eq]
    simp only [mul_inv_cancel, uniformizerQuotient_one, map_one]
  change residueUnit (u (φ*(τ : Gal(L/K))*φ⁻¹))=(residueUnit (u τ))^q
  dsimp only [u]
  rw [dvfUniformizerQuotientUnit_mul_eq, map_mul,
    valuationUnitAut_mul, hφ, residueUnit_aut_of_inertia huniq τ,
    dvfUniformizerQuotientUnit_mul_eq, map_mul, hφ]
  calc
    _ = (residueUnit (u (τ : Gal(L/K))))^q *
        ((residueUnit (u φ⁻¹))^q * residueUnit (u φ)) := by ac_rfl
    _ = _ := by rw [hinv, mul_one]

/-- The literal tame word vanishes in the actual finite Galois group. -/
theorem frobenius_conj_eq_pow
    (p q : ℕ) (hG : IsPGroup p Gal(L/K)) (hpq : p.Coprime q)
    (hq : (q : target.valuationSubring)∈target.maximalIdeal)
    (pi : target.valuationSubring) (hpi : target.valuation.IsUniformizer (pi : L))
    (φ : Gal(L/K))
    (hφ : ∀ a : target.valuationSubringˣ,
      residueUnit (dvfValuationSubringUnitAut huniq φ a)=(residueUnit a)^q)
    (τ : lowerRamificationGroup (base:=base) (target:=target) huniq ((0 : ℕ) : ℝ)) :
    φ*(τ : Gal(L/K))*φ⁻¹=(τ : Gal(L/K))^q := by
  have h := inertiaCharacter_conj_frobenius huniq pi hpi q φ hφ τ
  rw [← map_pow] at h
  exact congrArg Subtype.val (inertiaCharacter_injective huniq p q hG hpq hq pi hpi h)

end UnitDistance.OddTame
