module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.HilbertRamification.UniformizerGradedHom
public import UnitDistance.PrincipalUnitGradedExponent
public import Mathlib.RingTheory.Filtration

@[expose] public section
set_option backward.privateInPublic true


/-! The actual wild ramification group vanishes in prime-to-residue-characteristic
Galois extensions, using actual ideal-power layers and the uniformizer injection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w x
namespace UnitDistance.OddTame
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField.ResidueField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
  {base : ValuationTheory.DiscreteValuationField.DVF.{u,v} K}
  {target : ValuationTheory.DiscreteValuationField.DVF.{w,x} L}

theorem principalUnitGraded_pow (q n : ℕ) (hn : 1≤n)
    (hq : (q : target.valuationSubring)∈target.maximalIdeal)
    (a : dvfPrincipalUnitGradedPiece target n) : a^q=1 := by
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective
    ((dvfHigherPrincipalUnitGroup target (n+1)).subgroupOf
      (dvfHigherPrincipalUnitGroup target n)) a
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff (b^q)).mpr
  change (((b : target.valuationSubringˣ) : target.valuationSubring)^q-1)∈target.maximalIdeal^(n+1)
  exact principal_unit_pow_mem target.maximalIdeal q n hn hq _ b.property

variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] [IsGalois K L]
  (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u,v,w,x,x}
    base target)
  [Algebra.IsSeparable base.residueField target.residueField]

/-- Every positive lower-ramification layer is trivial when the Galois
group is a p-group and the residue characteristic is coprime to p. -/
theorem lower_step_eq (p q : ℕ) (hG : IsPGroup p Gal(L/K)) (hpq : p.Coprime q)
    (hq : (q : target.valuationSubring)∈target.maximalIdeal)
    (pi : target.valuationSubring) (hpi : target.valuation.IsUniformizer (pi : L))
    (n : ℕ) (hn : 1≤n) :
    lowerRamificationGroup (base:=base) (target:=target) huniq (n : ℝ) =
      lowerRamificationGroup (base:=base) (target:=target) huniq ((n+1 : ℕ) : ℝ) := by
  apply le_antisymm
  · intro σ hσ
    let H := lowerRamificationGroup (base:=base) (target:=target) huniq (n : ℝ)
    let N := (lowerRamificationGroup (base:=base) (target:=target) huniq ((n+1 : ℕ) : ℝ)).subgroupOf H
    let a : H := ⟨σ,hσ⟩
    let f := uniformizerGradedHom (base:=base) (target:=target) huniq pi hpi n
    have hzero : f (QuotientGroup.mk' N a)=1 :=
      hom_eq_one_of_coprime_exponent ((hG.to_subgroup H).to_quotient N) hpq f
        (principalUnitGraded_pow q n hn hq) _
    have hquot : QuotientGroup.mk' N a=1 :=
      (uniformizerGradedHom_injective_of_residue_isSeparable
        (base:=base) (target:=target) huniq pi hpi n) (hzero.trans f.map_one.symm)
    exact (QuotientGroup.eq_one_iff a).mp hquot
  · exact lowerRamificationGroup_antitone huniq (by norm_num)

/-- The actual wild ramification subgroup is trivial. No tame-inertia or
ramification-order premise is assumed. -/
theorem wild_eq_bot (p q : ℕ) (hG : IsPGroup p Gal(L/K)) (hpq : p.Coprime q)
    (hq : (q : target.valuationSubring)∈target.maximalIdeal)
    (pi : target.valuationSubring) (hpi : target.valuation.IsUniformizer (pi : L)) :
    lowerRamificationGroup (base:=base) (target:=target) huniq 1=⊥ := by
  letI : IsNoetherianRing target.valuationSubring := target.valuationSubring_isNoetherianRing
  letI : IsFractionRing target.valuationSubring L := target.valuationSubring_isFractionRing
  apply le_antisymm
  · intro σ hσ
    apply Subgroup.mem_bot.mpr
    have hlevels (n : ℕ) : σ∈lowerRamificationGroup (base:=base) (target:=target)
        huniq ((n+1 : ℕ) : ℝ) := by
      induction n with
      | zero => simpa using hσ
      | succ n ih =>
        rw [← lower_step_eq huniq p q hG hpq hq pi hpi (n+1) (by omega)]
        exact ih
    have hfixed (a : target.valuationSubring) : σ (a : L)=(a : L) := by
      have hinter : valuationSubringAutOfUniqueExtension (base:=base) (target:=target)
          huniq σ a-a∈⨅ n : ℕ, target.maximalIdeal^n := by
        apply Ideal.mem_iInf.mpr
        intro n
        have h := (mem_lowerRamificationGroup_nat_iff huniq (n+1) σ).mp (hlevels n) a
        exact Ideal.pow_le_pow_right (by omega : n≤n+1+1) h
      rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top,
        Ideal.mem_bot] at hinter
      exact congrArg (fun b : target.valuationSubring ↦ (b : L)) (sub_eq_zero.mp hinter)
    apply AlgEquiv.ext
    intro z
    obtain ⟨a,b,_,hz⟩ := IsFractionRing.div_surjective target.valuationSubring z
    change (a : L)/(b : L)=z at hz
    change σ z=z
    rw [← hz,map_div₀,hfixed a,hfixed b]
  · exact bot_le

end UnitDistance.OddTame
