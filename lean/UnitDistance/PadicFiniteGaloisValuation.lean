module

public import UnitDistance.OddTameResidueGeneration
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree

@[expose] public section
set_option backward.privateInPublic true


/-! Actual complete discrete valuations and residue fields of finite Galois Qp extensions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace UnitDistance.PadicFiniteGalois
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField.ResidueField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

variable (p : ℕ) [Fact p.Prime] (L : Type u) [Field L] [Algebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]

abbrev base := padicCompleteDVF p

private theorem exists_target : ∃ target : CompleteDVF.{u,0} L,
    (base p).valuation.HasExtension target.valuation := by
  obtain ⟨target,hExt,_,_⟩ := exists_integralClosure_standard_fundamental_identity
    (K:=ℚ_[p]) (L:=L) (base p)
  exact ⟨target,hExt⟩

def target : CompleteDVF.{u,0} L := (exists_target p L).choose

instance target_hasExtension : (base p).valuation.HasExtension (target p L).valuation :=
  (exists_target p L).choose_spec

instance base_residue_finite : Finite (base p).residueField :=
  padicCompleteDVF_residueField_finite p

def baseResidueEquiv : (base p).residueField ≃+* ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv (padicIntEquivValuationSubring p)).symm.trans
    (padicIntResidueFieldEquivZMod p)

instance target_residue_finite : Finite (target p L).residueField := by
  letI : Module.Finite (base p).valuationSubring (target p L).valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable (base p) (target p L)
  letI : FiniteDimensional (base p).residueField (target p L).residueField :=
    residueField_finiteDimensional_of_moduleFinite (base p) (target p L)
  exact Module.finite_of_finite (base p).residueField

def residueEmbedding : ZMod p →+* (target p L).residueField :=
  (algebraMap (base p).residueField (target p L).residueField).comp (baseResidueEquiv p).symm.toRingHom

theorem residue_card : Nat.card (base p).residueField=p :=
  padicCompleteDVF_residueField_card p

theorem prime_mem_maximalIdeal : (p : (target p L).valuationSubring)∈(target p L).maximalIdeal := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
  have h := map_natCast (residueEmbedding p L) p
  simpa using h.symm

theorem two_residue_ne_zero (hp : p≠2) : (2 : (target p L).residueField)≠0 := by
  have h2 : (2 : ZMod p)≠0 := by
    change ¬((2 : ℕ) : ZMod p)=0
    rw [ZMod.natCast_eq_zero_iff]
    intro h
    exact hp ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left (Fact.out : p.Prime).ne_one)
  intro h
  apply h2
  apply (residueEmbedding p L).injective
  rw [map_ofNat, map_zero]
  exact h

theorem integer_isUnit (d : ℤ) (hd : ¬(p : ℤ)∣d) :
    IsUnit (d : (target p L).valuationSubring) := by
  have hZ : IsUnit (d : ℤ_[p]) := by
    apply PadicInt.isUnit_iff.mpr
    apply PadicInt.norm_intCast_eq_one_iff.mpr
    rw [Int.isCoprime_iff_gcd_eq_one]
    change Nat.gcd d.natAbs p=1
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (fun h ↦ hd (Int.natCast_dvd.mpr h))).symm
  have hB := hZ.map (padicIntEquivValuationSubring p).toRingHom
  have hT := hB.map (algebraMap (base p).valuationSubring (target p L).valuationSubring)
  simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_intCast] using hT

/-- Every actual square root of an integer is integral in the chosen valuation ring. -/
theorem radical_integral (a : L) (d : ℤ) (ha : a^2=d) :
    a∈(target p L).valuation.valuationSubring := by
  change (target p L).valuation a≤1
  apply (pow_le_one_iff_of_nonneg (zero_le) (by decide : (2:ℕ)≠0)).mp
  rw [← map_pow, ha]
  exact (d : (target p L).valuationSubring).property

theorem radical_isUnit (a : (target p L).valuationSubring) (d : ℤ)
    (ha : a^2=d) (hd : ¬(p : ℤ)∣d) : IsUnit a := by
  have h := integer_isUnit p L d hd
  rw [← ha] at h
  exact (isUnit_pow_iff (by decide : (2:ℕ)≠0)).mp h

end UnitDistance.PadicFiniteGalois
