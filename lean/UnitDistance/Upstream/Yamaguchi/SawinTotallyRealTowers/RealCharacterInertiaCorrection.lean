/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.AbsoluteCharacterRealValue
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.AbsoluteRealKernelField
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.EmptySupportKummerCokernel
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceH1AdicRestriction
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportInertiaCorrection
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportLocalReciprocityIdeleCharacter
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProP.ContinuousH1
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.PNat.Basic
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Instances.ZMod

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Real values and prescribed finite inertia over the rationals

The finite-support radical kernel constructs an absolute quadratic character
with the prescribed inertia values. Multiplication by the character of
negative three then gives any specified real value while preserving inertia
outside an allowed ramification set containing three.
-/

open NumberField IsDedekindDomain
open scoped NumberField

namespace ClassFieldTower.Sawin

open ClassFieldTower.Martinet.Shafarevich ClassFieldTower.ProP

/-- Realize a finite local family in the radical kernel, with a prescribed
real value and unchanged inertia outside a set containing three. -/
theorem exists_absoluteCharacter_with_real_value_of_radical_annihilator
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hThree : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ T)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (chi : ∀ v : ↥S, finitePlaceAbsoluteDecompositionGroup ℚ v.1 →ₜ*
      Multiplicative (ZMod 2))
    (hchi : absolutePowerClassDualRestriction ℚ 2
      (finiteSupportLocalReciprocityPowerClassFunctional ℚ 2 S
        (fun v => finitePlaceDecompositionH1ToAdic ℚ 2 v.1
          (h1OfCharacter (chi v)))) = 0)
    (ε : Multiplicative (ZMod 2)) :
    ∃ gamma : Field.absoluteGaloisGroup ℚ →ₜ* Multiplicative (ZMod 2),
      (∀ v : InfinitePlace ℚ,
        gamma (absoluteInfinitePlaceArtinNegOne ℚ v) = ε) ∧
      (∀ (v : ↥S), v.1 ∉ T →
        ∀ sigma : finitePlaceAbsoluteInertiaSubgroup ℚ v.1,
          chi v sigma.1 =
            gamma (finitePlaceAbsoluteDecompositionInclusion ℚ v.1 sigma.1)) ∧
      (∀ (v : HeightOneSpectrum (𝓞 ℚ)), v ∉ S → v ∉ T →
        ∀ sigma : finitePlaceAbsoluteInertiaSubgroup ℚ v,
          gamma (finitePlaceAbsoluteDecompositionInclusion ℚ v sigma.1) = 1) := by
  obtain ⟨gamma, hInside, hOutside⟩ :=
    exists_absoluteCharacter_of_finiteSupport_radical_annihilator
      ℚ (2 : ℕ+) S chi hchi
  refine ⟨absoluteCharacterWithRealValue gamma ε,
    absoluteCharacterWithRealValue_infinite gamma ε, ?_, ?_⟩
  · intro v hv sigma
    have hNe : v.1 ≠ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
        (⟨3, Nat.prime_three⟩ : Nat.Primes) := by
      intro h
      exact hv (h.symm ▸ hThree)
    have hValue : absoluteCharacterWithRealValue gamma ε
        (finitePlaceAbsoluteDecompositionInclusion ℚ v.1 sigma.1) =
        gamma (finitePlaceAbsoluteDecompositionInclusion ℚ v.1 sigma.1) :=
      absoluteCharacterWithRealValue_inertia gamma ε v.1 hNe sigma
    exact (hInside v sigma).trans hValue.symm
  · intro v hv hT sigma
    have hNe : v ≠ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
        (⟨3, Nat.prime_three⟩ : Nat.Primes) := by
      intro h
      exact hT (h.symm ▸ hThree)
    have hValue : absoluteCharacterWithRealValue gamma ε
        (finitePlaceAbsoluteDecompositionInclusion ℚ v sigma.1) =
        gamma (finitePlaceAbsoluteDecompositionInclusion ℚ v sigma.1) :=
      absoluteCharacterWithRealValue_inertia gamma ε v hNe sigma
    exact hValue.trans (hOutside v hv sigma)

end ClassFieldTower.Sawin
