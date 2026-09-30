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

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.NegativeThreeCharacter
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.InfiniteArtinCompatibility
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.GlobalReciprocityCharacter
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.AbsoluteCharacterRadicalReciprocity
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportGlobalReciprocity
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdeleIntegralCharacterRadical
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Instances.ZMod

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# The local value at three of the negative-three character

Global reciprocity applied to the principal idele of negative one identifies
its local value at three with its nontrivial real sign. All other finite
components disappear by the proved unramifiedness of the actual quadratic
character. No Hilbert-symbol or norm-pairing comparison is assumed.
-/

open NumberField IsDedekindDomain
open scoped NumberField Classical

noncomputable section

namespace ClassFieldTower.Sawin
open ClassFieldTower.Martinet.Shafarevich

/-- The character of the actual field ℚ(√−3), evaluated through global
reciprocity on the three-adic unit −1, is nontrivial. -/
theorem negativeThreeCharacter_three_neg_one_ne_one :
    globalReciprocityIdeleCharacter ℚ 2 negativeThreeCharacter
      (IdeleGroup.finitePlaceIdele
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
          (⟨3, Nat.prime_three⟩ : Nat.Primes)) (-1)) ≠ 1 := by
  let v₃ : HeightOneSpectrum (𝓞 ℚ) :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes)
  let ψ := globalReciprocityIdeleCharacter ℚ 2 negativeThreeCharacter
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := {v₃}
  let r : IdeleGroup ℚ →ₜ* Multiplicative (ZMod 2) :=
    finiteSupportIdeleRestrictionCharacter ℚ (2 : ℕ+) S ψ
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) :=
    discreteTopology_bot _
  let δ : IdeleGroup ℚ →ₜ* Multiplicative (ZMod 2) :=
    { toFun := fun x => ψ x / r x
      map_one' := by
        simp only [map_one]
        apply Multiplicative.toAdd.injective
        simp only [toAdd_div, toAdd_one, sub_self]
      map_mul' x y := by
        simp only [map_mul]
        exact mul_div_mul_comm _ _ _ _
      continuous_toFun := ψ.continuous.div' r.continuous }
  have div_one_target (z : Multiplicative (ZMod 2)) : z / 1 = z := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_div, toAdd_one]
    exact sub_zero _
  have hfinite : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (a : (v.adicCompletion ℚ)ˣ),
      a ∈ (v.adicCompletionIntegers ℚ).units →
        δ (IdeleGroup.finitePlaceIdele v a) = 1 := by
    intro v a ha
    change ψ (IdeleGroup.finitePlaceIdele v a) /
      r (IdeleGroup.finitePlaceIdele v a) = 1
    rw [show r (IdeleGroup.finitePlaceIdele v a) =
      if v ∈ S then ψ (IdeleGroup.finitePlaceIdele v a) else 1 from
        finiteSupportIdeleRestrictionCharacter_finitePlace ℚ (2 : ℕ+) S ψ v a]
    by_cases hv : v ∈ S
    · rw [if_pos hv, div_self']
    · rw [if_neg hv, div_one_target]
      apply globalReciprocityIdeleCharacter_integral_eq_one_of_inertia
        ℚ (2 : ℕ+) negativeThreeCharacter v _ a ha
      intro σ
      exact negativeThreeCharacter_inertia v
        (fun h => hv (Finset.mem_singleton.mpr h)) σ
  let P : IdeleGroup ℚ := IdeleGroup.principalIdele ℚ (-1)
  have hIntegral : P ∈ IdeleGroup.integralAtFinitePlaces (K := ℚ) := by
    have h := IdeleGroup.principalRingUnit_mem_integralAtFinitePlaces
      (K := ℚ) (-1 : (𝓞 ℚ)ˣ)
    have he : InfiniteIdeleGroup.ringUnitToFieldUnit (K := ℚ)
        (-1 : (𝓞 ℚ)ˣ) = (-1 : ℚˣ) := by
      apply Units.ext
      change algebraMap (𝓞 ℚ) ℚ (-1) = -1
      rw [map_neg, map_one]
    rw [he] at h
    exact h
  let u : ∀ v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ).units :=
    fun v => ⟨P.2 v, hIntegral v⟩
  have hFiniteP : δ (integralFiniteIdeleContinuousHom ℚ u) = 1 :=
    ideleCharacter_integralFinite_eq_one ℚ (2 : ℕ+) δ hfinite u
  have hSplit : P = IdeleGroup.infinitePlaceIdele Rat.infinitePlace (-1) *
      integralFiniteIdeleContinuousHom ℚ u := by
    apply Prod.ext
    · apply ContinuousMulEquiv.piUnits.injective
      funext v
      rw [Subsingleton.elim v Rat.infinitePlace]
      change IdeleGroup.infiniteComponent Rat.infinitePlace P =
        IdeleGroup.infiniteComponent Rat.infinitePlace
          (IdeleGroup.infinitePlaceIdele Rat.infinitePlace (-1)) * 1
      rw [IdeleGroup.infinitePlaceIdele_infiniteComponent_same, mul_one]
      apply Units.ext
      change ((IdeleGroup.infiniteComponent Rat.infinitePlace
        (IdeleGroup.principalIdele ℚ (-1 : ℚˣ))) : Rat.infinitePlace.Completion) = -1
      rw [IdeleGroup.infiniteComponent_principalIdele]
      apply InfinitePlace.Completion.ext
      change ((WithAbs.toAbs Rat.infinitePlace.1
        (-1 : ℚ)) : Rat.infinitePlace.1.Completion) = -1
      rw [WithAbs.toAbs_neg, WithAbs.toAbs_one,
        UniformSpace.Completion.coe_neg, UniformSpace.Completion.coe_one]
    · exact (one_mul P.2).symm
  have hrInfinite : r (IdeleGroup.infinitePlaceIdele Rat.infinitePlace (-1)) = 1 := by
    change (∏ v : ↥S, ψ (IdeleGroup.finitePlaceIdele v.1
      (IdeleGroup.finiteComponent v.1
        (IdeleGroup.infinitePlaceIdele Rat.infinitePlace (-1))))) = 1
    apply Finset.prod_eq_one
    intro v hv
    rw [IdeleGroup.infinitePlaceIdele_finiteComponent, map_one, map_one]
  have hrP : r P = ψ (IdeleGroup.finitePlaceIdele v₃ (-1)) := by
    change (∏ v : ↥({v₃} : Finset (HeightOneSpectrum (𝓞 ℚ))),
      ψ (IdeleGroup.finitePlaceIdele v.1 (IdeleGroup.finiteComponent v.1 P))) = _
    rw [Fintype.prod_subsingleton _ (⟨v₃, Finset.mem_singleton_self v₃⟩ :
      ↥({v₃} : Finset (HeightOneSpectrum (𝓞 ℚ))))]
    have he : IdeleGroup.finiteComponent v₃ P = (-1 : (v₃.adicCompletion ℚ)ˣ) := by
      apply Units.ext
      rw [IdeleGroup.finiteComponent_principalIdele]
      let f : ℚ →+* v₃.adicCompletion ℚ :=
        (HeightOneSpectrum.adicCompletion.equiv ℚ v₃).symm.toRingHom.comp
          (UniformSpace.Completion.coeRingHom.comp
            (WithVal.equiv (v₃.valuation ℚ)).symm.toRingHom)
      change f (-1) = -1
      rw [map_neg, map_one]
    rw [he]
  intro hLocal
  have hP : δ P = 1 := by
    change ψ P / r P = 1
    rw [hrP, hLocal]
    exact div_one_target _ |>.trans
      (globalReciprocityIdeleCharacter_principal ℚ 2 negativeThreeCharacter (-1))
  rw [hSplit, map_mul, hFiniteP, mul_one] at hP
  change ψ (IdeleGroup.infinitePlaceIdele Rat.infinitePlace (-1)) /
    r (IdeleGroup.infinitePlaceIdele Rat.infinitePlace (-1)) = 1 at hP
  rw [hrInfinite, div_one_target] at hP
  exact negativeThreeCharacter_infinite Rat.infinitePlace
    ((globalReciprocityIdeleCharacter_infinite_neg_one
      ℚ 2 negativeThreeCharacter Rat.infinitePlace).symm.trans hP)

end ClassFieldTower.Sawin
