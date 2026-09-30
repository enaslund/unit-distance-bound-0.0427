module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.ProTwoFrattini
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProP.BurnsideBasis
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProP.ElementaryAbelianRank
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProP.GeneratorRank
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.FieldTheory.Finiteness

@[expose] public section
set_option backward.privateInPublic true


/-! Actual elementary abelian quotients and generator counts for pro-two groups.

The generator-rank argument also appears in Yamaguchi's
`SawinTotallyRealTowers/RealProTwoGeneratorRank.lean` (Apache-2.0, pinned in
third-party/yamaguchi). Here finite generation is proved first by lifting the
whole finite quotient, and the public rank theorem then proves minimality.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ProTwoElementaryQuotient
open ClassFieldTower.ProP ClassFieldTower.Sawin
open ProCGroups ProCGroups.ProC ProCGroups.Generation ProCGroups.FiniteGeneration

variable {G Q : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup Q] [TopologicalSpace Q] [T2Space Q] [IsTopologicalGroup Q]

/-- The actual closed square-and-commutator subgroup dies in any continuous
abelian quotient of exponent two. -/
theorem closedPowerCommutator_le_ker (q : G →ₜ* Q) (hpow : ∀ a : Q, a ^ 2 = 1) :
    closedPowerCommutator 2 G ≤ q.toMonoidHom.ker := by
  apply Subgroup.topologicalClosure_minimal
  · apply sup_le
    · rw [powerSubgroup, Subgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      change q (g ^ 2) = 1
      rw [map_pow, hpow]
    · exact Abelianization.commutator_subset_ker q.toMonoidHom
  · exact ProCGroups.ContinuousMonoidHom.isClosed_ker q

/-- If every quadratic quotient factors through an actual elementary
abelian quotient, its kernel is exactly the actual Frattini subgroup. -/
theorem closedPowerCommutator_eq_ker
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasPGroupOpenNormalBasis 2 G) (q : G →ₜ* Q)
    (hpow : ∀ a : Q, a ^ 2 = 1)
    (hquadratic : ∀ U : OpenNormalSubgroup G, (U : Subgroup G).index = 2 →
      q.toMonoidHom.ker ≤ (U : Subgroup G)) :
    closedPowerCommutator 2 G = q.toMonoidHom.ker := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm (closedPowerCommutator_le_ker q hpow)
  rw [← profiniteFrattini_eq_closedPowerCommutator hG,
    profiniteFrattini_eq_iInf_openNormal_index_two G hG]
  exact le_iInf fun U ↦ le_iInf fun hU ↦ hquadratic U hU

open scoped IsMulCommutative

/-- A proved finite cardinality of the actual Frattini quotient proves
finite generation and its exact topological generator rank. -/
theorem generatorRank_of_powerCommutator_card
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasPGroupOpenNormalBasis 2 G) (d : ℕ)
    (hcard : Nat.card (powerCommutatorQuotient 2 G) = 2 ^ d) :
    TopologicallyGeneratedByAtMost d G ∧ topologicalGeneratorRank G = d := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (closedPowerCommutator 2 G).Normal := closedPowerCommutator_normal 2 G
  letI : IsClosed (closedPowerCommutator 2 G : Set G) :=
    isClosed_closedPowerCommutator 2 G
  let V := powerCommutatorQuotient 2 G
  letI : IsMulCommutative V := powerCommutatorQuotient_isMulCommutative 2 G
  letI : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (fun x ↦ by
    change (Additive.toMul x) ^ 2 = 1
    exact powerCommutatorQuotient_pow_eq_one 2 G (Additive.toMul x))
  letI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI : Fintype V := Fintype.ofFinite V
  letI : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hcardAdd : Nat.card (Additive V) = 2 ^ d :=
    (Nat.card_congr (Additive.toMul : Additive V ≃ V)).trans hcard
  have hdim : Module.finrank (ZMod 2) (Additive V) = d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hcardAdd
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hcardAdd
  let liftV : V → G := Function.surjInv (powerCommutatorQuotientMk_surjective 2 G)
  let s : Finset G := Finset.univ.image liftV
  have himage : powerCommutatorQuotientMk 2 G '' (s : Set G) = Set.univ := by
    ext v
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨liftV v, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩,
        Function.surjInv_eq (powerCommutatorQuotientMk_surjective 2 G) v⟩
  have hgen : TopologicallyGenerates (s : Set G) := by
    apply (topologicallyGenerates_iff_powerCommutatorQuotient_image hG).mpr
    rw [himage]
    simp [TopologicallyGenerates]
  have hfg : TopologicallyFinitelyGenerated G := ⟨s, hgen⟩
  have hrank : topologicalGeneratorRank G = d :=
    (topologicalGeneratorRank_eq_powerCommutatorQuotient_finrank hG hfg).trans hdim
  refine ⟨?_, hrank⟩
  apply (topologicallyGeneratedByAtMost_iff_powerCommutatorQuotientRank_le hG hfg).mpr
  change Module.finrank (ZMod 2) (Additive V) ≤ d
  exact hdim.le

/-- An actual elementary quotient exhausting quadratic quotients supplies
both finite generation and the exact rank, without either as an input. -/
theorem generatorRank_of_quadratic_quotient
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasPGroupOpenNormalBasis 2 G) (q : G →ₜ* Q)
    (hq : Function.Surjective q) (hpow : ∀ a : Q, a ^ 2 = 1)
    (hquadratic : ∀ U : OpenNormalSubgroup G, (U : Subgroup G).index = 2 →
      q.toMonoidHom.ker ≤ (U : Subgroup G))
    (d : ℕ) (hcard : Nat.card Q = 2 ^ d) :
    TopologicallyGeneratedByAtMost d G ∧ topologicalGeneratorRank G = d := by
  letI : (closedPowerCommutator 2 G).Normal := closedPowerCommutator_normal 2 G
  have hk := closedPowerCommutator_eq_ker hG q hpow hquadratic
  let e : powerCommutatorQuotient 2 G ≃* Q :=
    QuotientGroup.liftEquiv _ hq hk
  exact generatorRank_of_powerCommutator_card hG d ((Nat.card_congr e.toEquiv).trans hcard)

end UnitDistance.ProTwoElementaryQuotient
