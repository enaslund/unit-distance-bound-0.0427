/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
Adapted from RiemannHypothesis/Xi/CanonicalDivisor.lean at commit
753938937e624d1c8bbe4c208517660a672d1b8e. Generalized from the xi pullback
to an arbitrary nontrivial even entire function; special xi facts omitted.
Negation-involution proofs adapted from Xi/CanonicalProductPairedGrowth.lean
at the same commit. Exact location-fiber and full divisor identities added.
-/
module

public import UnitDistance.HadamardPairing
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section
set_option backward.privateInPublic true

noncomputable section
open Filter Metric Set Topology
namespace UnitDistance.EntireDivisor
open OverflowResidueRH
structure EntireEvenFunction where
  toFun : ℂ → ℂ
  differentiable : Differentiable ℂ toFun
  nontrivial : ∃ z, toFun z ≠ 0
  even : ∀ z, toFun (-z) = toFun z
variable (F : EntireEvenFunction)

/-- The function cannot vanish identically on a neighborhood of any point. -/
theorem not_eventuallyEq_zero (p : Complex) :
    ¬ (F.toFun =ᶠ[nhds p] 0) := by
  intro hlocal
  have h_on : AnalyticOnNhd Complex F.toFun Set.univ :=
    fun z _hz => F.differentiable.analyticAt z
  have heq : Set.EqOn F.toFun 0 Set.univ :=
    h_on.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ
      (Set.mem_univ p)
      hlocal
  obtain ⟨z, hz⟩ := F.nontrivial
  exact hz (heq (Set.mem_univ z))

/-- The analytic order of the entire function is finite at every point. -/
theorem analyticOrderAt_ne_top (z : Complex) :
    analyticOrderAt F.toFun z ≠ ⊤ := by
  intro htop
  exact
    (not_eventuallyEq_zero F) z
      (analyticOrderAt_eq_top.mp htop)

/-- Negation preserves the analytic order of the even function. -/
theorem analyticOrderAt_neg (z : Complex) :
    analyticOrderAt F.toFun (-z) =
      analyticOrderAt F.toFun z := by
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := F.toFun) (g := fun w : Complex => -w) (z₀ := z)
    (by fun_prop) (by simp)
  have hfun : F.toFun ∘ (fun w : Complex => -w) =
      F.toFun := by
    funext w
    exact F.even w
  rw [hfun] at hcomp
  exact hcomp.symm

/-- Negation also preserves the natural-valued analytic multiplicity. -/
theorem analyticOrderNatAt_neg (z : Complex) :
    analyticOrderNatAt F.toFun (-z) =
      analyticOrderNatAt F.toFun z := by
  unfold analyticOrderNatAt
  rw [(analyticOrderAt_neg F)]

/-- The multiplicity of a possible zero at the function origin. -/
noncomputable def OriginMultiplicity : Nat :=
  analyticOrderNatAt F.toFun 0

/-- The origin multiplicity is exactly the analytic order at the origin. -/
theorem analyticOrderAt_zero :
    analyticOrderAt F.toFun 0 =
      ((OriginMultiplicity F) : ENat) := by
  exact
    (Nat.cast_analyticOrderNatAt
      ((analyticOrderAt_ne_top F) 0)).symm

/-- The origin multiplicity is nonzero exactly when the function vanishes at
the origin. -/
theorem OriginMultiplicity_ne_zero_iff :
    (OriginMultiplicity F) ≠ 0 ↔
      F.toFun 0 = 0 := by
  constructor
  · intro hm
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hm
  · intro hz hm
    have horder : analyticOrderAt F.toFun 0 ≠ 0 :=
      (F.differentiable.analyticAt 0).analyticOrderAt_ne_zero.mpr hz
    apply horder
    rw [(analyticOrderAt_zero F), hm]
    simp

/-- The subtype of distinct nonzero zeros of the entire function. -/
def NonzeroZero : Type :=
  {z : Complex // F.toFun z = 0 ∧ z ≠ 0}

/-- Negation acts on the distinct nonzero function zeros. -/
def NonzeroZeroNeg
    (z : (NonzeroZero F)) :
    (NonzeroZero F) :=
  ⟨-z.1, F.even z.1 ▸ z.2.1, neg_ne_zero.mpr z.2.2⟩

@[simp] theorem NonzeroZeroNeg_val
    (z : (NonzeroZero F)) :
    ((NonzeroZeroNeg F) z).1 = -z.1 :=
  rfl

/-- Negation is an involutive equivalence of the distinct nonzero zeros. -/
def NonzeroZeroNegEquiv :
    (NonzeroZero F) ≃ (NonzeroZero F) where
  toFun := (NonzeroZeroNeg F)
  invFun := (NonzeroZeroNeg F)
  left_inv z := by
    apply Subtype.ext
    simp [NonzeroZeroNeg]
  right_inv z := by
    apply Subtype.ext
    simp [NonzeroZeroNeg]

/-- Every nonzero function zero has strictly positive natural analytic order. -/
theorem NonzeroZero_analyticOrderNatAt_pos
    (z : (NonzeroZero F)) :
    0 < analyticOrderNatAt F.toFun z.1 := by
  apply Nat.pos_of_ne_zero
  intro horderNat
  have horder : analyticOrderAt F.toFun z.1 ≠ 0 :=
    (F.differentiable.analyticAt z.1).analyticOrderAt_ne_zero.mpr z.2.1
  apply horder
  rw [← Nat.cast_analyticOrderNatAt
    ((analyticOrderAt_ne_top F) z.1), horderNat]
  simp

/-- One occurrence for each unit of analytic multiplicity at every nonzero
function zero. -/
noncomputable def ZeroOccurrence : Type :=
  Sigma fun z : (NonzeroZero F) =>
    Fin (analyticOrderNatAt F.toFun z.1)

/-- The occurrence fiber above a distinct nonzero zero is exactly a finite
type with cardinality equal to that zero's analytic order. -/
noncomputable def ZeroOccurrenceFiberEquiv
    (z : (NonzeroZero F)) :
    {i : (ZeroOccurrence F) // i.1 = z} ≃
      Fin (analyticOrderNatAt F.toFun z.1) where
  toFun i := i.2 ▸ i.1.2
  invFun k := ⟨⟨z, k⟩, rfl⟩
  left_inv i := by
    rcases i with ⟨⟨z', k⟩, hz'⟩
    change z' = z at hz'
    subst z'
    rfl
  right_inv k := rfl

/-- The number of canonical occurrences above a nonzero zero is its exact
analytic multiplicity. -/
theorem ZeroOccurrence_fiber_natCard
    (z : (NonzeroZero F)) :
    Nat.card {i : (ZeroOccurrence F) // i.1 = z} =
      analyticOrderNatAt F.toFun z.1 := by
  calc
    Nat.card {i : (ZeroOccurrence F) // i.1 = z} =
        Nat.card (Fin (analyticOrderNatAt F.toFun z.1)) :=
      Nat.card_congr ((ZeroOccurrenceFiberEquiv F) z)
    _ = analyticOrderNatAt F.toFun z.1 := Nat.card_fin _

/-- The location of a multiplicity-bearing nonzero-zero occurrence. -/
def ZeroOccurrenceLoc
    (i : (ZeroOccurrence F)) : Complex :=
  i.1.1

/-- Negation lifts from distinct zeros to the exact multiplicity-bearing
occurrence index. -/
noncomputable def ZeroOccurrenceNegEquiv :
    (ZeroOccurrence F) ≃ (ZeroOccurrence F) :=
  Equiv.sigmaCongr (NonzeroZeroNegEquiv F) fun z =>
    finCongr ((analyticOrderNatAt_neg F) z.1).symm

/-- The lifted occurrence equivalence negates its zero location. -/
@[simp] theorem ZeroOccurrenceNegEquiv_loc
    (i : (ZeroOccurrence F)) :
    (ZeroOccurrenceLoc F)
        ((ZeroOccurrenceNegEquiv F) i) =
      -(ZeroOccurrenceLoc F) i := by
  rfl

/-- Every canonical occurrence is located away from the origin. -/
theorem ZeroOccurrenceLoc_ne_zero
    (i : (ZeroOccurrence F)) :
    (ZeroOccurrenceLoc F) i ≠ 0 :=
  i.1.2.2

/-- Every canonical occurrence is located at a zero of the function. -/
theorem ZeroOccurrenceLoc_is_zero
    (i : (ZeroOccurrence F)) :
    F.toFun ((ZeroOccurrenceLoc F) i) = 0 :=
  i.1.2.1

/-- Every nonzero function zero occurs in the canonical multiplicity index. -/
theorem ZeroOccurrenceLoc_exhaustive
    {z : Complex}
    (hz : F.toFun z = 0) (hz0 : z ≠ 0) :
    ∃ i : (ZeroOccurrence F),
      (ZeroOccurrenceLoc F) i = z := by
  let rho : (NonzeroZero F) := ⟨z, hz, hz0⟩
  have hpos : 0 < analyticOrderNatAt F.toFun rho.1 :=
    (NonzeroZero_analyticOrderNatAt_pos F) rho
  exact ⟨⟨rho, ⟨0, hpos⟩⟩, rfl⟩

/-- Set-level characterization of the canonical occurrence locations. -/
theorem exists_ZeroOccurrenceLoc_iff (z : Complex) :
    (∃ i : (ZeroOccurrence F),
      (ZeroOccurrenceLoc F) i = z) ↔
      F.toFun z = 0 ∧ z ≠ 0 := by
  constructor
  · rintro ⟨i, rfl⟩
    exact
      ⟨(ZeroOccurrenceLoc_is_zero F) i,
        (ZeroOccurrenceLoc_ne_zero F) i⟩
  · rintro ⟨hz, hz0⟩
    exact (ZeroOccurrenceLoc_exhaustive F) hz hz0

/-- Zeros of the entire function are locally finite. -/
theorem zeroSet_locallyFinite (p : Complex) :
    ∃ U ∈ nhds p,
      (U ∩ {z : Complex | F.toFun z = 0}).Finite := by
  by_cases hp : F.toFun p = 0
  · have hAn : AnalyticAt Complex F.toFun p :=
      F.differentiable.analyticAt p
    rcases hAn.eventually_eq_zero_or_eventually_ne_zero with hlocal | hpunct
    · exact absurd hlocal ((not_eventuallyEq_zero F) p)
    · rw [eventually_nhdsWithin_iff] at hpunct
      refine
        ⟨{z : Complex | z ∈ ({p}ᶜ : Set Complex) → F.toFun z ≠ 0},
          hpunct, ?_⟩
      apply Set.Finite.subset (Set.finite_singleton p)
      rintro z ⟨hzU, hzzero⟩
      by_cases hzp : z = p
      · simp [hzp]
      · have hzmem : z ∈ ({p}ᶜ : Set Complex) := hzp
        exact absurd hzzero (hzU hzmem)
  · have hcont : ContinuousAt F.toFun p :=
      (F.differentiable.analyticAt p).continuousAt
    have hEventually_ne :
        ∀ᶠ z in nhds p, F.toFun z ≠ 0 :=
      hcont.eventually_ne hp
    refine ⟨{z : Complex | F.toFun z ≠ 0}, hEventually_ne, ?_⟩
    have hempty :
        {z : Complex | F.toFun z ≠ 0} ∩
            {z : Complex | F.toFun z = 0} =
          ∅ := by
      ext z
      constructor
      · rintro ⟨hz_ne, hz_zero⟩
        exact (hz_ne hz_zero).elim
      · intro hz
        exact absurd hz (Set.notMem_empty z)
    rw [hempty]
    exact Set.finite_empty

/-- Only finitely many distinct function zeros lie in any closed norm ball. -/
theorem zeroSet_finite_in_closedBall (R : Real) :
    {z : Complex |
      z ∈ Metric.closedBall (0 : Complex) R ∧ F.toFun z = 0}.Finite := by
  classical
  let Z : Set Complex :=
    {z : Complex |
      z ∈ Metric.closedBall (0 : Complex) R ∧ F.toFun z = 0}
  let K : Set Complex := Metric.closedBall (0 : Complex) R
  have hK : IsCompact K := ProperSpace.isCompact_closedBall (0 : Complex) R
  have hZK : Z ⊆ K := by
    intro z hz
    exact hz.1
  have hlocal :
      ∀ p ∈ K, ∃ U ∈ nhds p, (U ∩ Z).Finite := by
    intro p _hp
    obtain ⟨U, hU, hfin⟩ := (zeroSet_locallyFinite F) p
    refine ⟨U, hU, ?_⟩
    exact hfin.subset (by
      rintro z ⟨hzU, hz⟩
      exact ⟨hzU, hz.2⟩)
  choose! V hV_nhds hV_finite using hlocal
  obtain ⟨t, ht_sub, ht_cover⟩ := hK.elim_nhds_subcover V hV_nhds
  have hZsubset : Z ⊆ ⋃ p ∈ t, V p ∩ Z := by
    intro z hz
    have hzK : z ∈ K := hZK hz
    obtain ⟨p, hpt, hzVp⟩ := Set.mem_iUnion₂.mp (ht_cover hzK)
    exact Set.mem_iUnion₂.mpr ⟨p, hpt, hzVp, hz⟩
  have hZfinite : Z.Finite := by
    refine Set.Finite.subset ?_ hZsubset
    refine Set.Finite.biUnion t.finite_toSet ?_
    intro p hp
    exact hV_finite p (ht_sub p hp)
  simpa [Z] using hZfinite

/-- The distinct nonzero function zeros in a fixed norm ball form a finite
subtype set. -/
private theorem NonzeroZero_norm_le_finite (R : Real) :
    {z : (NonzeroZero F) | (norm (z.1) : Real) ≤ R}.Finite := by
  let Z : Set Complex :=
    {z : Complex |
      z ∈ Metric.closedBall (0 : Complex) R ∧ F.toFun z = 0}
  have hZ : Z.Finite := (zeroSet_finite_in_closedBall F) R
  apply Set.Finite.of_finite_image
    (s := {z : (NonzeroZero F) | (norm (z.1) : Real) ≤ R})
    (f := fun z : (NonzeroZero F) => z.1)
  · exact hZ.subset (by
      rintro z ⟨rho, hrho, rfl⟩
      refine ⟨?_, rho.2.1⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using hrho)
  · exact Subtype.val_injective.injOn

/-- The multiplicity-bearing function occurrence locations are norm-proper. -/
theorem ZeroOccurrenceNormProper :
    HadamardZeroNormProper (ZeroOccurrenceLoc F) := by
  refine ⟨?_⟩
  intro R
  let S : Set (ZeroOccurrence F) :=
    {i : (ZeroOccurrence F) |
      norm ((ZeroOccurrenceLoc F) i) ≤ R}
  have hbase :
      ((fun i : (ZeroOccurrence F) => i.1) '' S).Finite := by
    apply ((NonzeroZero_norm_le_finite F) R).subset
    rintro rho ⟨i, hi, rfl⟩
    exact hi
  have hfiber :
      ∀ rho ∈
        (fun i : (ZeroOccurrence F) => i.1) '' S,
        (S ∩
          (fun i : (ZeroOccurrence F) => i.1) ⁻¹' {rho}).Finite := by
    intro rho _hrho
    apply (Set.finite_range
      (fun k : Fin (analyticOrderNatAt F.toFun rho.1) =>
        Sigma.mk rho k)).subset
    intro i hi
    have hirho : i.1 = rho := hi.2
    subst rho
    exact ⟨i.2, rfl⟩
  exact Set.Finite.of_finite_fibers
    (fun i : (ZeroOccurrence F) => i.1) hbase hfiber

/-- The zero set of the entire function is countable. -/
theorem zeroSet_countable :
    {z : Complex | F.toFun z = 0}.Countable := by
  let D := MeromorphicOn.divisor F.toFun (Set.univ : Set Complex)
  have hAn : AnalyticOnNhd Complex F.toFun Set.univ :=
    fun z _hz => F.differentiable.analyticAt z
  have hfinite :
      ∀ z : (Set.univ : Set Complex),
        meromorphicOrderAt F.toFun z.1 ≠ ⊤ := by
    intro z
    rw [(hAn z.1 z.2).meromorphicOrderAt_eq]
    simpa using (analyticOrderAt_ne_top F) z.1
  have hsupport :
      {z : Complex | F.toFun z = 0} = D.support := by
    have hzero := hAn.meromorphicNFOn.zero_set_eq_divisor_support hfinite
    ext z
    have hz := Set.ext_iff.mp hzero z
    simpa [D] using hz
  rw [hsupport]
  exact
    (HereditarilyLindelofSpace.isLindelof D.support).countable_of_isDiscrete
      D.discreteSupport

/-- The subtype of distinct nonzero function zeros is countable. -/
noncomputable instance NonzeroZero_countable :
    Countable (NonzeroZero F) := by
  exact
    ((zeroSet_countable F).mono (by
      intro z hz
      exact hz.1)).to_subtype

/-- The exact multiplicity-bearing occurrence type is countable. -/
noncomputable instance ZeroOccurrence_countable :
    Countable (ZeroOccurrence F) := by
  unfold ZeroOccurrence
  infer_instance

/-- Proposition form of countability for downstream interfaces. -/
theorem ZeroOccurrence_countable_holds :
    Countable (ZeroOccurrence F) := by
  infer_instance


/-- The exact occurrence involution is involutive, including multiplicity labels. -/
theorem ZeroOccurrenceNegEquiv_involutive :
    Function.Involutive (ZeroOccurrenceNegEquiv F) := by
  intro i
  let j := ZeroOccurrenceNegEquiv F (ZeroOccurrenceNegEquiv F i)
  have hfst : j.fst = i.fst := by
    apply Subtype.ext
    change - -i.fst.1 = i.fst.1
    simp
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (by rw [hfst])).2
  rfl

theorem ZeroOccurrenceNegEquiv_fixedPointFree (i : ZeroOccurrence F) :
    ZeroOccurrenceNegEquiv F i ≠ i := by
  intro hi
  have hloc := ZeroOccurrenceNegEquiv_loc F i
  rw [hi] at hloc
  have htwo : (2 : ℂ)*ZeroOccurrenceLoc F i = 0 := by linear_combination hloc
  exact ZeroOccurrenceLoc_ne_zero F i ((mul_eq_zero.mp htwo).resolve_left (by norm_num))

def ZeroOccurrenceNegationPairingData : HadamardNegationPairingData (ZeroOccurrenceLoc F) :=
  HadamardNegationPairingData.ofInvolution (ZeroOccurrenceLoc F)
    (ZeroOccurrenceNegEquiv F) (ZeroOccurrenceNegEquiv_involutive F)
    (ZeroOccurrenceNegEquiv_fixedPointFree F) (ZeroOccurrenceNegEquiv_loc F)

/-- Fibers over locations carry exactly the analytic multiplicity. -/
def ZeroOccurrenceLocFiberEquiv (z : NonzeroZero F) :
    {i : ZeroOccurrence F // ZeroOccurrenceLoc F i = z.1} ≃
      Fin (analyticOrderNatAt F.toFun z.1) :=
  (show {i : ZeroOccurrence F // ZeroOccurrenceLoc F i = z.1} ≃
      {i : ZeroOccurrence F // i.1 = z} from
    { toFun := fun i => ⟨i.1, Subtype.ext i.2⟩
      invFun := fun i => ⟨i.1, congrArg Subtype.val i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans (ZeroOccurrenceFiberEquiv F z)

theorem ZeroOccurrenceLoc_fiber_natCard (z : NonzeroZero F) :
    Nat.card {i : ZeroOccurrence F // ZeroOccurrenceLoc F i = z.1} =
      analyticOrderNatAt F.toFun z.1 := by
  rw [Nat.card_congr (ZeroOccurrenceLocFiberEquiv F z), Nat.card_fin]

theorem analyticOrderAt_eq_canonical_divisor (z : ℂ) :
    analyticOrderAt F.toFun z =
      (if z = 0 then (OriginMultiplicity F : ENat) else 0)+
        (Nat.card {i : ZeroOccurrence F // ZeroOccurrenceLoc F i = z} : ENat) := by
  by_cases hz0 : z = 0
  · subst z
    letI : IsEmpty {i : ZeroOccurrence F // ZeroOccurrenceLoc F i = 0} :=
      ⟨fun i => ZeroOccurrenceLoc_ne_zero F i.1 i.2⟩
    simpa using analyticOrderAt_zero F
  · rw [if_neg hz0, zero_add]
    by_cases hz : F.toFun z = 0
    · rw [ZeroOccurrenceLoc_fiber_natCard F (⟨z,hz,hz0⟩ : NonzeroZero F)]
      exact (Nat.cast_analyticOrderNatAt (analyticOrderAt_ne_top F z)).symm
    · letI : IsEmpty {i : ZeroOccurrence F // ZeroOccurrenceLoc F i = z} :=
        ⟨fun i => hz (i.2 ▸ ZeroOccurrenceLoc_is_zero F i.1)⟩
      simpa using (F.differentiable.analyticAt z).analyticOrderAt_eq_zero.mpr hz

end UnitDistance.EntireDivisor
