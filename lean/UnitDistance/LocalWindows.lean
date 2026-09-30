module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Additive local ball overlaps

The ball axioms below are the elementary properties of `π⁻ᵃ O` in a discretely
valued local field with normalized additive Haar measure.  In particular, no
overlap formula is assumed.  They also make explicit the outstanding bridge
to a chosen construction of local completions.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace UnitDistance.Local

attribute [local instance] Classical.propDecidable

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]

/-- A nested family of measurable additive balls with its ordinary Haar volume.
The positive real `Q` is the residue cardinality in the intended application. -/
structure BallSystem (G : Type*) [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (Q : ℝ) where
  ball : ℤ → AddSubgroup G
  mono : Monotone ball
  measurable : ∀ a, MeasurableSet (ball a : Set G)
  volume : ∀ a, μ.real (ball a : Set G) = Q ^ a

namespace BallSystem

variable {μ : Measure G} {Q : ℝ} (B : BallSystem G μ Q)

/-- The set of first endpoints whose translated endpoint lies in the other ball. -/
def ballOverlap (a c : ℤ) (z : G) : Set G :=
  {x | x ∈ B.ball a ∧ x + z ∈ B.ball c}

theorem ballOverlap_measurable (a c : ℤ) (z : G) :
    MeasurableSet (B.ballOverlap a c z) :=
  (B.measurable a).inter ((B.measurable c).preimage (measurable_id.add_const z))

omit [MeasurableAdd G] in
theorem ballOverlap_eq_of_le {a c : ℤ} (h : a ≤ c) {z : G}
    (hz : z ∈ B.ball c) : B.ballOverlap a c z = B.ball a := by
  ext x
  exact ⟨And.left, fun hx => ⟨hx, (B.ball c).add_mem (B.mono h hx) hz⟩⟩

omit [MeasurableAdd G] in
theorem ballOverlap_eq_preimage_of_le {a c : ℤ} (h : c ≤ a) {z : G}
    (hz : z ∈ B.ball a) :
    B.ballOverlap a c z = (fun x => x + z) ⁻¹' (B.ball c : Set G) := by
  ext x
  constructor
  · exact And.right
  · intro hx
    refine ⟨?_, hx⟩
    have := (B.ball a).sub_mem (B.mono h hx) hz
    simpa using this

omit [MeasurableAdd G] in
theorem ballOverlap_eq_empty {a c : ℤ} {z : G}
    (hz : z ∉ B.ball (max a c)) : B.ballOverlap a c z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hxz⟩
  apply hz
  have := (B.ball (max a c)).sub_mem
    (B.mono (le_max_right a c) hxz) (B.mono (le_max_left a c) hx)
  simpa using this

/-- The translated intersection has the smaller volume precisely when the
displacement lies in the larger ball.  This uses genuine translation invariance. -/
theorem ballOverlap_volume [μ.IsAddRightInvariant] (a c : ℤ) (z : G) :
    μ.real (B.ballOverlap a c z) =
      if z ∈ B.ball (max a c) then Q ^ min a c else 0 := by
  classical
  split_ifs with hz
  · rcases le_total a c with h | h
    · rw [max_eq_right h] at hz
      rw [B.ballOverlap_eq_of_le h hz, B.volume, min_eq_left h]
    · rw [max_eq_left h] at hz
      rw [B.ballOverlap_eq_preimage_of_le h hz, measureReal_def,
        measure_preimage_add_right, ← measureReal_def, B.volume, min_eq_right h]
  · rw [B.ballOverlap_eq_empty hz]
    simp

/-- Indicator of a rectangular additive ball, taking real values. -/
def rectangle (a b : ℤ) : G × G → ℝ :=
  ((B.ball a : Set G) ×ˢ (B.ball b : Set G)).indicator (fun _ => 1)

omit [MeasurableAdd G] in
theorem rectangle_overlap_integrand (a b c e : ℤ) (z : G × G) (x : G × G) :
    B.rectangle a b x * B.rectangle c e (x + z) =
      (B.ballOverlap a c z.1 ×ˢ B.ballOverlap b e z.2).indicator (fun _ => 1) x := by
  classical
  simp only [rectangle, ballOverlap, Set.indicator, Set.mem_prod, Set.mem_setOf_eq,
    Prod.fst_add, Prod.snd_add]
  split_ifs <;> simp_all

/-- Exact additive Haar integral of the product of two translated rectangle
indicators.  Negative ball indices are allowed. -/
theorem rectangle_overlap [SFinite μ] [μ.IsAddRightInvariant]
    (a b c e : ℤ) (z : G × G) :
    (∫ x, B.rectangle a b x * B.rectangle c e (x + z) ∂μ.prod μ) =
      if z.1 ∈ B.ball (max a c) ∧ z.2 ∈ B.ball (max b e)
      then Q ^ min a c * Q ^ min b e else 0 := by
  classical
  simp_rw [B.rectangle_overlap_integrand]
  rw [integral_indicator_const 1
    ((B.ballOverlap_measurable a c z.1).prod (B.ballOverlap_measurable b e z.2))]
  rw [smul_eq_mul, mul_one, measureReal_prod_prod,
    B.ballOverlap_volume, B.ballOverlap_volume]
  split_ifs <;> simp_all

/-- Norm-one steps, with unit parameter and integer valuation label.  These
membership laws express valuations `n` and `-n`; the unit measure is separate. -/
structure ReciprocalSteps (U : Type*) where
  step : ℤ → U → G × G
  fst_mem : ∀ n u a, (step n u).1 ∈ B.ball a ↔ -a ≤ n
  snd_mem : ∀ n u b, (step n u).2 ∈ B.ball b ↔ n ≤ b

variable {U : Type*} [MeasurableSpace U] (S : B.ReciprocalSteps U)
    (ν : Measure U) [IsProbabilityMeasure ν]

/-- The overlap functional, written in Tonelli order: integer counting,
normalized unit average, and additive overlap integral. -/
def rectangleGram (a b c e : ℤ) : ℝ :=
  ∑' n : ℤ, ∫ u, ∫ x, B.rectangle a b x *
    B.rectangle c e (x + S.step n u) ∂μ.prod μ ∂ν

theorem rectangle_unit_average [SFinite μ] [μ.IsAddRightInvariant]
    (a b c e n : ℤ) :
    (∫ u, ∫ x, B.rectangle a b x * B.rectangle c e (x + S.step n u)
      ∂μ.prod μ ∂ν) =
      if n ∈ Finset.Icc (-max a c) (max b e)
      then Q ^ min a c * Q ^ min b e else 0 := by
  simp_rw [B.rectangle_overlap, S.fst_mem, S.snd_mem]
  simp

/-- The exact rectangle Gram formula in the manuscript, including the positive
part through `Int.toNat`. The normalized unit measure contributes no `Q - 1`. -/
theorem rectangleGram_eq [SFinite μ] [μ.IsAddRightInvariant]
    (a b c e : ℤ) :
    B.rectangleGram S ν a b c e =
      Q ^ min a c * Q ^ min b e * ((max a c + max b e + 1).toNat : ℝ) := by
  classical
  unfold rectangleGram
  simp_rw [B.rectangle_unit_average S ν]
  rw [tsum_eq_sum (s := Finset.Icc (-max a c) (max b e))]
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    rw [Int.card_Icc]
    rw [show max b e + 1 - -max a c = max a c + max b e + 1 by ring]
    ring
  · intro n hn
    simp [hn]

end BallSystem
end UnitDistance.Local
