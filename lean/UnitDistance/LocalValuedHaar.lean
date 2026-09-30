module

public import UnitDistance.LocalRegularity
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! # Haar volumes and reciprocal steps in arbitrary nonarchimedean local fields

The balls use the integer-valued valuation directly. In particular no chosen
extension of the `p`-adic norm, ramification normalization, or ball-volume law
is an additional hypothesis.
-/

noncomputable section
open Set MeasureTheory ValuativeRel WithZero
open scoped BigOperators ENNReal

namespace UnitDistance.Local.ValuedHaar

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

/-- The valuation with value group canonically identified with `ℤᵐ⁰`. -/
def intValuation : Valuation K ℤᵐ⁰ :=
  (valuation K).map (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)

theorem intValuation_apply (x : K) : intValuation K x =
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x) := rfl

theorem intValuation_surjective : Function.Surjective (intValuation K) :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).surjective.comp valuation_surjective

/-- Actual valuation balls of integer radius index. -/
def ball (a : ℤ) : AddSubgroup K where
  carrier := {x | intValuation K x ≤ exp a}
  zero_mem' := by simp
  add_mem' := fun hx hy => (intValuation K).map_add_le hx hy
  neg_mem' := by intro x hx; simpa using hx

theorem ball_mono : Monotone (ball K) := by
  intro a b hab x hx
  exact hx.trans (exp_le_exp.mpr hab)

theorem ball_eq (a : ℤ) : (ball K a : Set K) =
    {x | valuation K x ≤ (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm (exp a)} := by
  ext x
  change intValuation K x ≤ exp a ↔ valuation K x ≤ _
  rw [← (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm.strictMono.le_iff_le]
  simp only [intValuation_apply, OrderMonoidIso.symm_apply_apply]

theorem ball_compact (a : ℤ) : IsCompact (ball K a : Set K) := by
  rw [ball_eq]
  exact IsNonarchimedeanLocalField.isCompact_closedBall K _

/-- A uniformizer chosen from the surjective integer valuation. -/
def uniformizer : K := (intValuation_surjective K (exp (-1))).choose

@[simp] theorem intValuation_uniformizer :
    intValuation K (uniformizer K) = exp (-1) :=
  (intValuation_surjective K (exp (-1))).choose_spec

theorem uniformizer_ne_zero : uniformizer K ≠ 0 := by
  intro h
  have := intValuation_uniformizer K
  exact exp_ne_zero (by simpa only [h, map_zero] using this.symm)

@[simp] theorem intValuation_uniformizer_zpow (a : ℤ) :
    intValuation K (uniformizer K ^ a) = exp (-a) := by
  rw [map_zpow₀, intValuation_uniformizer]
  simp

theorem ball_clopen (a : ℤ) : IsClopen (ball K a : Set K) := by
  have he : (ball K a : Set K) =
      {x | (valuation K).restrict x ≤ (valuation K).restrict (uniformizer K ^ (-a))} := by
    ext x
    change intValuation K x ≤ exp a ↔
      (valuation K).restrict x ≤ (valuation K).restrict (uniformizer K ^ (-a))
    rw [Valuation.restrict_le_iff]
    rw [← (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).strictMono.le_iff_le]
    change intValuation K x ≤ exp a ↔ intValuation K x ≤ intValuation K (uniformizer K ^ (-a))
    simp
  rw [he]
  exact (valuation K).isClopen_closedBall ((valuation K).restrict.ne_zero_iff.mpr (zpow_ne_zero (-a) (uniformizer_ne_zero K)))

theorem intValuation_le_one_iff (x : K) : intValuation K x ≤ 1 ↔ valuation K x ≤ 1 := by
  rw [intValuation_apply, ← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K),
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).strictMono.le_iff_le]

theorem intValuation_lt_one_iff (x : K) : intValuation K x < 1 ↔ valuation K x < 1 := by
  rw [intValuation_apply, ← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K),
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).strictMono.lt_iff_lt]

theorem lt_one_iff_le_exp_neg_one (x : ℤᵐ⁰) : x < 1 ↔ x ≤ exp (-1) := by
  simpa only [← exp_add, neg_add_cancel, exp_zero] using
    (lt_mul_exp_iff_le (x := x) (y := exp (-1)) exp_ne_zero)

local instance residueFintype : Fintype 𝓀[K] := Fintype.ofFinite _

/-- The independently defined cardinality of the actual residue field. -/
def residueCard : ℕ := Nat.card 𝓀[K]

theorem residueCard_gt_one : 1 < residueCard K := by
  rw [residueCard, Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

theorem ball_zero_eq_integer : (ball K 0 : Set K) = (𝒪[K] : Set K) := by
  ext x
  change intValuation K x ≤ exp 0 ↔ valuation K x ≤ 1
  rw [exp_zero, intValuation_le_one_iff]

/-- Chosen representatives in the valuation ring of the actual residue field. -/
def residueRep (r : 𝓀[K]) : 𝒪[K] := (IsLocalRing.residue_surjective r).choose

@[simp] theorem residue_residueRep (r : 𝓀[K]) :
    IsLocalRing.residue 𝒪[K] (residueRep K r) = r :=
  (IsLocalRing.residue_surjective r).choose_spec

theorem residueRep_le_one (r : 𝓀[K]) : intValuation K (residueRep K r) ≤ 1 :=
  (intValuation_le_one_iff K _).mpr (residueRep K r).property

theorem residue_eq_iff (x y : 𝒪[K]) :
    IsLocalRing.residue 𝒪[K] x = IsLocalRing.residue 𝒪[K] y ↔
      intValuation K ((x : K) - y) ≤ exp (-1) := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change valuation K ((x : K) - y) < 1 ↔ _
  rw [← intValuation_lt_one_iff, lt_one_iff_le_exp_neg_one]

/-- Centers indexed by the actual residue field. -/
def center (a : ℤ) (r : 𝓀[K]) : K :=
  uniformizer K ^ (-(a + 1)) * (residueRep K r : K)

def cell (a : ℤ) (r : 𝓀[K]) : Set K := {x | x - center K a r ∈ ball K a}

theorem normalized_sub (a : ℤ) (r : 𝓀[K]) (x : K) :
    uniformizer K ^ (a + 1) * (x - center K a r) =
      uniformizer K ^ (a + 1) * x - (residueRep K r : K) := by
  rw [mul_sub]
  congr 1
  rw [center, ← mul_assoc, ← zpow_add₀ (uniformizer_ne_zero K), add_neg_cancel, zpow_zero, one_mul]

theorem scaled_mem (a : ℤ) (x : K) :
    x ∈ ball K a ↔ intValuation K (uniformizer K ^ (a + 1) * x) ≤ exp (-1) := by
  change intValuation K x ≤ exp a ↔ _
  rw [map_mul, intValuation_uniformizer_zpow]
  have he : exp (-(a + 1)) * exp a = exp (-1) := by
    rw [← exp_add]
    congr 1
    omega
  rw [← he, mul_le_mul_iff_right₀ exp_pos]

theorem cell_iff (a : ℤ) (r : 𝓀[K]) (x : K) :
    x ∈ cell K a r ↔
      intValuation K (uniformizer K ^ (a + 1) * x - (residueRep K r : K)) ≤ exp (-1) := by
  change x - center K a r ∈ ball K a ↔ _
  rw [scaled_mem, normalized_sub]

theorem cell_subset (a : ℤ) (r : 𝓀[K]) : cell K a r ⊆ ball K (a + 1) := by
  intro x hx
  have hc : intValuation K (center K a r) ≤ exp (a + 1) := by
    rw [center, map_mul, intValuation_uniformizer_zpow, neg_neg]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (residueRep_le_one K r) (le_of_lt exp_pos)
  have hxa : intValuation K (x - center K a r) ≤ exp (a + 1) :=
    hx.trans (exp_le_exp.mpr (by omega))
  change intValuation K x ≤ exp (a + 1)
  convert (intValuation K).map_add_le hxa hc using 1
  rw [sub_add_cancel]

theorem ball_eq_union_cells (a : ℤ) : (ball K (a + 1) : Set K) = ⋃ r : 𝓀[K], cell K a r := by
  apply Set.Subset.antisymm
  · intro x hx
    have hu : intValuation K (uniformizer K ^ (a + 1) * x) ≤ 1 := by
      rw [map_mul, intValuation_uniformizer_zpow]
      calc
        exp (-(a + 1)) * intValuation K x ≤ exp (-(a + 1)) * exp (a + 1) :=
          mul_le_mul_of_nonneg_left hx (le_of_lt exp_pos)
        _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
    let u : 𝒪[K] := ⟨uniformizer K ^ (a + 1) * x, (intValuation_le_one_iff K _).mp hu⟩
    let r : 𝓀[K] := IsLocalRing.residue 𝒪[K] u
    apply Set.mem_iUnion.mpr
    refine ⟨r, (cell_iff K a r x).mpr ?_⟩
    exact (residue_eq_iff K u (residueRep K r)).mp (by simp only [residue_residueRep]; rfl)
  · apply Set.iUnion_subset
    intro r
    exact cell_subset K a r

theorem cells_disjoint (a : ℤ) : Pairwise (fun r s => Disjoint (cell K a r) (cell K a s)) := by
  intro r s hrs
  apply Set.disjoint_left.mpr
  intro x hxr hxs
  have hr := (cell_iff K a r x).mp hxr
  have hs := (cell_iff K a s x).mp hxs
  have hsmall : intValuation K ((residueRep K r : K) - residueRep K s) ≤ exp (-1) := by
    have he : (residueRep K r : K) - residueRep K s =
        (uniformizer K ^ (a + 1) * x - residueRep K s) -
          (uniformizer K ^ (a + 1) * x - residueRep K r) := by ring
    rw [he]
    exact (intValuation K).map_sub_le hs hr
  have heq := (residue_eq_iff K (residueRep K r) (residueRep K s)).mpr hsmall
  exact hrs (by simpa only [residue_residueRep] using heq)

local instance valuedMeasurableSpace : MeasurableSpace K := borel K
local instance valuedBorelSpace : BorelSpace K := ⟨rfl⟩

theorem ball_measurable (a : ℤ) : MeasurableSet (ball K a : Set K) :=
  (ball_clopen K a).isClosed.measurableSet

theorem cell_measurable (a : ℤ) (r : 𝓀[K]) : MeasurableSet (cell K a r) :=
  (ball_measurable K a).preimage (measurable_id.sub_const _)

theorem measure_cell (μ : Measure K) [μ.IsAddRightInvariant] (a : ℤ) (r : 𝓀[K]) :
    μ (cell K a r) = μ (ball K a) := by
  change μ ((fun x => x - center K a r) ⁻¹' (ball K a : Set K)) = _
  simp only [sub_eq_add_neg, measure_preimage_add_right]

theorem measureReal_cell (μ : Measure K) [μ.IsAddRightInvariant] (a : ℤ) (r : 𝓀[K]) :
    μ.real (cell K a r) = μ.real (ball K a) := by
  simp only [measureReal_def, measure_cell]

/-- Each successive ball has exactly the residue-cardinality multiple of its
predecessor's additive Haar volume. -/
theorem haar_ball_succ (μ : Measure K) [μ.IsAddHaarMeasure] (a : ℤ) :
    μ.real (ball K (a + 1)) = (residueCard K : ℝ) * μ.real (ball K a) := by
  rw [ball_eq_union_cells, measureReal_iUnion_fintype (cells_disjoint K a)
    (cell_measurable K a) (fun r => ?_)]
  · simp only [measureReal_cell, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      residueCard, Nat.card_eq_fintype_card]
  · rw [measure_cell]
    exact (ball_compact K a).measure_ne_top

/-- All integer-indexed valuation balls have exact residue-cardinality power
volume for any Haar measure normalized on the valuation ring. -/
theorem haar_ball_volume (μ : Measure K) [μ.IsAddHaarMeasure]
    (hμ : μ.real (ball K 0) = 1) (a : ℤ) :
    μ.real (ball K a) = (residueCard K : ℝ) ^ a := by
  have hQ : (residueCard K : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (lt_trans Nat.zero_lt_one (residueCard_gt_one K))
  induction a using Int.induction_on with
  | zero => simpa using hμ
  | succ i ih =>
    rw [haar_ball_succ, ih, zpow_add₀ hQ, zpow_one]
    ring
  | pred i ih =>
    have h := haar_ball_succ K μ (-(i : ℤ) - 1)
    rw [sub_add_cancel, ih] at h
    apply mul_left_cancel₀ hQ
    rw [← h]
    calc
      (residueCard K : ℝ) ^ (-(i : ℤ)) =
        (residueCard K : ℝ) ^ (1 + (-(i : ℤ) - 1)) := by congr 1; ring
      _ = _ := by rw [zpow_add₀ hQ, zpow_one]

/-- The compact open valuation ring as Haar normalization set. -/
def unitBall : TopologicalSpace.PositiveCompacts K where
  carrier := ball K 0
  isCompact' := ball_compact K 0
  interior_nonempty' := by
    rw [(ball_clopen K 0).isOpen.interior_eq]
    exact ⟨0, (ball K 0).zero_mem⟩

/-- Additive Haar measure normalized on the actual valuation ring. -/
def normalizedHaar : Measure K := Measure.addHaarMeasure (unitBall K)

instance : (normalizedHaar K).IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_addHaarMeasure _

theorem normalizedHaar_zero : (normalizedHaar K).real (ball K 0) = 1 := by
  change ((Measure.addHaarMeasure (unitBall K)) (unitBall K)).toReal = 1
  rw [Measure.addHaarMeasure_self, ENNReal.toReal_one]

theorem normalizedHaar_ball (a : ℤ) :
    (normalizedHaar K).real (ball K a) = (residueCard K : ℝ) ^ a :=
  haar_ball_volume K _ (normalizedHaar_zero K) a

/-- The normalized additive Haar measure and all its ball volumes exist
without any auxiliary volume or normalization hypothesis. -/
theorem exists_normalizedHaar : ∃ μ : Measure K, μ.IsAddHaarMeasure ∧
    ∀ a : ℤ, μ.real (ball K a) = (residueCard K : ℝ) ^ a :=
  ⟨normalizedHaar K, inferInstance, normalizedHaar_ball K⟩

/-- Fully constructed measured ball data for every nonarchimedean local field. -/
def ballSystem : BallSystem K (normalizedHaar K) (residueCard K) where
  ball := ball K
  mono := ball_mono K
  measurable := ball_measurable K
  volume := normalizedHaar_ball K

theorem iUnion_ball : (⋃ a : ℤ, (ball K a : Set K)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨(intValuation K x).log, le_exp_log⟩

instance sigmaCompactSpace : SigmaCompactSpace K := ⟨by
  rw [← iUnion_ball K]
  exact isSigmaCompact_iUnion _ (fun a => (ball_compact K a).isSigmaCompact)⟩

instance secondCountableTopology : SecondCountableTopology K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : Valuation.RankOne (Valued.v (R := K)) :=
    inferInstanceAs (Valuation.RankOne (valuation K))
  letI := Valued.toNormedField K (ValueGroupWithZero K)
  exact EMetric.secondCountable_of_sigmaCompact K

instance : SFinite (normalizedHaar K) :=
  inferInstanceAs (SFinite (Measure.addHaarMeasure (unitBall K)))

/-- Actual valuation-one units, with the measurable structure from the field. -/
abbrev ValuationOneUnits := {u : K // intValuation K u = 1}

theorem valuationOneUnits_ne_zero (u : ValuationOneUnits K) : (u : K) ≠ 0 := by
  intro h
  have := u.property
  simp only [h, map_zero] at this
  exact zero_ne_one this

/-- Actual reciprocal field displacements, with no step-membership hypothesis. -/
def reciprocalSteps : (ballSystem K).ReciprocalSteps (ValuationOneUnits K) where
  step n u := (uniformizer K ^ n * (u : K), uniformizer K ^ (-n) * (u : K)⁻¹)
  fst_mem := by
    intro n u a
    change intValuation K (uniformizer K ^ n * (u : K)) ≤ exp a ↔ -a ≤ n
    rw [map_mul, intValuation_uniformizer_zpow, u.property, mul_one, exp_le_exp]
    omega
  snd_mem := by
    intro n u b
    change intValuation K (uniformizer K ^ (-n) * (u : K)⁻¹) ≤ exp b ↔ n ≤ b
    rw [map_mul, intValuation_uniformizer_zpow, map_inv₀, u.property, inv_one, mul_one,
      neg_neg, exp_le_exp]

theorem reciprocalSteps_measurable (n : ℤ) : Measurable ((reciprocalSteps K).step n) := by
  exact (continuous_const.mul continuous_subtype_val).measurable.prodMk
    (continuous_const.mul (continuous_subtype_val.inv₀ (valuationOneUnits_ne_zero K))).measurable

theorem ball_unit_invariant (a : ℤ) (u : ValuationOneUnits K) (x : K) :
    (u : K) * x ∈ ball K a ↔ x ∈ ball K a := by
  change intValuation K ((u : K) * x) ≤ exp a ↔ intValuation K x ≤ exp a
  rw [map_mul, u.property, one_mul]

/-- The full local weighted operator formula on every nonarchimedean local
field. The additive Haar measure, residue cardinality, ball volumes, uniformizer
and reciprocal steps are constructed; only the freely chosen unit probability
measure and finite profile remain parameters. -/
theorem operator_formula (ν : Measure (ValuationOneUnits K)) [IsProbabilityMeasure ν]
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    (∫ x, (ballSystem K).shellProfile k I w x *
      (ballSystem K).displacementOperator (reciprocalSteps K) ν
        ((ballSystem K).shellProfile k I w) x ∂(normalizedHaar K).prod (normalizedHaar K)) =
      (residueCard K : ℝ) ^ k * ∑ ij ∈ I, ∑ rt ∈ I,
        w ij * shellKernel (residueCard K) k ij.1 ij.2 rt.1 rt.2 * w rt := by
  exact (ballSystem K).shellProfile_operator_eq (reciprocalSteps K) ν
    (by exact_mod_cast lt_trans Nat.zero_lt_one (residueCard_gt_one K))
    (reciprocalSteps_measurable K) k I w

end UnitDistance.Local.ValuedHaar
