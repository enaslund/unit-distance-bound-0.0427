module

public import UnitDistance.TensorFiniteProfiles

@[expose] public section
set_option backward.privateInPublic true


/-!
# Individual finite-place shell factors

One-dimensional shell factors allow the two primes in an actual conjugate
pair to retain their own completion types. Their product has the same exact
mass as the two-coordinate witness, without any identification of completions.
-/

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace UnitDistance.Local.BallSystem
variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
  {μ : Measure G} {Q : ℝ} (B : BallSystem G μ Q)

def shellFactor (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ) (x : G) : ℝ :=
  ∑ i ∈ I, (B.shell k i).indicator (fun _ => w i) x

theorem shellFactor_measurable (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ) :
    Measurable (B.shellFactor k I w) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.indicator (B.shell_measurable k i))

theorem shellFactor_nonneg (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (x : G) : 0 ≤ B.shellFactor k I w x :=
  Finset.sum_nonneg (fun i hi => Set.indicator_nonneg (fun _ _ => hw i hi) x)

theorem shellFactor_eq_weight (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ)
    {i : ℕ} (hi : i ∈ I) {x : G} (hx : x ∈ B.shell k i) :
    B.shellFactor k I w x = w i := by
  rw [shellFactor, Finset.sum_eq_single i]
  · simp [hx]
  · intro j hj hji
    have hnot : x ∉ B.shell k j :=
      fun hxj => Set.disjoint_left.mp (B.shell_disjoint k hji) hxj hx
    simp [hnot]
  · exact fun h => False.elim (h hi)

theorem shellFactor_eq_zero (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ)
    {x : G} (hx : ∀ i ∈ I, x ∉ B.shell k i) : B.shellFactor k I w x = 0 := by
  exact Finset.sum_eq_zero (fun i hi => by simp [hx i hi])

theorem shellFactor_rpow (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ)
    {q : ℝ} (hq : q ≠ 0) (x : G) :
    B.shellFactor k I w x ^ q = B.shellFactor k I (fun i => w i ^ q) x := by
  by_cases hx : ∃ i ∈ I, x ∈ B.shell k i
  · obtain ⟨i, hi, hx⟩ := hx
    rw [B.shellFactor_eq_weight k I w hi hx,
      B.shellFactor_eq_weight k I (fun i => w i ^ q) hi hx]
  · push Not at hx
    rw [B.shellFactor_eq_zero k I w hx,
      B.shellFactor_eq_zero k I (fun i => w i ^ q) hx, Real.zero_rpow hq]

theorem shellFactor_integrable (hQ : 0 < Q) (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ) :
    Integrable (B.shellFactor k I w) μ := by
  exact integrable_finsetSum _ (fun i _ =>
    (integrable_indicator_iff (B.shell_measurable k i)).mpr
      (integrableOn_const (B.shell_measure_ne_top hQ k i)))

theorem shellFactor_rpow_integrable (hQ : 0 < Q) (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ)
    {q : ℝ} (hq : q ≠ 0) : Integrable (fun x => B.shellFactor k I w x ^ q) μ := by
  simp_rw [B.shellFactor_rpow k I w hq]
  exact B.shellFactor_integrable hQ k I _

theorem shellFactor_moment (hQ : 0 < Q) (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ)
    {q : ℝ} (hq : q ≠ 0) :
    (∫ x, B.shellFactor k I w x ^ q ∂μ) = Q ^ k * shellLpMass Q q I w := by
  simp_rw [B.shellFactor_rpow k I w hq]
  unfold shellFactor
  rw [integral_finsetSum]
  · simp_rw [integral_indicator_const _ (B.shell_measurable k _), smul_eq_mul,
      B.shell_volume hQ]
    simp only [shellLpMass, Finset.mul_sum, mul_assoc]
  · intro i hi
    exact (integrable_indicator_iff (B.shell_measurable k i)).mpr
      (integrableOn_const (B.shell_measure_ne_top hQ k i))

theorem shellFactor_period (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ)
    {z : G} (hz : z ∈ B.ball k) (x : G) :
    B.shellFactor k I w (x + z) = B.shellFactor k I w x := by
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Set.indicator, B.mem_shell_add_period_iff k i hz x]

theorem shellFactor_invariant (φ : G → G)
    (hφ : ∀ a x, φ x ∈ B.ball a ↔ x ∈ B.ball a)
    (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ) (x : G) :
    B.shellFactor k I w (φ x) = B.shellFactor k I w x := by
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Set.indicator, B.shell_invariant φ hφ k i x]

/-- Shell factors commute with maps preserving all integer-indexed balls,
even when the source and target are different actual completion fields. -/
theorem shellFactor_transport {H : Type*} [AddCommGroup H] [MeasurableSpace H]
    {ν : Measure H} {R : ℝ} (C : BallSystem H ν R) (φ : G → H)
    (hφ : ∀ a x, φ x ∈ C.ball a ↔ x ∈ B.ball a)
    (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ) (x : G) :
    C.shellFactor k I w (φ x) = B.shellFactor k I w x := by
  have hs (i : ℕ) : φ x ∈ C.shell k i ↔ x ∈ B.shell k i := by
    cases i with
    | zero => exact hφ k x
    | succ i => simp only [shell, Set.mem_sdiff, SetLike.mem_coe, hφ]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Set.indicator, hs]

theorem shellFactor_support (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ)
    {x : G} (hx : x ∈ Function.support (B.shellFactor k I w)) :
    x ∈ B.ball (k + (I.sup id : ℕ)) := by
  by_contra h
  apply hx
  apply B.shellFactor_eq_zero
  intro i hi hx
  apply h
  have hi' : i ≤ I.sup id := Finset.le_sup (f := id) hi
  exact B.mono (by omega) (B.shell_subset k i hx)

theorem shellFactor_log_norm_le (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ) (x : G) :
    ‖Real.log (B.shellFactor k I w x)‖ ≤ ∑ i ∈ I, |Real.log (w i)| := by
  by_cases hx : ∃ i ∈ I, x ∈ B.shell k i
  · obtain ⟨i, hi, hx⟩ := hx
    rw [B.shellFactor_eq_weight k I w hi hx, Real.norm_eq_abs]
    exact Finset.single_le_sum (s := I) (f := fun i => |Real.log (w i)|)
      (fun _ _ => abs_nonneg _) hi
  · push Not at hx
    rw [B.shellFactor_eq_zero k I w hx, Real.log_zero, norm_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

variable [TopologicalSpace G]

theorem shellFactor_locallyConstant (hB : ∀ a, IsClopen (B.ball a : Set G))
    (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ) : IsLocallyConstant (B.shellFactor k I w) := by
  unfold shellFactor
  induction I using Finset.induction_on with
  | empty =>
    apply IsLocallyConstant.of_constant
    intro x y
    simp
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact ((LocallyConstant.const G (w i)).indicator (B.shell_clopen hB k i)).isLocallyConstant.add ih

theorem shellFactor_hasCompactSupport [T2Space G]
    (hB : ∀ a, IsCompact (B.ball a : Set G)) (k : ℤ) (I : Finset ℕ) (w : ℕ → ℝ) :
    HasCompactSupport (B.shellFactor k I w) := by
  apply HasCompactSupport.intro (hB (k + (I.sup id : ℕ)))
  intro x hx
  by_contra hz
  exact hx (B.shellFactor_support k I w hz)

end UnitDistance.Local.BallSystem

namespace UnitDistance.Witness
variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
  {μ : Measure G} (v : Fin 11) (B : Local.BallSystem G μ (residueCard v))

def localShellFactor (k : ℤ) : G → ℝ := B.shellFactor k (Finset.range 6) (shellWeightNat v)

theorem localShellFactor_moment (k : ℤ) :
    (∫ x, localShellFactor v B k x ^ p ∂μ) = residueCard v ^ k * finiteLp v := by
  rw [localShellFactor, B.shellFactor_moment (zero_lt_one.trans (residueCard_gt_one v))
    k _ _ witness_basic.2.2.1.ne', shellLpMass_witness]

/-- The two-coordinate witness is literally the product of its two one-dimensional factors. -/
theorem localShellProfile_eq_factors (x : G × G) :
    localShellProfile v B x = localShellFactor v B 0 x.1 *
      localShellFactor v B (periodPower v) x.2 := by
  unfold localShellProfile Local.BallSystem.shellProfile localShellFactor Local.BallSystem.shellFactor
  rw [Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Local.BallSystem.shellCell, Set.indicator, Set.mem_prod]
  split_ifs <;> simp_all

end UnitDistance.Witness
