module

public import UnitDistance.LocalShells

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual shell profiles: Haar mass and support-independent periods -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace UnitDistance.Local.BallSystem

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
variable {μ : Measure G} {Q : ℝ} (B : BallSystem G μ Q)

theorem ball_measure_ne_top (hQ : 0 < Q) (a : ℤ) : μ (B.ball a) ≠ ∞ := by
  intro h
  have hv := B.volume a
  rw [measureReal_def, h, ENNReal.toReal_top] at hv
  exact (ne_of_gt (zpow_pos hQ a)) hv.symm

/-- The `i`th shell above the base ball with index `k`. -/
def shell (k : ℤ) : ℕ → Set G :=
  Nat.rec (B.ball k : Set G)
    (fun i _ => (B.ball (k + (i + 1 : ℕ))) \ (B.ball (k + (i : ℕ))))

theorem shell_measurable (k : ℤ) (i : ℕ) : MeasurableSet (B.shell k i) := by
  cases i with
  | zero => exact B.measurable k
  | succ i => exact (B.measurable _).diff (B.measurable _)

theorem shell_subset (k : ℤ) (i : ℕ) : B.shell k i ⊆ B.ball (k + (i : ℕ)) := by
  cases i <;> simp [shell]

theorem shell_measure_ne_top (hQ : 0 < Q) (k : ℤ) (i : ℕ) :
    μ (B.shell k i) ≠ ∞ :=
  measure_ne_top_of_subset (B.shell_subset k i) (B.ball_measure_ne_top hQ _)

theorem shell_volume (hQ : 0 < Q) (k : ℤ) (i : ℕ) :
    μ.real (B.shell k i) = Q ^ k * shellMass Q i := by
  cases i with
  | zero => simp [shell, shellMass, B.volume]
  | succ i =>
    rw [shell, measureReal_sdiff (B.mono (by omega)) (B.measurable _)
      (B.ball_measure_ne_top hQ _), B.volume, B.volume]
    rw [zpow_add₀ (ne_of_gt hQ), zpow_add₀ (ne_of_gt hQ)]
    simp only [zpow_natCast, shellMass]
    ring

theorem shell_disjoint (k : ℤ) {i r : ℕ} (hir : i ≠ r) :
    Disjoint (B.shell k i) (B.shell k r) := by
  wlog h : i < r generalizing i r
  · exact (this hir.symm (by omega)).symm
  cases r with
  | zero => omega
  | succ r =>
    apply Set.disjoint_left.mpr
    intro x hx hxr
    exact hxr.2 (B.mono (by omega : k + (i : ℤ) ≤ k + (r : ℤ))
      (B.shell_subset k i hx))

theorem mem_ball_add_period_iff {k a : ℤ} (hka : k ≤ a) {z : G}
    (hz : z ∈ B.ball k) (x : G) : x + z ∈ B.ball a ↔ x ∈ B.ball a := by
  constructor
  · intro hx
    have := (B.ball a).sub_mem hx (B.mono hka hz)
    simpa using this
  · intro hx
    exact (B.ball a).add_mem hx (B.mono hka hz)

/-- Adding a point of the base ball preserves every shell, however large its index. -/
theorem mem_shell_add_period_iff (k : ℤ) (i : ℕ) {z : G}
    (hz : z ∈ B.ball k) (x : G) : x + z ∈ B.shell k i ↔ x ∈ B.shell k i := by
  cases i with
  | zero => exact B.mem_ball_add_period_iff le_rfl hz x
  | succ i =>
    simp only [shell, Set.mem_sdiff, SetLike.mem_coe]
    rw [B.mem_ball_add_period_iff (show k ≤ k + (i + 1 : ℕ) by omega) hz,
      B.mem_ball_add_period_iff (show k ≤ k + (i : ℕ) by omega) hz]

def shellCell (k : ℕ) (ij : ℕ × ℕ) : Set (G × G) :=
  B.shell 0 ij.1 ×ˢ B.shell k ij.2

theorem shellCell_measurable (k : ℕ) (ij : ℕ × ℕ) :
    MeasurableSet (B.shellCell k ij) :=
  (B.shell_measurable _ _).prod (B.shell_measurable _ _)

theorem shellCell_volume [SFinite μ] (hQ : 0 < Q) (k : ℕ) (ij : ℕ × ℕ) :
    (μ.prod μ).real (B.shellCell k ij) =
      Q ^ k * shellMass Q ij.1 * shellMass Q ij.2 := by
  rw [shellCell, measureReal_prod_prod, B.shell_volume hQ, B.shell_volume hQ]
  simp only [zpow_zero, zpow_natCast]
  ring

theorem shellCell_measure_ne_top [SFinite μ] (hQ : 0 < Q) (k : ℕ) (ij : ℕ × ℕ) :
    (μ.prod μ) (B.shellCell k ij) ≠ ∞ := by
  rw [shellCell, Measure.prod_prod]
  exact ENNReal.mul_ne_top (B.shell_measure_ne_top hQ _ _) (B.shell_measure_ne_top hQ _ _)

theorem shellCell_disjoint (k : ℕ) {ij rt : ℕ × ℕ} (h : ij ≠ rt) :
    Disjoint (B.shellCell k ij) (B.shellCell k rt) := by
  by_cases hi : ij.1 = rt.1
  · have hj : ij.2 ≠ rt.2 := by exact fun hj => h (Prod.ext hi hj)
    exact Set.disjoint_prod.mpr (Or.inr (B.shell_disjoint k hj))
  · exact Set.disjoint_prod.mpr (Or.inl (B.shell_disjoint 0 hi))

/-- A finite weighted shell profile as an actual function on the additive local plane. -/
def shellProfile (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) : G × G → ℝ :=
  fun x => ∑ ij ∈ I, (B.shellCell k ij).indicator (fun _ => w ij) x

/-- The fixed period is `B₀ × Bₖ`, independent of support and weights. -/
theorem shellProfile_period (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    {z : G × G} (hz : z ∈ (B.ball 0 : Set G) ×ˢ (B.ball k : Set G)) (x : G × G) :
    B.shellProfile k I w (x + z) = B.shellProfile k I w x := by
  classical
  apply Finset.sum_congr rfl
  intro ij hij
  simp only [shellCell, Set.indicator, Set.mem_prod, Prod.fst_add, Prod.snd_add,
    B.mem_shell_add_period_iff _ _ hz.1, B.mem_shell_add_period_iff _ _ hz.2]

theorem shellProfile_period_volume [SFinite μ] (k : ℕ) :
    (μ.prod μ).real ((B.ball 0 : Set G) ×ˢ (B.ball k : Set G)) = Q ^ k := by
  simp [measureReal_prod_prod, B.volume]

/-- On its cell the finite weighted profile has exactly the prescribed value. -/
theorem shellProfile_eq_weight (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    {ij : ℕ × ℕ} (hij : ij ∈ I) {x : G × G} (hx : x ∈ B.shellCell k ij) :
    B.shellProfile k I w x = w ij := by
  classical
  rw [shellProfile, Finset.sum_eq_single ij]
  · simp [hx]
  · intro rt hrt hne
    have hnot : x ∉ B.shellCell k rt :=
      fun hxr => Set.disjoint_left.mp (B.shellCell_disjoint k hne) hxr hx
    simp [hnot]
  · exact fun h => False.elim (h hij)

theorem shellProfile_eq_zero (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    {x : G × G} (hx : ∀ ij ∈ I, x ∉ B.shellCell k ij) :
    B.shellProfile k I w x = 0 := by
  apply Finset.sum_eq_zero
  intro ij hij
  simp [hx ij hij]

/-- Powers distribute over this disjoint shell decomposition, including zero
weights. The nonzero exponent is needed at points outside the finite support. -/
theorem shellProfile_rpow (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    {p : ℝ} (hp : p ≠ 0) (x : G × G) :
    B.shellProfile k I w x ^ p = B.shellProfile k I (fun ij => w ij ^ p) x := by
  classical
  by_cases hx : ∃ ij ∈ I, x ∈ B.shellCell k ij
  · obtain ⟨ij, hij, hx⟩ := hx
    rw [B.shellProfile_eq_weight k I w hij hx,
      B.shellProfile_eq_weight k I (fun ij => w ij ^ p) hij hx]
  · push Not at hx
    rw [B.shellProfile_eq_zero k I w hx,
      B.shellProfile_eq_zero k I (fun ij => w ij ^ p) hx, Real.zero_rpow hp]

/-- Exact weighted local `A(g)` integral. -/
theorem shellProfile_moment [SFinite μ] (hQ : 0 < Q)
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) {p : ℝ} (hp : p ≠ 0) :
    (∫ x, B.shellProfile k I w x ^ p ∂μ.prod μ) =
      Q ^ k * ∑ ij ∈ I, shellMass Q ij.1 * shellMass Q ij.2 * w ij ^ p := by
  simp_rw [B.shellProfile_rpow k I w hp]
  unfold shellProfile
  rw [integral_finsetSum]
  · simp_rw [integral_indicator_const _ (B.shellCell_measurable k _),
      smul_eq_mul, B.shellCell_volume hQ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    ring
  · intro ij hij
    exact (integrable_indicator_iff (B.shellCell_measurable k ij)).mpr
      (integrableOn_const (B.shellCell_measure_ne_top hQ k ij))

end UnitDistance.Local.BallSystem
