module

public import UnitDistance.LocalRegularity
public import UnitDistance.SupportedProfile
public import Mathlib.Probability.Moments.Variance

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual finite-shell energies and uniform endpoint moment bounds

The energy is the negative logarithm of the actual local shell profile.
Disjointness of the cells bounds it by a finite expression in the displayed
weights, including outside the support. Thus every normalized local overlap
law has finite endpoint second moments and a uniform variance bound.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
namespace UnitDistance.Local.BallSystem

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
  {μ : Measure G} {Q : ℝ} (B : BallSystem G μ Q)

def shellEnergy (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) (x : G × G) : ℝ :=
  -Real.log (B.shellProfile k I w x)

/-- A fixed finite bound depending only on the shell coefficients. -/
def shellEnergyBound (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) : ℝ :=
  ∑ ij ∈ I, |Real.log (w ij)|

theorem shellEnergyBound_nonneg (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    0 ≤ shellEnergyBound I w := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem shellEnergy_measurable (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    Measurable (B.shellEnergy k I w) :=
  (Real.measurable_log.comp (B.shellProfile_measurable k I w)).neg

/-- No positive-minimum hypothesis is needed: a finite disjoint shell
profile takes only zero and the finitely many displayed coefficient values. -/
theorem shellEnergy_norm_le (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (x : G × G) : ‖B.shellEnergy k I w x‖ ≤ shellEnergyBound I w := by
  by_cases hx : ∃ ij ∈ I, x ∈ B.shellCell k ij
  · obtain ⟨ij, hij, hx⟩ := hx
    rw [shellEnergy, B.shellProfile_eq_weight k I w hij hx, norm_neg, Real.norm_eq_abs]
    exact Finset.single_le_sum (s := I) (f := fun ij => |Real.log (w ij)|)
      (fun _ _ => abs_nonneg _) hij
  · push Not at hx
    rw [shellEnergy, B.shellProfile_eq_zero k I w hx, Real.log_zero, neg_zero, norm_zero]
    exact shellEnergyBound_nonneg I w

theorem shellEnergy_weight (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (hw : ∀ ij ∈ I, 0 ≤ w ij) (q : ℝ) {x : G × G}
    (hx : x ∈ Function.support (B.shellProfile k I w)) :
    Real.exp (-q*B.shellEnergy k I w x) = B.shellProfile k I w x^q := by
  have hp : 0 < B.shellProfile k I w x :=
    lt_of_le_of_ne (B.shellProfile_nonneg k I w hw x) (Ne.symm hx)
  rw [shellEnergy, Real.rpow_def_of_pos hp]
  congr 1
  ring

theorem shellEnergy_neg (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (x : G × G) : B.shellEnergy k I w (-x) = B.shellEnergy k I w x := by
  exact congrArg (fun t => -Real.log t)
    (B.shellProfile_invariant Neg.neg Neg.neg (by intros; simp) (by intros; simp) k I w x)

/-- Both endpoints are covered by any measurable map into the local plane.
The bound is independent of the displacement and the probability law. -/
theorem shellEnergy_comp_memLp {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsFiniteMeasure ν] (f : A → G × G) (hf : Measurable f)
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) (q : ℝ≥0∞) :
    MemLp (fun x => B.shellEnergy k I w (f x)) q ν :=
  MemLp.of_bound ((B.shellEnergy_measurable k I w).comp hf).aestronglyMeasurable
    (shellEnergyBound I w) (Filter.Eventually.of_forall (fun x => B.shellEnergy_norm_le k I w (f x)))

/-- A concrete variance bound for every normalized local endpoint law. -/
theorem shellEnergy_comp_variance_le {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (f : A → G × G) (hf : Measurable f)
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    variance (fun x => B.shellEnergy k I w (f x)) ν ≤ (shellEnergyBound I w)^2 := by
  have hb : ∀ᵐ x ∂ν, B.shellEnergy k I w (f x) ∈
      Set.Icc (-shellEnergyBound I w) (shellEnergyBound I w) :=
    Filter.Eventually.of_forall (fun x =>
      abs_le.mp (by simpa only [Real.norm_eq_abs] using B.shellEnergy_norm_le k I w (f x)))
  convert variance_le_sq_of_bounded hb ((B.shellEnergy_measurable k I w).comp hf).aemeasurable using 1
  congr 1
  ring

end UnitDistance.Local.BallSystem
