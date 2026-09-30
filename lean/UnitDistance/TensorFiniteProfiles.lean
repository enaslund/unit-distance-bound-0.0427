module

public import UnitDistance.WitnessLocalFunctional
public import UnitDistance.LocalRegularity
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual finite tensor witness profiles

The finite profile is the literal product of the published local shell
profiles. Its p-power is integrable with exactly the displayed product
mass, and its fixed additive period is independent of the shell support.
-/

noncomputable section
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace UnitDistance

namespace Local.BallSystem
variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
  {μ : Measure G} [SFinite μ] {Q : ℝ} (B : BallSystem G μ Q)

theorem shellProfile_integrable (hQ : 0 < Q) (k : ℕ)
    (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    Integrable (B.shellProfile k I w) (μ.prod μ) := by
  unfold shellProfile
  exact integrable_finsetSum _ (fun ij _ =>
    (integrable_indicator_iff (B.shellCell_measurable k ij)).mpr
      (integrableOn_const (B.shellCell_measure_ne_top hQ k ij)))

theorem shellProfile_rpow_integrable (hQ : 0 < Q) (k : ℕ)
    (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) {q : ℝ} (hq : q ≠ 0) :
    Integrable (fun x => B.shellProfile k I w x^q) (μ.prod μ) := by
  simp_rw [B.shellProfile_rpow k I w hq]
  exact B.shellProfile_integrable hQ k I _

end Local.BallSystem

namespace Witness

section LocalProfile
variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
  {μ : Measure G} (v : Fin 11) (B : Local.BallSystem G μ (residueCard v))

theorem localShellProfile_nonneg (x : G × G) : 0 ≤ localShellProfile v B x :=
  B.shellProfile_nonneg _ _ _ (fun ij _ =>
    mul_nonneg (shellWeightNat_nonneg v ij.1) (shellWeightNat_nonneg v ij.2)) x

theorem localShellProfile_measurable : Measurable (localShellProfile v B) :=
  B.shellProfile_measurable _ _ _

theorem localShellProfile_rpow_integrable [SFinite μ] :
    Integrable (fun x => localShellProfile v B x^p) (μ.prod μ) :=
  B.shellProfile_rpow_integrable (zero_lt_one.trans (residueCard_gt_one v)) _ _ _
    witness_basic.2.2.1.ne'

theorem localShellProfile_period {z : G × G}
    (hz : z ∈ (B.ball 0 : Set G) ×ˢ (B.ball (periodPower v) : Set G)) (x : G × G) :
    localShellProfile v B (x+z) = localShellProfile v B x :=
  B.shellProfile_period _ _ _ hz x

theorem localShellProfile_invariant (φ ψ : G → G)
    (hφ : ∀ a x, φ x ∈ B.ball a ↔ x ∈ B.ball a)
    (hψ : ∀ a x, ψ x ∈ B.ball a ↔ x ∈ B.ball a) (x : G × G) :
    localShellProfile v B (φ x.1, ψ x.2) = localShellProfile v B x :=
  B.shellProfile_invariant φ ψ hφ hψ _ _ _ x

end LocalProfile

variable {ι : Type*} [Fintype ι] {G : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, MeasurableSpace (G i)]
  (v : ι → Fin 11) (μ : (i : ι) → Measure (G i))
  (B : (i : ι) → Local.BallSystem (G i) (μ i) (residueCard (v i)))

/-- The actual product of the finite local witness profiles. -/
def tensorFiniteProfile (x : (i : ι) → G i × G i) : ℝ :=
  ∏ i, localShellProfile (v i) (B i) (x i)

/-- The actual local p-weight used in the S-integer weighted count. -/
def tensorFiniteWeight (x : (i : ι) → G i × G i) : ℝ :=
  ∏ i, localShellProfile (v i) (B i) (x i)^p

/-- The product of the exact local p-masses. -/
def tensorFiniteMass : ℝ := ∏ i, residueCard (v i)^periodPower (v i)*finiteLp (v i)^2

theorem tensorFiniteMass_pos : 0 < tensorFiniteMass v := by
  unfold tensorFiniteMass
  exact Finset.prod_pos (fun i _ => mul_pos
    (pow_pos (zero_lt_one.trans (residueCard_gt_one (v i))) _)
    (pow_pos (finiteLp_pos (v i)) _))

theorem tensorFiniteProfile_nonneg (x : (i : ι) → G i × G i) :
    0 ≤ tensorFiniteProfile v μ B x :=
  Finset.prod_nonneg (fun i _ => localShellProfile_nonneg (v i) (B i) (x i))

theorem tensorFiniteWeight_nonneg (x : (i : ι) → G i × G i) :
    0 ≤ tensorFiniteWeight v μ B x :=
  Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (localShellProfile_nonneg (v i) (B i) (x i)) _)

/-- The literal product weight is exactly the p-power of the actual product profile. -/
theorem tensorFiniteWeight_eq_rpow (x : (i : ι) → G i × G i) :
    tensorFiniteWeight v μ B x = tensorFiniteProfile v μ B x^p :=
  Real.finsetProd_rpow Finset.univ (fun i => localShellProfile (v i) (B i) (x i))
    (fun i _ => localShellProfile_nonneg (v i) (B i) (x i)) p

theorem tensorFiniteProfile_measurable : Measurable (tensorFiniteProfile v μ B) := by
  unfold tensorFiniteProfile
  exact Finset.measurable_prod _ (fun i _ =>
    (localShellProfile_measurable (v i) (B i)).comp (measurable_pi_apply i))

theorem tensorFiniteWeight_measurable : Measurable (tensorFiniteWeight v μ B) := by
  change Measurable (fun x : (i : ι) → G i × G i => tensorFiniteWeight v μ B x)
  simp_rw [tensorFiniteWeight_eq_rpow]
  exact (tensorFiniteProfile_measurable v μ B).pow_const p

theorem tensorFiniteWeight_integrable [∀ i, SigmaFinite (μ i)] :
    Integrable (tensorFiniteWeight v μ B) (Measure.pi (fun i => (μ i).prod (μ i))) :=
  Integrable.fintype_prod_dep (fun i => localShellProfile_rpow_integrable (v i) (B i))

theorem tensorFiniteWeight_integral [∀ i, SigmaFinite (μ i)] :
    (∫ x, tensorFiniteWeight v μ B x ∂Measure.pi (fun i => (μ i).prod (μ i))) =
      tensorFiniteMass v := by
  change (∫ x, ∏ i, localShellProfile (v i) (B i) (x i)^p
    ∂Measure.pi (fun i => (μ i).prod (μ i))) = _
  simpa only [localShellProfile_moment, tensorFiniteMass] using
    (integral_fintype_prod_eq_prod (μ := fun i => (μ i).prod (μ i))
      (fun i x => localShellProfile (v i) (B i) x^p))

/-- The actual period consists of B₀ in each first coordinate and Bₖ in each second. -/
def tensorFinitePeriod : Set ((i : ι) → G i × G i) :=
  {z | ∀ i, z i ∈ ((B i).ball 0 : Set (G i)) ×ˢ ((B i).ball (periodPower (v i)) : Set (G i))}

theorem tensorFiniteProfile_period {z : (i : ι) → G i × G i}
    (hz : z ∈ tensorFinitePeriod v μ B) (x : (i : ι) → G i × G i) :
    tensorFiniteProfile v μ B (x+z) = tensorFiniteProfile v μ B x := by
  exact Finset.prod_congr rfl (fun i _ => localShellProfile_period (v i) (B i) (hz i) (x i))

theorem tensorFiniteWeight_period {z : (i : ι) → G i × G i}
    (hz : z ∈ tensorFinitePeriod v μ B) (x : (i : ι) → G i × G i) :
    tensorFiniteWeight v μ B (x+z) = tensorFiniteWeight v μ B x := by
  rw [tensorFiniteWeight_eq_rpow, tensorFiniteProfile_period v μ B hz, tensorFiniteWeight_eq_rpow]

/-- Coordinatewise ball-preserving phase or involution maps preserve the literal weight. -/
theorem tensorFiniteWeight_invariant (φ ψ : (i : ι) → G i → G i)
    (hφ : ∀ i a x, φ i x ∈ (B i).ball a ↔ x ∈ (B i).ball a)
    (hψ : ∀ i a x, ψ i x ∈ (B i).ball a ↔ x ∈ (B i).ball a)
    (x : (i : ι) → G i × G i) :
    tensorFiniteWeight v μ B (fun i => (φ i (x i).1, ψ i (x i).2)) = tensorFiniteWeight v μ B x := by
  apply Finset.prod_congr rfl
  intro i _
  rw [localShellProfile_invariant (v i) (B i) (φ i) (ψ i) (hφ i) (hψ i)]

end Witness
end UnitDistance
