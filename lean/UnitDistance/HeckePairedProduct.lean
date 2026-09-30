module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Monotonicity from a paired zero product

A centered zero `z` contributes `|1-t²/z²|` to the absolute value of
the paired canonical product. When `|Re z| ≤ a`, this factor is
nondecreasing for real `t ≥ a ≥ 0`. Finite products preserve the inequality,
and so do their actual limits. This proves the monotonicity step without
differentiating an infinite product.

The existence and identification of the canonical product of a particular
Hecke function is a separate analytic theorem, not assumed as an axiom here.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace UnitDistance.HeckeAnalysis

/-- Absolute value of the quadratic factor paired at `z` and `-z`, written
as a quotient of norms. The zeros in a canonical product are nonzero. -/
def pairedFactor (z : ℂ) (t : ℝ) : ℝ :=
  ‖(t : ℂ)^2-z^2‖ / ‖z^2‖

theorem pairedFactor_nonneg (z : ℂ) (t : ℝ) : 0 ≤ pairedFactor z t :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

theorem pairedFactor_eq_norm {z : ℂ} (hz : z ≠ 0) (t : ℝ) :
    pairedFactor z t = ‖1-((t : ℂ)/z)^2‖ := by
  unfold pairedFactor
  rw [norm_sub_rev, ← norm_div]
  congr 1
  field_simp

/-- The elementary strip estimate underlying the Hecke monotonicity lemma. -/
theorem norm_centered_quadratic_le {z : ℂ} {a s t : ℝ} (ha : 0 ≤ a)
    (hz : |z.re| ≤ a) (hs : a ≤ s) (hst : s ≤ t) :
    ‖(s : ℂ)^2-z^2‖ ≤ ‖(t : ℂ)^2-z^2‖ := by
  have hs0 : 0 ≤ s := ha.trans hs
  have ht0 : 0 ≤ t := hs0.trans hst
  have hrs : z.re^2 ≤ s^2 := by
    have h1 : 0 ≤ s-z.re := by linarith [(abs_le.mp hz).2]
    have h2 : 0 ≤ s+z.re := by linarith [(abs_le.mp hz).1]
    nlinarith [mul_nonneg h1 h2]
  have hst2 : s^2 ≤ t^2 := by nlinarith
  have hq0 : 0 ≤ s^2-z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hq : (s^2-z.re^2+z.im^2)^2 ≤ (t^2-z.re^2+z.im^2)^2 := by
    nlinarith [sq_nonneg (t^2-s^2)]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero]
  nlinarith only [hq]

theorem pairedFactor_mono {z : ℂ} {a s t : ℝ} (ha : 0 ≤ a)
    (hz : |z.re| ≤ a) (hs : a ≤ s) (hst : s ≤ t) :
    pairedFactor z s ≤ pairedFactor z t := by
  exact div_le_div_of_nonneg_right (norm_centered_quadratic_le ha hz hs hst) (norm_nonneg _)

/-- A finite paired product, including the possible zero at the center. -/
def pairedPartialProduct {ι : Type*} (z : ι → ℂ) (m : ℕ) (A : ℝ)
    (J : Finset ι) (t : ℝ) : ℝ := A*t^m*∏ i ∈ J, pairedFactor (z i) t

theorem pairedPartialProduct_mono {ι : Type*} (z : ι → ℂ) (m : ℕ)
    {a A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hz : ∀ i, |(z i).re| ≤ a)
    (J : Finset ι) : MonotoneOn (pairedPartialProduct z m A J) (Set.Ici a) := by
  intro s hs t ht hst
  have hs0 := ha.trans hs
  unfold pairedPartialProduct
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hst m) hA
  · exact Finset.prod_le_prod₀ (fun i _ => pairedFactor_nonneg (z i) s)
      (fun i _ => pairedFactor_mono ha (hz i) hs hst)
  · exact Finset.prod_nonneg fun i _ => pairedFactor_nonneg (z i) s
  · exact mul_nonneg hA (pow_nonneg (ha.trans ht) m)

/-- Actual limits of paired products are nondecreasing on the real ray beyond
the zero strip. The convergence and identification premises are the precise
canonical-product obligation for an application to a completed Hecke function. -/
theorem monotoneOn_of_paired_product {ι : Type*} (z : ι → ℂ) (m : ℕ)
    {a A : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hz : ∀ i, |(z i).re| ≤ a)
    (f : ℝ → ℝ)
    (hlim : ∀ t ∈ Set.Ici a, Tendsto (fun J : Finset ι => pairedPartialProduct z m A J t)
      atTop (𝓝 (f t))) : MonotoneOn f (Set.Ici a) := by
  intro s hs t ht hst
  exact le_of_tendsto_of_tendsto (hlim s hs) (hlim t ht)
    (Filter.Eventually.of_forall fun J => pairedPartialProduct_mono z m ha hA hz J hs ht hst)

end UnitDistance.HeckeAnalysis
