module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section
set_option backward.privateInPublic true


/-!
# Full logarithmic lattice unfolding

This uses an arbitrary countable additive lattice action and its fundamental
domain. The lattice is not assumed to split into coordinate factors. All
measures are additive; no angular factor occurs. The finite type `Torsion`
records precisely the size of the kernel of the logarithmic unit map.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace UnitDistance

/-- Tonelli followed by fundamental-domain tiling. -/
theorem logarithmic_unfolding {L V : Type*} [AddGroup L] [Countable L]
    [MeasurableSpace V] [AddAction L V] [MeasurableConstVAdd L V]
    (μ : Measure V) [VAddInvariantMeasure L V μ]
    (P : Set V) (hP : IsAddFundamentalDomain L P μ)
    (Φ : V → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ h in P, ∑' l : L, Φ (l +ᵥ h) ∂μ) = ∫⁻ u, Φ u ∂μ := by
  calc
    _ = ∑' l : L, ∫⁻ h in P, Φ (l +ᵥ h) ∂μ :=
      lintegral_tsum (fun (l : L) => (hΦ.comp (measurable_const_vadd l)).aemeasurable)
    _ = ∫⁻ u, Φ u ∂μ := (hP.lintegral_eq_tsum'' Φ).symm

/-- Unfold a translated and reflected profile. This is the exact
`Φ(log β - h)` dependence of reciprocal deformation. -/
theorem logarithmic_unfolding_shifted {L V : Type*} [AddGroup L] [Countable L]
    [AddGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] [MeasurableNeg V]
    [AddAction L V] [MeasurableConstVAdd L V]
    (μ : Measure V) [VAddInvariantMeasure L V μ]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (P : Set V) (hP : IsAddFundamentalDomain L P μ)
    (Φ : V → ℝ≥0∞) (hΦ : Measurable Φ) (c : V) :
    (∫⁻ h in P, ∑' l : L, Φ (c - (l +ᵥ h)) ∂μ) = ∫⁻ u, Φ u ∂μ := by
  rw [logarithmic_unfolding μ P hP (fun u => Φ (c - u))
    (hΦ.comp (measurable_const.sub measurable_id))]
  exact lintegral_sub_left_eq_self Φ c

/-- Several weighted classes may have different profiles and different
logarithmic coset representatives. Every logarithmic lattice point has the
same finite torsion multiplicity. The formula does not impose any relation
between the representatives and local unit coordinates. -/
theorem logarithmic_unfolding_cosets {L V Labels Torsion : Type*}
    [AddGroup L] [Countable L] [Fintype Labels] [Fintype Torsion]
    [AddGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] [MeasurableNeg V]
    [AddAction L V] [MeasurableConstVAdd L V]
    (μ : Measure V) [VAddInvariantMeasure L V μ]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (P : Set V) (hP : IsAddFundamentalDomain L P μ)
    (Φ : Labels → V → ℝ≥0∞) (hΦ : ∀ i, Measurable (Φ i)) (c : Labels → V) :
    (∫⁻ h in P, ∑ i : Labels, ∑ _τ : Torsion, ∑' l : L,
      Φ i (c i - (l +ᵥ h)) ∂μ) =
      (Fintype.card Torsion : ℝ≥0∞) * ∑ i : Labels, ∫⁻ u, Φ i u ∂μ := by
  have hm (i : Labels) : Measurable (fun h => ∑' l : L, Φ i (c i - (l +ᵥ h))) :=
    Measurable.tsum (fun l =>
      (hΦ i).comp (measurable_const.sub (measurable_const_vadd l)))
  rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ (fun _ _ => hm i))]
  simp_rw [lintegral_finsetSum _ (fun _ _ => hm _),
    logarithmic_unfolding_shifted μ P hP _ (hΦ _) (c _)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact (Finset.mul_sum _ _ _).symm

end UnitDistance
