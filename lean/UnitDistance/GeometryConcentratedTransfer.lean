module

public import UnitDistance.GeometryEnergy

@[expose] public section
set_option backward.privateInPublic true


/-! # Geometric transfer from a proved concentration estimate

This form consumes a concentration estimate already proved in other
measure-preserving coordinates. It uses the same ordinary geometric model
and proves the exact cancellation of the common threshold.
-/

noncomputable section
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace UnitDistance

variable {G H X Labels Torsion C : Type*}
  [AddGroup G] [Countable G] [Fintype Torsion]
  [Fintype Labels] [Fintype C] [Nonempty C] [DecidableEq C]
  [AddGroup H] [MeasurableSpace H] [MeasurableAdd₂ H] [MeasurableNeg H]
  [AddAction G H] [MeasurableConstVAdd G H]
  [AddCommGroup X] [MeasurableSpace X] [MeasurableAdd₂ X]

theorem WeightedWindowModel.concentrated_transfer
    (ν : Measure H) [VAddInvariantMeasure G H ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (Q : Set H) (hQ : IsAddFundamentalDomain G Q ν) (hQfin : ν Q < ⊤) (hQ0 : ν Q ≠ 0)
    (L : AddSubgroup X) [Countable L]
    (μ : Measure X) [VAddInvariantMeasure L X μ]
    (P : Set X) (hP : IsAddFundamentalDomain L P μ) (hPfin : μ P < ⊤)
    (baseWindow : Set X) (Φ : Labels → H → ℝ≥0∞)
    (A D p δ Z ε d mean : ℝ)
    (model : WeightedWindowModel (G := G) (Torsion := Torsion) (C := C)
      Q L μ baseWindow Φ (mean+ε*d))
    (hbase0 : μ baseWindow ≠ 0) (hbasefin : μ baseWindow ≠ ⊤)
    (hΦ : ∀ i, Measurable (Φ i)) (hΦfin : ∀ i, (∫⁻ u, Φ i u ∂ν) ≠ ⊤)
    (hA : 0 < A) (hD : 0 < D) (hZ : 0 < Z) (hp : 0 ≤ p) (hδ : 0 ≤ δ)
    (hpδ : p*(1+δ) = 2)
    (hOverlap : (1/2:ℝ)*Z*Real.exp (2*(mean-ε*d)) ≤
      ∑ i : Labels, (∫⁻ u, Φ i u ∂ν).toReal)
    (hVolume : (μ baseWindow).toReal ≤ A*Real.exp (p*(mean+ε*d)))
    (hweighted : ∀ i₀ h r,
      ∑ l ∈ model.vertices i₀ (h,r),
        Real.exp (-p*model.energy i₀ h ((l : X)+r)) ≤ 2*A/D) :
    ∃ U : Finset ℂ, 0 < U.card ∧ (U.card : ℝ) ≤ 2*A*Real.exp (p*(mean+ε*d))/D ∧
      ((Fintype.card Torsion : ℝ)/((Fintype.card C : ℝ)*(ν Q).toReal))*
        D^δ/(2:ℝ)^(2+δ)*(Z/A^(1+δ))*Real.exp (-4*(ε*d)) ≤
        unitPairs U/(U.card : ℝ)^(1+δ) := by
  obtain ⟨U, hU0, hUB, hratio⟩ := model.energy_transfer ν Q hQ hQfin hQ0
    L μ P hP hPfin baseWindow Φ (mean+ε*d) hbase0 hbasefin hΦ hΦfin
    A D p δ ((1/2)*Z*Real.exp (2*(mean-ε*d))) hA hD hp hδ
    (by positivity) hOverlap hVolume hweighted
  refine ⟨U, hU0, hUB, ?_⟩
  rw [← weighted_ratio_identity
    ((Fintype.card Torsion : ℝ)/((Fintype.card C : ℝ)*(ν Q).toReal))
    Z A D p δ mean (ε*d) hA hD hpδ]
  convert hratio using 1
  ring

end UnitDistance
