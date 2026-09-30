module

public import UnitDistance.TensorFourier
public import UnitDistance.EuclideanIdealSeparation

@[expose] public section
set_option backward.privateInPublic true


/-!
# Ordinary-volume singleton/pair coordinates for a totally complex field

An actual bijection of complex places specifies the singleton and pair blocks.
The induced continuous linear coordinates preserve ordinary Lebesgue measure
and the real Euclidean inner product. No mass or Fourier hypothesis occurs.
-/

noncomputable section
open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Classical BigOperators

namespace UnitDistance.EuclideanIdeal

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
variable {β γ : Type*} [Fintype β] [Fintype γ]

abbrev ComplexPlaces := {w : InfinitePlace K // w.IsComplex}

/-- Drop the empty real-place block; retain the actual complex embeddings. -/
def complexCoordinates : Space K ≃L[ℝ] (ComplexPlaces K → ℂ) := by
  letI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩
  exact (coordinates K).trans (ContinuousLinearEquiv.uniqueProd ℝ _ _)

@[simp] theorem complexCoordinates_apply (x : Space K) (w : ComplexPlaces K) :
    complexCoordinates K x w = (coordinates K x).2 w := rfl

theorem complexCoordinates_measurePreserving :
    MeasurePreserving (complexCoordinates K) volume volume := by
  letI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩
  letI : IsProbabilityMeasure (volume : Measure ({w : InfinitePlace K // w.IsReal} → ℝ)) :=
    ⟨by simp only [volume_pi, Measure.pi_empty_univ]⟩
  change MeasurePreserving (fun x : Space K => (coordinates K x).2) volume volume
  have hs : MeasurePreserving
      (Prod.snd : mixedEmbedding.mixedSpace K → (ComplexPlaces K → ℂ)) volume volume := by
    exact measurePreserving_snd
      (μ := (volume : Measure ({w : InfinitePlace K // w.IsReal} → ℝ)))
      (ν := (volume : Measure (ComplexPlaces K → ℂ)))
  exact hs.comp (mixedEmbedding.euclidean.volumePreserving_toMixed K)

/-- Pair the two copies of an index set pointwise. -/
def pairCoordinateEquiv : ((γ → ℂ) × (γ → ℂ)) ≃L[ℝ] (γ → ℂ × ℂ) :=
  ({ toFun := fun x j => (x.1 j, x.2 j)
     invFun := fun x => (fun j => (x j).1, fun j => (x j).2)
     left_inv := fun x => by rfl
     right_inv := fun x => by rfl
     map_add' := fun x y => by rfl
     map_smul' := fun c x => by rfl } :
    ((γ → ℂ) × (γ → ℂ)) ≃ₗ[ℝ] (γ → ℂ × ℂ)).toContinuousLinearEquiv

@[simp] theorem pairCoordinateEquiv_apply (x : (γ → ℂ) × (γ → ℂ)) (j : γ) :
    pairCoordinateEquiv x j = (x.1 j, x.2 j) := rfl

theorem pairCoordinateEquiv_measurePreserving :
    MeasurePreserving (pairCoordinateEquiv (γ := γ)) volume volume :=
  (volume_measurePreserving_arrowProdEquivProdArrow ℂ ℂ γ).symm _

/-- A designated grouping of complex places gives the literal singleton/pair
coordinates. The first copy of `γ` is the first entry of each pair. -/
def tensorCoordinates (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ)) :
    Space K ≃L[ℝ] Witness.TensorCoordinates β γ :=
  ((complexCoordinates K).trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : β ⊕ (γ ⊕ γ) => ℂ) g)).trans
    ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ β (γ ⊕ γ) (fun _ => ℂ)).trans
      ((ContinuousLinearEquiv.refl ℝ (β → ℂ)).prodCongr
        ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ γ γ (fun _ => ℂ)).trans pairCoordinateEquiv)))

omit [Fintype β] in
@[simp] theorem tensorCoordinates_singleton (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ))
    (x : Space K) (i : β) :
    (tensorCoordinates K g x).1 i = (coordinates K x).2 (g.symm (.inl i)) := by
  change Equiv.piCongrLeft (fun _ : β ⊕ (γ ⊕ γ) => ℂ) g
    (complexCoordinates K x) (.inl i) = _
  simp only [Equiv.piCongrLeft_apply_eq_cast, cast_eq, complexCoordinates_apply]

omit [Fintype β] in
@[simp] theorem tensorCoordinates_pair_fst (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ))
    (x : Space K) (j : γ) :
    ((tensorCoordinates K g x).2 j).1 = (coordinates K x).2 (g.symm (.inr (.inl j))) := by
  change Equiv.piCongrLeft (fun _ : β ⊕ (γ ⊕ γ) => ℂ) g
    (complexCoordinates K x) (.inr (.inl j)) = _
  simp only [Equiv.piCongrLeft_apply_eq_cast, cast_eq, complexCoordinates_apply]

omit [Fintype β] in
@[simp] theorem tensorCoordinates_pair_snd (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ))
    (x : Space K) (j : γ) :
    ((tensorCoordinates K g x).2 j).2 = (coordinates K x).2 (g.symm (.inr (.inr j))) := by
  change Equiv.piCongrLeft (fun _ : β ⊕ (γ ⊕ γ) => ℂ) g
    (complexCoordinates K x) (.inr (.inr j)) = _
  simp only [Equiv.piCongrLeft_apply_eq_cast, cast_eq, complexCoordinates_apply]

theorem tensorCoordinates_measurePreserving (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ)) :
    MeasurePreserving (tensorCoordinates K g) volume volume := by
  have h₁ := complexCoordinates_measurePreserving K
  have h₂ := volume_measurePreserving_piCongrLeft (fun _ : β ⊕ (γ ⊕ γ) => ℂ) g
  have h₃ := volume_measurePreserving_sumPiEquivProdPi (fun _ : β ⊕ (γ ⊕ γ) => ℂ)
  have h₄ := volume_measurePreserving_sumPiEquivProdPi (fun _ : γ ⊕ γ => ℂ)
  have h₅ := pairCoordinateEquiv_measurePreserving (γ := γ)
  exact ((MeasurePreserving.id volume).prod (h₅.comp h₄)).comp (h₃.comp (h₂.comp h₁))

theorem tensorCoordinates_inner (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ)) (x ξ : Space K) :
    inner ℝ x ξ = Witness.tensorInner (tensorCoordinates K g x) (tensorCoordinates K g ξ) := by
  letI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩
  rw [WithLp.prod_inner_apply, PiLp.inner_apply, Fintype.sum_empty, zero_add, PiLp.inner_apply]
  change (∑ w : ComplexPlaces K, inner ℝ ((coordinates K x).2 w)
    ((coordinates K ξ).2 w)) = _
  have hsum := g.symm.sum_comp (fun w : ComplexPlaces K =>
    inner ℝ ((coordinates K x).2 w) ((coordinates K ξ).2 w))
  simpa only [Fintype.sum_sum_type, Witness.tensorInner, tensorCoordinates_singleton,
    tensorCoordinates_pair_fst, tensorCoordinates_pair_snd, Finset.sum_add_distrib] using hsum.symm

theorem tensorCoordinates_norm (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ)) (ξ : Space K) :
    Witness.tensorCoordinateNorm (tensorCoordinates K g ξ) = coordinateNorm K ξ := by
  have hsum := g.symm.sum_comp (fun w : ComplexPlaces K => ‖(coordinates K ξ).2 w‖)
  simpa only [Fintype.sum_sum_type, Witness.tensorCoordinateNorm, coordinateNorm,
    tensorCoordinates_singleton, tensorCoordinates_pair_fst, tensorCoordinates_pair_snd,
    Finset.sum_add_distrib] using hsum

omit [IsTotallyComplex K] in
theorem tensorCoordinates_card (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ)) :
    Fintype.card β + 2*Fintype.card γ = nrComplexPlaces K := by
  have h := Fintype.card_congr g
  simp only [Fintype.card_sum] at h
  change _ = Fintype.card (ComplexPlaces K)
  omega

/-- The literal archimedean p-th-power profile on the field's Euclidean space. -/
def archimedeanProfile (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ)) : Space K → ℝ :=
  Witness.tensorProfile (tensorCoordinates K g)

theorem archimedeanProfile_pos (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ)) (x : Space K) :
    0 < archimedeanProfile K g x := Witness.tensorProfile_pos _ _

theorem temperateGrowth_archimedeanProfile (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ)) :
    (archimedeanProfile K g).HasTemperateGrowth := Witness.temperateGrowth_tensorProfile _

theorem integrable_archimedeanProfile (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ)) :
    Integrable (archimedeanProfile K g) :=
  Witness.integrable_tensorProfile _ (tensorCoordinates_measurePreserving K g)

theorem integral_archimedeanProfile (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ)) :
    (∫ x, archimedeanProfile K g x) =
      Witness.compactMass ^ Fintype.card β * Witness.pairMass ^ Fintype.card γ :=
  Witness.integral_tensorProfile _ (tensorCoordinates_measurePreserving K g)

theorem integral_archimedeanProfile_pos (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ)) :
    0 < ∫ x, archimedeanProfile K g x := by
  rw [integral_archimedeanProfile]
  positivity [Witness.compactMass_pos, Witness.pairMass_pos]

open FourierTransform in
/-- The actual global profile satisfies the original Fourier bound with
`M = 2` and `σ = 1`, for all dimensions and all singleton/pair groupings. -/
theorem archimedeanProfile_fourier_envelope (g : ComplexPlaces K ≃ β ⊕ (γ ⊕ γ)) (ξ : Space K) :
    ‖𝓕 (fun x => ((archimedeanProfile K g x:ℝ):ℂ)) ξ‖ ≤
      ((∫ x, archimedeanProfile K g x) * 2^nrComplexPlaces K) *
        Real.exp (-coordinateNorm K ξ) := by
  have h := Witness.tensorProfile_fourier_envelope (tensorCoordinates K g)
    (tensorCoordinates_measurePreserving K g) (tensorCoordinates_inner K g) ξ
  rwa [tensorCoordinates_norm K g, tensorCoordinates_card K g,
    ← integral_archimedeanProfile K g] at h

end UnitDistance.EuclideanIdeal
