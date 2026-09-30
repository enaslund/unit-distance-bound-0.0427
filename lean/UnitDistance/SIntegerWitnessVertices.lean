module

public import UnitDistance.SIntegerWitnessWindow
public import UnitDistance.SIntegerPlaneProjection
public import UnitDistance.GeometryFinite

@[expose] public section
set_option backward.privateInPublic true


/-! # Genuine finite S-integer vertex sets for every witness transformation -/

noncomputable section
open Set MeasureTheory NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]
  {S : Type*} [Fintype S] {ι : K ≃ₐ[F] K}

local instance verticesLocalMeasurableSpace (P : S × Bool → HeightOneSpectrum (𝓞 K)) (t : S × Bool) :
    MeasurableSpace ((P t).adicCompletion K) := borel ((P t).adicCompletion K)
local instance verticesLocalBorelSpace (P : S × Bool → HeightOneSpectrum (𝓞 K)) (t : S × Bool) :
    BorelSpace ((P t).adicCompletion K) := ⟨rfl⟩

def witnessDeformation (hι : ι ≠ 1) (D : PrimePairFamily ι S) (h : PairPlaceIndex F → ℝ) :
    (EuclideanIdeal.Space K × LocalProduct D.prime) ≃ₜ (EuclideanIdeal.Space K × LocalProduct D.prime) :=
  (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)).toHomeomorph.prodCongr
    (Homeomorph.refl _)

theorem witnessDeformation_measurePreserving (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (h : PairPlaceIndex F → ℝ) :
    MeasurePreserving (witnessDeformation hι D h) (semiLocalHaar D.prime) (semiLocalHaar D.prime) :=
  (EuclideanIdeal.deformation_measurePreserving K (reciprocalLogScale ι hι h)
    (sum_reciprocalLogScale ι hι h)).prod (MeasurePreserving.id (localProductHaar D.prime))

def witnessDeformedWindow (hι : ι ≠ 1) (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (T : ℝ) (h : PairPlaceIndex F → ℝ) :
    Set (EuclideanIdeal.Space K × LocalProduct D.prime) :=
  witnessDeformation hι D h ⁻¹' witnessSAdicWindow hι D v n₀ T

theorem witnessDeformedWindow_compact (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11) (n₀ : S → ℤ) (T : ℝ) (h : PairPlaceIndex F → ℝ) :
    IsCompact (witnessDeformedWindow hι D v n₀ T h) :=
  (witnessDeformation hι D h).isCompact_preimage.mpr (witnessSAdicWindow_compact hι D v n₀ T)

theorem witnessDeformedWindow_volume (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11) (n₀ : S → ℤ) (T : ℝ) (h : PairPlaceIndex F → ℝ) :
    semiLocalHaar D.prime (witnessDeformedWindow hι D v n₀ T h) =
      semiLocalHaar D.prime (witnessSAdicWindow hι D v n₀ T) :=
  (witnessDeformation_measurePreserving hι D h).measure_preimage
    (measurableSet_supportedWindow (witnessSAdicSupport_measurable D v n₀)
      (witnessSAdicEnergy_continuous hι D v n₀).measurable T).nullMeasurableSet

theorem diagonalSIntegers_closed (D : PrimePairFamily ι S) :
    IsClosed (diagonalSIntegers D.prime : Set (EuclideanIdeal.Space K × LocalProduct D.prime)) := by
  letI := diagonalSIntegers_discreteTopology D.prime (primePair_injective D)
  exact AddSubgroup.isClosed_of_discrete

/-- Actual diagonal S-integer points in the transformed common witness window. -/
def witnessDiagonalVertices (hι : ι ≠ 1) (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (T : ℝ) (h : PairPlaceIndex F → ℝ)
    (r : EuclideanIdeal.Space K × LocalProduct D.prime) : Finset (diagonalSIntegers D.prime) := by
  letI := diagonalSIntegers_discreteTopology D.prime (primePair_injective D)
  exact compactLatticeWindow (diagonalSIntegers D.prime) (diagonalSIntegers_closed D)
    (witnessDeformedWindow hι D v n₀ T h) (witnessDeformedWindow_compact hι D v n₀ T h) r

@[simp] theorem mem_witnessDiagonalVertices (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11) (n₀ : S → ℤ) (T : ℝ) (h : PairPlaceIndex F → ℝ)
    (r : EuclideanIdeal.Space K × LocalProduct D.prime) (x : diagonalSIntegers D.prime) :
    x ∈ witnessDiagonalVertices hι D v n₀ T h r ↔
      x.val+r ∈ witnessDeformedWindow hι D v n₀ T h := by
  letI := diagonalSIntegers_discreteTopology D.prime (primePair_injective D)
  exact mem_compactLatticeWindow _ _ _ _ _ _

/-- The same finite vertex set, as actual field S-integers. -/
def witnessSIntegerVertices (hι : ι ≠ 1) (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (T : ℝ) (h : PairPlaceIndex F → ℝ)
    (r : EuclideanIdeal.Space K × LocalProduct D.prime) : Finset ((Set.range D.prime).integer K) :=
  (witnessDiagonalVertices hι D v n₀ T h r).map (diagonalEmbeddingEquiv D.prime).symm.toEmbedding

@[simp] theorem mem_witnessSIntegerVertices (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11) (n₀ : S → ℤ) (T : ℝ) (h : PairPlaceIndex F → ℝ)
    (r : EuclideanIdeal.Space K × LocalProduct D.prime) (x : (Set.range D.prime).integer K) :
    x ∈ witnessSIntegerVertices hι D v n₀ T h r ↔
      (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
        (EuclideanIdeal.embedding K x.val+r.1), localEmbedding D.prime x.val+r.2) ∈
        witnessSAdicWindow hι D v n₀ T := by
  simp only [witnessSIntegerVertices, Finset.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    subst x
    have hm := (mem_witnessDiagonalVertices hι D v n₀ T h r y).mp hy
    have he := congrArg Subtype.val ((diagonalEmbeddingEquiv D.prime).apply_symm_apply y)
    change diagonalEmbedding D.prime ((diagonalEmbeddingEquiv D.prime).symm y) = y.val at he
    change witnessDeformation hι D h (y.val+r) ∈ witnessSAdicWindow hι D v n₀ T at hm
    rw [← he] at hm
    exact hm
  · intro hx
    refine ⟨diagonalEmbeddingEquiv D.prime x, ?_, (diagonalEmbeddingEquiv D.prime).symm_apply_apply x⟩
    exact (mem_witnessDiagonalVertices hι D v n₀ T h r _).mpr hx

/-- Uniform point count for the complete actual lattice intersection. -/
theorem witnessSIntegerVertices_card_le (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ)
    (hgap : Real.log 2+2*Real.log 5+2 ≤
      EuclideanIdeal.dualScale K (periodIdeal D.prime (witnessPeriodExponent v n₀)))
    (T : ℝ) (h : PairPlaceIndex F → ℝ) (r : EuclideanIdeal.Space K × LocalProduct D.prime) :
    ((witnessSIntegerVertices hι D v n₀ T h r).card : ℝ) ≤
      2*(Witness.compactMass^nrRealPlaces F*Witness.pairMass^nrComplexPlaces F)*
        Witness.tensorFiniteMass v*Real.exp (Witness.p*T) /
          ((2⁻¹ : ℝ)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|) := by
  apply witnessSAdic_card_le hι D v hQ n₀ hgap h r.1 r.2 T
  intro x hx
  simpa only [add_comm r.1] using (mem_witnessSIntegerVertices hι D v n₀ T h r x).mp hx

/-- The original Poisson bound applies directly to the exponential energy
sum over the entire actual diagonal lattice intersection. -/
theorem witnessDiagonalVertices_weight_sum_le (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ)
    (hgap : Real.log 2+2*Real.log 5+2 ≤
      EuclideanIdeal.dualScale K (periodIdeal D.prime (witnessPeriodExponent v n₀)))
    (T : ℝ) (h : PairPlaceIndex F → ℝ) (r : EuclideanIdeal.Space K × LocalProduct D.prime) :
    (∑ l ∈ witnessDiagonalVertices hι D v n₀ T h r,
      Real.exp (-Witness.p*witnessSAdicEnergy hι D v n₀ (witnessDeformation hι D h (l.val+r)))) ≤
      2*(Witness.compactMass^nrRealPlaces F*Witness.pairMass^nrComplexPlaces F)*
        Witness.tensorFiniteMass v / ((2⁻¹ : ℝ)^nrComplexPlaces K*Real.sqrt |(discr K : ℝ)|) := by
  have hw := witnessSAdic_weight_sum_le hι D v hQ n₀ hgap h r.1 r.2
    (witnessSIntegerVertices hι D v n₀ T h r)
  rw [witnessSIntegerVertices, Finset.sum_map] at hw
  refine le_trans (le_of_eq ?_) hw
  apply Finset.sum_congr rfl
  intro l hl
  have hx := (mem_witnessDiagonalVertices hι D v n₀ T h r l).mp hl
  rw [witnessSAdicEnergy_weight hι D v n₀ hx.1]
  have he := congrArg Subtype.val ((diagonalEmbeddingEquiv D.prime).apply_symm_apply l)
  change diagonalEmbedding D.prime ((diagonalEmbeddingEquiv D.prime).symm l) = l.val at he
  rw [← he]
  change relativeProfile ι hι
      (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
        (EuclideanIdeal.embedding K ((diagonalEmbeddingEquiv D.prime).symm l).val+r.1)) * _ = _
  rw [add_comm (EuclideanIdeal.embedding K ((diagonalEmbeddingEquiv D.prime).symm l).val) r.1]
  rfl

end UnitDistance.SIntegerCRT
