module

public import UnitDistance.SIntegerReferenceRescaling
public import UnitDistance.TensorMixedCoordinates

@[expose] public section
set_option backward.privateInPublic true


/-! # Exact actual-field coordinates for the common mixed overlap window -/

noncomputable section
set_option synthInstance.maxSize 512
open Set MeasureTheory NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeUnits Local.ValuedHaar Witness

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]
  {S : Type*} [Fintype S] {ι : K ≃ₐ[F] K}

local instance mixedLocalMeasurableSpace (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel (v.adicCompletion K)
local instance mixedLocalBorelSpace (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

abbrev WitnessLocalType (D : PrimePairFamily ι S) (s : S) :=
  (D.prime (s, false)).adicCompletion K

abbrev witnessPairHaar (D : PrimePairFamily ι S) (s : S) : Measure (WitnessLocalType D s) :=
  normalizedHaar (WitnessLocalType D s)

abbrev WitnessMixedPosition (D : PrimePairFamily ι S) :=
  MixedPositionCoordinates (RealPlaceIndex F) (PairPlaceIndex F) (WitnessLocalType D)

/-- The actual relative archimedean grouping and the actual completed
involution give one additive equivalence to the mixed position space. -/
def witnessMixedCoordinates (hι : ι ≠ 1) (D : PrimePairFamily ι S) :
    (EuclideanIdeal.Space K × LocalProduct D.prime) ≃+ WitnessMixedPosition D :=
  (EuclideanIdeal.tensorCoordinates K (relativePlaceGrouping ι hι)).toAddEquiv.prodCongr
    (pairedCoordinates D)

def witnessMixedCoordinatesHomeomorph (hι : ι ≠ 1) (D : PrimePairFamily ι S) :
    (EuclideanIdeal.Space K × LocalProduct D.prime) ≃ₜ WitnessMixedPosition D :=
  (EuclideanIdeal.tensorCoordinates K (relativePlaceGrouping ι hι)).toHomeomorph.prodCongr
    (pairedCoordinatesHomeomorph D)

theorem witnessMixedCoordinates_measurePreserving (hι : ι ≠ 1) (D : PrimePairFamily ι S) :
    MeasurePreserving (witnessMixedCoordinates hι D) (semiLocalHaar D.prime)
      (mixedPositionMeasure (β := RealPlaceIndex F) (γ := PairPlaceIndex F) (witnessPairHaar D)) :=
  (EuclideanIdeal.tensorCoordinates_measurePreserving K (relativePlaceGrouping ι hι)).prod
    (pairedCoordinates_measurePreserving D)

theorem witnessMixedCoordinates_support (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (x : EuclideanIdeal.Space K × LocalProduct D.prime) :
    witnessMixedCoordinates hι D x ∈ mixedPositionSupport v (witnessPairHaar D)
        (witnessPairBallSystem D v hQ) ↔ x ∈ witnessSAdicSupport D v 0 := by
  change tensorFiniteProfile v (witnessPairHaar D) (witnessPairBallSystem D v hQ)
      (pairedCoordinates D x.2) ≠ 0 ↔ True ∧ witnessFiniteProfile D v 0 x.2 ≠ 0
  rw [witnessFiniteProfile_pairedCoordinates D v hQ]
  simp

/-- On its literal support, the finite negative logarithm is the sum of
the actual local shell energies used in the independent endpoint law. -/
theorem witnessMixedCoordinates_energy (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    {x : EuclideanIdeal.Space K × LocalProduct D.prime}
    (hx : x ∈ witnessSAdicSupport D v 0) :
    mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)
      (witnessMixedCoordinates hι D x) = witnessSAdicEnergy hι D v 0 x := by
  have hn : tensorFiniteProfile v (witnessPairHaar D) (witnessPairBallSystem D v hQ)
      (pairedCoordinates D x.2) ≠ 0 := by
    rw [witnessFiniteProfile_pairedCoordinates D v hQ]
    exact hx.2
  have ht := Finset.prod_ne_zero_iff.mp hn
  change relativeEnergy ι hι x.1 + ∑ s, -Real.log
      (localShellProfile (v s) (witnessPairBallSystem D v hQ s) (pairedCoordinates D x.2 s)) =
    relativeEnergy ι hι x.1 + -Real.log (witnessFiniteProfile D v 0 x.2)
  rw [← witnessFiniteProfile_pairedCoordinates D v hQ, tensorFiniteProfile,
    Real.log_prod ht, Finset.sum_neg_distrib]

/-- The same common supported sum-energy window occurs in the arithmetic
geometry and in the mixed overlap concentration theorem. -/
theorem witnessMixedCoordinates_window (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (T : ℝ) :
    witnessMixedCoordinates hι D ⁻¹'
      supportedWindow (mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
        (mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T =
      witnessSAdicWindow hι D v 0 T := by
  ext x
  change (_ ∧ _ ≤ T) ↔ (x ∈ witnessSAdicSupport D v 0 ∧ _ ≤ T)
  rw [witnessMixedCoordinates_support hι D v hQ x]
  apply and_congr_right
  intro hx
  rw [witnessMixedCoordinates_energy hι D v hQ hx]

theorem witnessMixedCoordinates_overlap (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = residueCard (v s))
    (T : ℝ) (δ : EuclideanIdeal.Space K × LocalProduct D.prime) :
    semiLocalHaar D.prime (overlapSet (witnessSAdicWindow hι D v 0 T) δ) =
      mixedPositionMeasure (witnessPairHaar D)
        (overlapSet
          (supportedWindow (mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
            (mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T)
          (witnessMixedCoordinates hι D δ)) := by
  let W := supportedWindow
    (mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
    (mixedPositionEnergy (β := RealPlaceIndex F) (γ := PairPlaceIndex F)
      v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T
  have hW : MeasurableSet W := measurableSet_supportedWindow
    (measurableSet_mixedPositionSupport v (witnessPairHaar D) (witnessPairBallSystem D v hQ))
    (measurable_mixedPositionEnergy v (witnessPairHaar D) (witnessPairBallSystem D v hQ)) T
  have hpre : witnessMixedCoordinates hι D ⁻¹' overlapSet W (witnessMixedCoordinates hι D δ) =
      overlapSet (witnessSAdicWindow hι D v 0 T) δ := by
    rw [← witnessMixedCoordinates_window hι D v hQ T]
    ext x
    change (_ ∧ witnessMixedCoordinates hι D x+witnessMixedCoordinates hι D δ ∈ W) ↔
      (_ ∧ witnessMixedCoordinates hι D (x+δ) ∈ W)
    rw [map_add]
    rfl
  rw [← hpre]
  exact (witnessMixedCoordinates_measurePreserving hι D).measure_preimage
    (hW.inter (hW.preimage ((continuous_id.add continuous_const).measurable))).nullMeasurableSet

end UnitDistance.SIntegerCRT
