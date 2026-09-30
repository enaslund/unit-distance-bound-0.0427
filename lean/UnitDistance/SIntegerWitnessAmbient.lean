module

public import UnitDistance.SIntegerPlaneProjection
public import Mathlib.LinearAlgebra.Countable

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual ambient lattice and fundamental-domain facts for the S-adic transfer -/

noncomputable section
set_option synthInstance.maxSize 512
open Set MeasureTheory NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped Classical ENNReal nonZeroDivisors

namespace UnitDistance.SIntegerCRT

variable {K : Type} [Field K] [NumberField K] {T : Type*} [Fintype T]

local instance ambientLocalMeasurableSpace (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel (v.adicCompletion K)
local instance ambientLocalBorelSpace (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

/-- Countability is inherited from the actual number field, not from a
separate enumeration assumption about the diagonal lattice. -/
instance diagonalSIntegers_countable (P : T → HeightOneSpectrum (𝓞 K)) :
    Countable (diagonalSIntegers P) := by
  letI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := K)
  exact (diagonalEmbeddingEquiv P).symm.injective.countable

theorem semiLocalHaar_isAddLeftInvariant (P : T → HeightOneSpectrum (𝓞 K)) :
    (semiLocalHaar P).IsAddLeftInvariant := by
  unfold semiLocalHaar localProductHaar
  infer_instance

theorem semiLocalHaar_isAddRightInvariant (P : T → HeightOneSpectrum (𝓞 K)) :
    (semiLocalHaar P).IsAddRightInvariant := by
  unfold semiLocalHaar localProductHaar
  infer_instance

theorem semiLocalHaar_isNegInvariant (P : T → HeightOneSpectrum (𝓞 K)) :
    (semiLocalHaar P).IsNegInvariant := by
  letI : (localProductHaar P).IsNegInvariant := by
    unfold localProductHaar
    infer_instance
  exact ⟨((Measure.measurePreserving_neg (volume : Measure (EuclideanIdeal.Space K))).prod
    (Measure.measurePreserving_neg (localProductHaar P))).map_eq⟩

theorem diagonalSIntegers_vaddInvariant (P : T → HeightOneSpectrum (𝓞 K)) :
    VAddInvariantMeasure (diagonalSIntegers P) (EuclideanIdeal.Space K × LocalProduct P)
      (semiLocalHaar P) := by
  letI := semiLocalHaar_isAddLeftInvariant P
  infer_instance

theorem productDomain_finite (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) :
    semiLocalHaar P (productDomain P a) < ∞ := by
  letI : IsLocallyFiniteMeasure (localProductHaar P) := by
    unfold localProductHaar
    infer_instance
  rw [semiLocalHaar, productDomain, Measure.prod_prod]
  exact ENNReal.mul_lt_top (EuclideanIdeal.idealFundamentalDomain_finite K (periodIdeal P a))
    (finitePeriod_compact P a).measure_lt_top

theorem productDomain_positive (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) :
    semiLocalHaar P (productDomain P a) ≠ 0 := by
  have hd : 0 < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hp : 0 < (semiLocalHaar P).real (productDomain P a) := by
    rw [productDomain_volume]
    exact mul_pos (pow_pos (by norm_num) _) (Real.sqrt_pos.mpr hd)
  exact (ENNReal.toReal_pos_iff.mp hp).1.ne'

end UnitDistance.SIntegerCRT
