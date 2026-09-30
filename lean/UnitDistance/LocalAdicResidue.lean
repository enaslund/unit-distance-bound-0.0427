module

public import UnitDistance.LocalResidueDensity
public import UnitDistance.LocalValuedHaar
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual adic-completion residue fields

For a nonzero prime of a Dedekind domain, the residue field of the local
completion is identified with the global prime quotient. The residue-density
argument and Mathlib's approximation of local integers by global integers
supply both parts of the identification.
-/

noncomputable section
open Set MeasureTheory IsDedekindDomain HeightOneSpectrum WithZero
open scoped BigOperators

namespace UnitDistance.Local.AdicResidue

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- Global integers mapped into the valuation ring of the fraction field. -/
def integerMap : R →+* (v.valuation K).integer where
  toFun a := ⟨algebraMap R K a, v.valuation_le_one a⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (map_mul _ a b)

/-- The actual residue homomorphism from global integers. -/
def residueMap : R →+* IsLocalRing.ResidueField (v.valuation K).integer :=
  (IsLocalRing.residue _).comp (integerMap R K v)

theorem residueMap_ker : RingHom.ker (residueMap R K v) = v.asIdeal := by
  ext a
  rw [RingHom.mem_ker]
  change IsLocalRing.residue (v.valuation K).integer (integerMap R K v a) = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  exact v.valuation_lt_one_iff_mem a

/-- Every local residue class contains a global integer. -/
theorem residueMap_surjective : Function.Surjective (residueMap R K v) := by
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer x.property (1 : ℤᵐ⁰ˣ)
  refine ⟨a, ?_⟩
  change IsLocalRing.residue (v.valuation K).integer (integerMap R K v a) =
    IsLocalRing.residue (v.valuation K).integer x
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  exact ha

/-- The global prime quotient is the residue field of the local valuation ring. -/
def sourceResidueEquiv : R ⧸ v.asIdeal ≃+* IsLocalRing.ResidueField (v.valuation K).integer := by
  rw [← residueMap_ker R K v]
  exact (residueMap R K v).quotientKerEquivOfSurjective (residueMap_surjective R K v)


/-- Completion preserves the source valuation-ring residue field. -/
def completionResidueEquiv :
    IsLocalRing.ResidueField (v.valuation K).integer ≃+*
      Valued.ResidueField (v.adicCompletion K) := by
  letI : Valued K ℤᵐ⁰ := v.adicValued
  exact ResidueDensity.residueEquiv (algebraMap K (v.adicCompletion K))
    (fun x => v.valuedAdicCompletion_eq_valuation' x) (v.denseRange_algebraMap K)

/-- The actual adic-completion residue field is the original prime quotient. -/
def primeQuotientResidueEquiv : R ⧸ v.asIdeal ≃+* Valued.ResidueField (v.adicCompletion K) :=
  (sourceResidueEquiv R K v).trans (completionResidueEquiv R K v)

theorem completion_residue_card : Nat.card (Valued.ResidueField (v.adicCompletion K)) =
    Nat.card (R ⧸ v.asIdeal) :=
  (Nat.card_congr (primeQuotientResidueEquiv R K v).toEquiv).symm

instance completionResidueFinite [Finite (R ⧸ v.asIdeal)] :
    Finite (Valued.ResidueField (v.adicCompletion K)) :=
  Finite.of_equiv _ (primeQuotientResidueEquiv R K v).toEquiv

section FiniteFree

variable [Module.Finite ℤ R] [Module.Free ℤ R]

local instance integerRingInfinite : Infinite R := by
  haveI : IsAddTorsionFree R := .of_isTorsionFree ℤ R
  haveI : CharZero R := CharZero.of_isAddTorsionFree R R
  exact Infinite.of_injective (Nat.cast : ℕ → R) Nat.cast_injective

local instance integerRingFiniteQuotients : Ring.HasFiniteQuotients R := .of_module_finite ℤ R

local instance adicCompletionRankOne :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).RankOne :=
  NumberField.HeightOneSpectrum.instRankOneAdicCompletion K v

local instance adicCompletionNormedField : NormedField (v.adicCompletion K) :=
  NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion K v

instance primeQuotientFinite : Finite (R ⧸ v.asIdeal) :=
  Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot

/-- Number-field-style finite-free Dedekind domains have locally compact
completions: completeness, the discrete valuation ring property, and the now
proved finite residue field discharge the exact Mathlib criterion. -/
instance adicCompletionProper : ProperSpace (v.adicCompletion K) :=
  (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := v.adicCompletion K) (Γ₀ := ℤᵐ⁰)).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K)), inferInstance⟩

/-- The ordinary topology of the actual adic completion is locally compact. -/
theorem locallyCompact_adicCompletion : LocallyCompactSpace (v.adicCompletion K) :=
  inferInstance

/-- The valuative relation comes from the actual extended adic valuation. -/
instance adicValuativeRel : ValuativeRel (v.adicCompletion K) :=
  .ofValuation (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

instance adicValuationCompatible : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Compatible :=
  .ofValuation _

instance adicValuativeTopology : IsValuativeTopology (v.adicCompletion K) :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
    (fun {s} => Valued.is_topological_valuation s)

instance adicValuationNontrivial : ValuativeRel.IsNontrivial (v.adicCompletion K) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).mpr
    inferInstance

/-- The actual finite-place completion is a nonarchimedean local field. -/
instance adicLocalField : IsNonarchimedeanLocalField (v.adicCompletion K) where
  toLocallyCompactSpace := locallyCompact_adicCompletion R K v

/-- The canonical valuative-relation integer ring is the integer ring of the
actual extended adic valuation. -/
def canonicalIntegerEquiv :
    (ValuativeRel.valuation (v.adicCompletion K)).integer ≃+* Valued.integer (v.adicCompletion K) where
  toFun x := ⟨x, (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).le_one_iff_le_one.mp x.property⟩
  invFun x := ⟨x, (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).le_one_iff_le_one.mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The residue cardinality used by the general local-window model is exactly
the cardinality of the global prime quotient. -/
theorem residueCard_eq_primeQuotient :
    ValuedHaar.residueCard (v.adicCompletion K) = Nat.card (R ⧸ v.asIdeal) := by
  rw [ValuedHaar.residueCard,
    Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (canonicalIntegerEquiv R K v)).toEquiv]
  exact completion_residue_card R K v

/-- The residue cardinality is the ordinary absolute norm of the global prime. -/
theorem residueCard_eq_absNorm :
    ValuedHaar.residueCard (v.adicCompletion K) = Ideal.absNorm v.asIdeal := by
  rw [residueCard_eq_primeQuotient, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- Haar ball volumes on the actual finite-place completion, expressed with
the global prime quotient cardinality. -/
theorem normalizedHaar_ball (a : ℤ) :
    (ValuedHaar.normalizedHaar (v.adicCompletion K)).real
      (ValuedHaar.ball (v.adicCompletion K) a) = (Nat.card (R ⧸ v.asIdeal) : ℝ) ^ a := by
  simpa only [residueCard_eq_primeQuotient] using ValuedHaar.normalizedHaar_ball (v.adicCompletion K) a

local instance adicMeasurableSpace : MeasurableSpace (v.adicCompletion K) := borel (v.adicCompletion K)
local instance adicBorelSpace : BorelSpace (v.adicCompletion K) := ⟨rfl⟩

/-- The literal local weighted operator formula on an actual finite-place
completion, with the prime's ordinary absolute norm as residue cardinality. -/
theorem operator_formula
    (ν : Measure (ValuedHaar.ValuationOneUnits (v.adicCompletion K))) [IsProbabilityMeasure ν]
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    (∫ x, (ValuedHaar.ballSystem (v.adicCompletion K)).shellProfile k I w x *
      (ValuedHaar.ballSystem (v.adicCompletion K)).displacementOperator
        (ValuedHaar.reciprocalSteps (v.adicCompletion K)) ν
        ((ValuedHaar.ballSystem (v.adicCompletion K)).shellProfile k I w) x
      ∂(ValuedHaar.normalizedHaar (v.adicCompletion K)).prod
        (ValuedHaar.normalizedHaar (v.adicCompletion K))) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ k * ∑ ij ∈ I, ∑ rt ∈ I,
        w ij * shellKernel (Ideal.absNorm v.asIdeal) k ij.1 ij.2 rt.1 rt.2 * w rt := by
  simpa only [residueCard_eq_absNorm] using ValuedHaar.operator_formula (v.adicCompletion K) ν k I w

end FiniteFree

end UnitDistance.Local.AdicResidue
