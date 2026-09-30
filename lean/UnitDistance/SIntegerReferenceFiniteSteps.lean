module

public import UnitDistance.SIntegerReferenceSteps
public import UnitDistance.SIntegerReferenceRescaling

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual finite valuation labels after the signed-reference normalization -/

noncomputable section
open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeCompletion Local.ValuedHaar

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]
  {S : Type*} [Fintype S] {ι : K ≃ₐ[F] K}

local instance finiteStepMeasurableSpace (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel (v.adicCompletion K)
local instance finiteStepBorelSpace (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

/-- An actual norm-one field element with relative exponent `n-n₀` becomes
the literal canonical reciprocal step at exponent `n`, with an actual unit
in each selected completion. -/
theorem referenceFiniteStep_of_normOne (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ n : S → ℤ) (β : K) (hβ : Algebra.norm F β = 1)
    (hv : ∀ s, (D.prime (s, false)).valuation K β = WithZero.exp (-(n s-n₀ s))) :
    ∃ u : (s : S) → ValuationOneUnits ((D.prime (s, false)).adicCompletion K),
      pairedCoordinates D (referenceRescaling D n₀ (localEmbedding D.prime β)) =
        fun s => (witnessPairSteps D v hQ s).step (n s) (u s) := by
  have hs (s : S) := normOne_eq_reciprocalStep_of_valuation ι hι
    (D.prime (s, false)) (D.prime (s, true)) (D.partner s) β hβ (n s-n₀ s) (hv s)
  choose u hu using hs
  refine ⟨u, ?_⟩
  rw [pairedCoordinates_referenceRescaling]
  funext s
  change reciprocalRescaling ((D.prime (s, false)).adicCompletion K) (n₀ s)
    (pairCoordinates ι (D.prime (s, false)) (D.prime (s, true)) (D.partner s)
      (algebraMap K ((D.prime (s, false)).adicCompletion K) β,
       algebraMap K ((D.prime (s, true)).adicCompletion K) β)) = _
  rw [hu s, reciprocalRescaling_step]
  change (reciprocalSteps ((D.prime (s, false)).adicCompletion K)).step
    (n s-n₀ s+n₀ s) (u s) =
    (reciprocalSteps ((D.prime (s, false)).adicCompletion K)).step (n s) (u s)
  rw [sub_add_cancel]

variable [IsTotallyComplex K]

/-- The signed class-group construction supplies all hypotheses in the
finite completion step theorem. -/
theorem signedReferenceEnumeratedPoint_finiteStep (hι : ι ≠ 1)
    (hb : 0 < NumberField.InfinitePlace.nrRealPlaces F) (D : PrimePairFamily ι S)
    (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ) (n : SignedReferenceFiber D n₀) (τ : NumberField.Units.torsion K)
    (l : RelativeUnits.differenceLattice ι) :
    ∃ u : (s : S) → ValuationOneUnits ((D.prime (s, false)).adicCompletion K),
      pairedCoordinates D (referenceRescaling D n₀ (localEmbedding D.prime
        (signedReferenceEnumeratedPoint hι hb D n₀ n τ l))) =
          fun s => (witnessPairSteps D v hQ s).step (n.val s) (u s) :=
  referenceFiniteStep_of_normOne hι D v hQ n₀ n.val _
    (signedReferenceEnumeratedPoint_norm hι hb D n₀ n τ l)
    (signedReferenceEnumeratedPoint_first_valuation hι hb D n₀ n τ l)

end UnitDistance.SIntegerCRT
