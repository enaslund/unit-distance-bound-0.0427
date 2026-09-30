module

public import UnitDistance.GaloisFixedArithmetic
public import UnitDistance.WitnessPrimePairs
public import UnitDistance.SIntegerWitnessRetainedDescent

@[expose] public section
set_option backward.privateInPublic true


/-! Construct the complete geometric input from genuine finite Galois layers,
actual local ramification/residue data, and actual prime conjugation. -/
noncomputable section
open NumberField NumberField.InfinitePlace Filter
open scoped Classical
namespace UnitDistance.SIntegerCRT
open GaloisConjugation RelativeIdealCosets RelativeUnits NumberFieldAnalysis Witness

/-- The exact planar sequence theorem, with its fields, signatures, quadratic
unramifiedness, prime pairs and multiplicities all derived from the displayed
Galois layers. The three remaining scalar inequalities are about independently
defined finite quantities. -/
theorem target_of_growing_retained_galois_fields
    (Ks : ℕ → Type) [∀j, Field (Ks j)] [∀j, NumberField (Ks j)]
    [∀j, IsGalois ℚ (Ks j)] [∀j, Algebra ArithmeticRetained.RetainedField (Ks j)]
    (φ : ∀j, Ks j →+* ℂ) (c : ∀j, Gal(Ks j/ℚ))
    (hc : ∀j, NumberField.ComplexEmbedding.IsConj (φ j) (c j))
    (hc1 : ∀j, c j ≠ 1)
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop)
    (hunrM : ∀ᶠ j in atTop, FiniteUnramified ArithmeticRetained.RetainedField (Ks j))
    (he : ∀ᶠ j in atTop, ∀a : Fin 11,
      (rationalPrimeIdeal (primes a)).ramificationIdxIn (𝓞 (Ks j)) = ramification a)
    (hf : ∀ᶠ j in atTop, ∀a : Fin 11,
      (rationalPrimeIdeal (primes a)).inertiaDegIn (𝓞 (Ks j)) = residueDegree a)
    (hfree : ∀ᶠ j in atTop, ∀a : Fin 11, ∀P : PrimeNormFiber (Ks j) (primeNorm a),
      Ideal.map (RingOfIntegers.mapRingHom (c j).toRingHom) P.1.asIdeal ≠ P.1.asIdeal)
    (hindex : ∀ᶠ j in atTop,
      4096 ≤ (Subgroup.centralizer ({c j} : Set Gal(Ks j/ℚ))).index)
    (hpair : (1379635324335 : ℝ)/10^12 ≤ JPair)
    (hdiscM : Real.log (rootDiscriminant ArithmeticRetained.RetainedField) ≤ logRD)
    (hfinite : Real.log (dedekindZeta ArithmeticRetained.RetainedField ((1+(1/12000:ℝ):ℝ):ℂ)).re /
        (524288 : ℝ) + (1/12000:ℝ)*
          ((logRD-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4-
            (logDeriv (dedekindZeta ArithmeticRetained.RetainedField) 2).re/(524288 : ℝ)) < ceiling) :
    Target := by
  let Fs : ℕ → Type := fun j => fixedField (Ks j) (c j)
  letI : ∀j, Algebra.IsQuadraticExtension (Fs j) (Ks j) :=
    fun j => fixedFieldQuadratic (φ j) (c j) (hc j) (hc1 j)
  letI : ∀j, IsTotallyComplex (Ks j) := fun j => totallyComplex_of_retained
  let ι : ∀j, Ks j ≃ₐ[Fs j] Ks j := fun j => fixedAutomorphism (c j)
  have hι : ∀j, ι j ≠ 1 := fun j => fixedAutomorphism_ne_one (c j) (hc1 j)
  let Ss : ℕ → Type := fun j => ActualPrimePairIndex (ι j) (hι j)
  let D : ∀j, PrimePairFamily (ι j) (Ss j) := fun j => actualPrimePairs (ι j) (hι j)
  let v : ∀j, Ss j → Fin 11 := fun _ s => s.1
  apply target_of_witnessFields_retainedBase_rootsDerived Fs Ks Ss ι D v
    (fixedField_degree_tendsto Ks φ c hc hc1 hdegree)
    (Eventually.of_forall fun j => fixedField_finiteUnramified (φ j) (c j) (hc j) (hc1 j))
    (Eventually.of_forall hι)
    (Eventually.of_forall fun j => nrRealPlaces_pos (φ j) (c j) (hc j))
  · exact Eventually.of_forall fun j s => actualPrimePairs_norm (ι j) (hι j) s
  · filter_upwards [he,hf,hfree] with j hje hjf hjfree
    intro a
    exact actualPrimePairs_multiplicity (ι j) (hι j) a (hje a) (hjf a) (hjfree a)
  · exact hpair
  · filter_upwards [hunrM] with j hj
    change Real.log (rootDiscriminant (fixedField (Ks j) (c j))) ≤ logRD
    rw [fixedField_rootDiscriminant_eq (φ j) (c j) (hc j) (hc1 j) hj]
    exact hdiscM
  · exact hfinite
  · filter_upwards [hindex] with j hj
    exact fixedField_signature_lower (φ j) (c j) (hc j) (hc1 j) hj

end UnitDistance.SIntegerCRT
