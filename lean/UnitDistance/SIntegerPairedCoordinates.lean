module

public import UnitDistance.RelativeCompletionHaar
public import UnitDistance.SIntegerWitnessProfile

@[expose] public section
set_option backward.privateInPublic true


/-! # Haar-preserving paired coordinates on the actual selected completions -/

noncomputable section
open Set MeasureTheory NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets RelativeCompletion

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]
  {S : Type*} [Fintype S] {ι : K ≃ₐ[F] K}

local instance pairedLocalMeasurableSpace (v : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (v.adicCompletion K) := borel (v.adicCompletion K)
local instance pairedLocalBorelSpace (v : HeightOneSpectrum (𝓞 K)) :
    BorelSpace (v.adicCompletion K) := ⟨rfl⟩

abbrev PairedLocalProduct (D : PrimePairFamily ι S) :=
  (s : S) → (D.prime (s, false)).adicCompletion K × (D.prime (s, false)).adicCompletion K

def pairedLocalHaar (D : PrimePairFamily ι S) : Measure (PairedLocalProduct D) :=
  Measure.pi fun s =>
    (Local.ValuedHaar.normalizedHaar ((D.prime (s, false)).adicCompletion K)).prod
      (Local.ValuedHaar.normalizedHaar ((D.prime (s, false)).adicCompletion K))

/-- The partner coordinate is transported along the actual completed field involution. -/
def pairedCoordinates (D : PrimePairFamily ι S) : LocalProduct D.prime ≃+ PairedLocalProduct D where
  toFun x s := (x (s, false),
    (completionInvolution ι (D.prime (s, false)) (D.prime (s, true)) (D.partner s)).symm (x (s, true)))
  invFun y := fun
    | (s, false) => (y s).1
    | (s, true) =>
      completionInvolution ι (D.prime (s, false)) (D.prime (s, true)) (D.partner s) (y s).2
  left_inv x := by
    funext t
    rcases t with ⟨s, b⟩
    cases b
    · rfl
    · exact RingEquiv.apply_symm_apply _ _
  right_inv y := by
    funext s
    exact Prod.ext rfl (RingEquiv.symm_apply_apply _ _)
  map_add' x y := by
    funext s
    exact Prod.ext rfl (map_add _ _ _)

theorem pairedCoordinates_continuous (D : PrimePairFamily ι S) : Continuous (pairedCoordinates D) := by
  apply continuous_pi
  intro s
  exact (continuous_apply (s, false)).prodMk
    ((completionInvolution_symm_continuous ι _ _ (D.partner s)).comp (continuous_apply (s, true)))

theorem pairedCoordinates_symm_continuous (D : PrimePairFamily ι S) :
    Continuous (pairedCoordinates D).symm := by
  apply continuous_pi
  rintro ⟨s, b⟩
  cases b
  · exact (continuous_apply s).fst
  · exact (completionInvolution_continuous ι _ _ (D.partner s)).comp (continuous_apply s).snd

def pairedCoordinatesHomeomorph (D : PrimePairFamily ι S) : LocalProduct D.prime ≃ₜ PairedLocalProduct D where
  toEquiv := (pairedCoordinates D).toEquiv
  continuous_toFun := pairedCoordinates_continuous D
  continuous_invFun := pairedCoordinates_symm_continuous D

def pairedCoordinatesMeasurableEquiv (D : PrimePairFamily ι S) : LocalProduct D.prime ≃ᵐ PairedLocalProduct D :=
  (pairedCoordinatesHomeomorph D).toMeasurableEquiv

theorem pairedCoordinates_symm_measurePreserving (D : PrimePairFamily ι S) :
    MeasurePreserving (pairedCoordinates D).symm (pairedLocalHaar D) (localProductHaar D.prime) := by
  refine ⟨(pairedCoordinates_symm_continuous D).measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro A hA
  rw [Measure.map_apply (pairedCoordinates_symm_continuous D).measurable
    (MeasurableSet.univ_pi hA)]
  have hp : (pairedCoordinates D).symm ⁻¹' Set.univ.pi A =
      Set.univ.pi (fun s => A (s, false) ×ˢ
        ((completionInvolution ι (D.prime (s, false)) (D.prime (s, true)) (D.partner s)) ⁻¹' A (s, true))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, Prod.forall, Bool.forall_bool]
    constructor
    · intro hx s
      exact ⟨(hx s).1, (hx s).2⟩
    · intro hx s
      exact ⟨(hx s).1, (hx s).2⟩
  rw [hp, pairedLocalHaar, Measure.pi_pi, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro s hs
  rw [Measure.prod_prod,
    (completionInvolution_measurePreserving ι _ _ (D.partner s)).measure_preimage (hA (s, true)).nullMeasurableSet,
    Fintype.prod_bool]
  exact mul_comm _ _

/-- Exact transport of the full finite-place Haar measure. -/
theorem pairedCoordinates_measurePreserving (D : PrimePairFamily ι S) :
    MeasurePreserving (pairedCoordinates D) (localProductHaar D.prime) (pairedLocalHaar D) :=
  MeasurePreserving.symm (pairedCoordinatesMeasurableEquiv D).symm
    (pairedCoordinates_symm_measurePreserving D)

/-- The actual completion ball system, with the selected witness's residue label. -/
def witnessPairBallSystem (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s)) (s : S) :
    Local.BallSystem ((D.prime (s, false)).adicCompletion K)
      (Local.ValuedHaar.normalizedHaar ((D.prime (s, false)).adicCompletion K))
      (Witness.residueCard (v s)) where
  ball := Local.ValuedHaar.ball _
  mono := Local.ValuedHaar.ball_mono _
  measurable := Local.ValuedHaar.ball_measurable _
  volume a := by
    rw [Local.ValuedHaar.normalizedHaar_ball, witness_residueCard D v hQ (s, false)]

/-- The actual reciprocal uniformizer/unit steps in each first completion. -/
def witnessPairSteps (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s)) (s : S) :
    (witnessPairBallSystem D v hQ s).ReciprocalSteps
      (Local.ValuedHaar.ValuationOneUnits ((D.prime (s, false)).adicCompletion K)) where
  step := (Local.ValuedHaar.reciprocalSteps ((D.prime (s, false)).adicCompletion K)).step
  fst_mem := (Local.ValuedHaar.reciprocalSteps ((D.prime (s, false)).adicCompletion K)).fst_mem
  snd_mem := (Local.ValuedHaar.reciprocalSteps ((D.prime (s, false)).adicCompletion K)).snd_mem

theorem witnessPair_factor_partner (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (s : S) (k : ℤ) (x : (D.prime (s, true)).adicCompletion K) :
    Witness.localShellFactor (v s) (witnessPairBallSystem D v hQ s) k
      ((completionInvolution ι (D.prime (s, false)) (D.prime (s, true)) (D.partner s)).symm x) =
      (Local.ValuedHaar.ballSystem ((D.prime (s, true)).adicCompletion K)).shellFactor
        k (Finset.range 6) (Witness.shellWeightNat (v s)) x := by
  apply Local.BallSystem.shellFactor_transport
  intro a y
  change Local.ValuedHaar.intValuation ((D.prime (s, false)).adicCompletion K)
    ((completionInvolution ι (D.prime (s, false)) (D.prime (s, true)) (D.partner s)).symm y) ≤
      WithZero.exp a ↔ Local.ValuedHaar.intValuation ((D.prime (s, true)).adicCompletion K) y ≤ WithZero.exp a
  have he := completionInvolution_intValuation ι (D.prime (s, false)) (D.prime (s, true))
    (D.partner s) ((completionInvolution ι (D.prime (s, false)) (D.prime (s, true)) (D.partner s)).symm y)
  rw [RingEquiv.apply_symm_apply] at he
  rw [he]

/-- Exact equality with the tensor profile used by the finite overlap laws. -/
theorem witnessFiniteProfile_pairedCoordinates (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (x : LocalProduct D.prime) :
    Witness.tensorFiniteProfile v
      (fun s => Local.ValuedHaar.normalizedHaar ((D.prime (s, false)).adicCompletion K))
      (witnessPairBallSystem D v hQ) (pairedCoordinates D x) = witnessFiniteProfile D v 0 x := by
  unfold Witness.tensorFiniteProfile witnessFiniteProfile
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro s hs
  rw [Witness.localShellProfile_eq_factors, Fintype.prod_bool]
  change Witness.localShellFactor (v s) (witnessPairBallSystem D v hQ s) 0 (x (s, false)) *
      Witness.localShellFactor (v s) (witnessPairBallSystem D v hQ s) (Witness.periodPower (v s))
        ((completionInvolution ι (D.prime (s, false)) (D.prime (s, true)) (D.partner s)).symm (x (s, true))) = _
  rw [witnessPair_factor_partner]
  simp only [witnessLocalFactor, witnessRadius, Bool.false_eq_true, ↓reduceIte, Pi.zero_apply, sub_zero]
  exact mul_comm _ _

theorem pairedCoordinates_field (D : PrimePairFamily ι S) (hι : ι ≠ 1) (β : K) (s : S) :
    pairedCoordinates D (localEmbedding D.prime β) s =
      (algebraMap K ((D.prime (s, false)).adicCompletion K) β,
        algebraMap K ((D.prime (s, false)).adicCompletion K) (ι β)) :=
  RelativeCompletion.pairCoordinates_field ι hι _ _ (D.partner s) β

end UnitDistance.SIntegerCRT
