module

public import UnitDistance.LocalOneDimensionalProfiles
public import UnitDistance.SIntegerLocalMeasure
public import UnitDistance.RelativeIdealCosetsFamily

@[expose] public section
set_option backward.privateInPublic true


/-!
# Literal witness profiles on the selected number-field completions

Each prime keeps its actual completion. The two factors of a conjugate pair
are joined by equality of their residue cardinalities, already proved from
the ideal-quotient isomorphism. Arbitrary signed reference rescalings preserve
the exact p-mass and the actual period ideal norm.
-/

noncomputable section
open Set MeasureTheory NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

namespace UnitDistance.SIntegerCRT
open RelativeIdealCosets

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]
  {S : Type*} [Fintype S] {ι : K ≃ₐ[F] K}

local instance witnessLocalMeasurableSpace (P : S × Bool → HeightOneSpectrum (𝓞 K)) (t : S × Bool) :
    MeasurableSpace ((P t).adicCompletion K) := borel ((P t).adicCompletion K)
local instance witnessLocalBorelSpace (P : S × Bool → HeightOneSpectrum (𝓞 K)) (t : S × Bool) :
    BorelSpace ((P t).adicCompletion K) := ⟨rfl⟩

theorem primePair_norm (D : PrimePairFamily ι S) (s : S) :
    Ideal.absNorm (D.prime (s, true)).asIdeal = Ideal.absNorm (D.prime (s, false)).asIdeal := by
  rw [D.partner, conjugateIdeal_absNorm]

theorem primePair_injective (D : PrimePairFamily ι S) : Function.Injective D.prime :=
  fun x y h => D.distinct (congrArg HeightOneSpectrum.asIdeal h)

/-- The profile's two base radii after reciprocal reference rescaling. -/
def witnessRadius (v : S → Fin 11) (n₀ : S → ℤ) (t : S × Bool) : ℤ :=
  if t.2 then Witness.periodPower (v t.1) - n₀ t.1 else n₀ t.1

/-- The exponents of the literal period ideal are the negatives of the radii. -/
def witnessPeriodExponent (v : S → Fin 11) (n₀ : S → ℤ) (t : S × Bool) : ℤ :=
  -witnessRadius v n₀ t

/-- A literal shell factor in one of the actual selected completions. -/
def witnessLocalFactor (D : PrimePairFamily ι S) (v : S → Fin 11) (n₀ : S → ℤ)
    (t : S × Bool) : (D.prime t).adicCompletion K → ℝ :=
  (Local.ValuedHaar.ballSystem ((D.prime t).adicCompletion K)).shellFactor
    (witnessRadius v n₀ t) (Finset.range 6) (Witness.shellWeightNat (v t.1))

/-- The actual finite-place profile on CRT's local product. -/
def witnessFiniteProfile (D : PrimePairFamily ι S) (v : S → Fin 11) (n₀ : S → ℤ)
    (x : LocalProduct D.prime) : ℝ := ∏ t, witnessLocalFactor D v n₀ t (x t)

/-- The literal p-weight appearing in the Poisson count. -/
def witnessFiniteWeight (D : PrimePairFamily ι S) (v : S → Fin 11) (n₀ : S → ℤ)
    (x : LocalProduct D.prime) : ℝ := ∏ t, witnessLocalFactor D v n₀ t (x t) ^ Witness.p

theorem witnessLocalFactor_nonneg (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (t : S × Bool) (x : (D.prime t).adicCompletion K) :
    0 ≤ witnessLocalFactor D v n₀ t x :=
  Local.BallSystem.shellFactor_nonneg _ _ _ _
    (fun i _ => Witness.shellWeightNat_nonneg (v t.1) i) x

theorem witnessFiniteProfile_nonneg (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (x : LocalProduct D.prime) : 0 ≤ witnessFiniteProfile D v n₀ x :=
  Finset.prod_nonneg (fun t _ => witnessLocalFactor_nonneg D v n₀ t (x t))

theorem witnessFiniteWeight_nonneg (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (x : LocalProduct D.prime) : 0 ≤ witnessFiniteWeight D v n₀ x :=
  Finset.prod_nonneg (fun t _ => Real.rpow_nonneg (witnessLocalFactor_nonneg D v n₀ t (x t)) _)

theorem witnessFiniteWeight_eq_rpow (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (x : LocalProduct D.prime) :
    witnessFiniteWeight D v n₀ x = witnessFiniteProfile D v n₀ x ^ Witness.p :=
  Real.finsetProd_rpow Finset.univ _ (fun t _ => witnessLocalFactor_nonneg D v n₀ t (x t)) _

theorem witnessLocalFactor_measurable (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (t : S × Bool) : Measurable (witnessLocalFactor D v n₀ t) :=
  Local.BallSystem.shellFactor_measurable _ _ _ _

theorem witnessFiniteProfile_measurable (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) : Measurable (witnessFiniteProfile D v n₀) :=
  Finset.measurable_prod _ (fun t _ =>
    (witnessLocalFactor_measurable D v n₀ t).comp (measurable_pi_apply t))

theorem witnessFiniteWeight_measurable (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) : Measurable (witnessFiniteWeight D v n₀) := by
  simp_rw [show witnessFiniteWeight D v n₀ =
    fun x => witnessFiniteProfile D v n₀ x ^ Witness.p from funext (witnessFiniteWeight_eq_rpow D v n₀)]
  exact (witnessFiniteProfile_measurable D v n₀).pow_const _

theorem witnessLocalFactor_rpow_integrable (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) (t : S × Bool) :
    Integrable (fun x => witnessLocalFactor D v n₀ t x ^ Witness.p)
      (Local.ValuedHaar.normalizedHaar ((D.prime t).adicCompletion K)) := by
  apply Local.BallSystem.shellFactor_rpow_integrable
    (Local.ValuedHaar.ballSystem ((D.prime t).adicCompletion K))
    (Nat.cast_pos.mpr (Nat.zero_lt_one.trans (Local.ValuedHaar.residueCard_gt_one _)))
    _ _ _ Witness.witness_basic.2.2.1.ne'

theorem witnessFiniteWeight_integrable (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) : Integrable (witnessFiniteWeight D v n₀) (localProductHaar D.prime) :=
  Integrable.fintype_prod_dep (witnessLocalFactor_rpow_integrable D v n₀)

theorem witness_residueCard (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (t : S × Bool) :
    (Local.ValuedHaar.residueCard ((D.prime t).adicCompletion K) : ℝ) =
      Witness.residueCard (v t.1) := by
  rw [Local.AdicResidue.residueCard_eq_absNorm]
  rcases t with ⟨s, b⟩
  cases b
  · exact hQ s
  · rw [primePair_norm]
    exact hQ s

theorem witnessLocalFactor_moment (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ) (t : S × Bool) :
    (∫ x, witnessLocalFactor D v n₀ t x ^ Witness.p
      ∂Local.ValuedHaar.normalizedHaar ((D.prime t).adicCompletion K)) =
      Witness.residueCard (v t.1) ^ witnessRadius v n₀ t * Witness.finiteLp (v t.1) := by
  rw [witnessLocalFactor, Local.BallSystem.shellFactor_moment _
    (Nat.cast_pos.mpr (Nat.zero_lt_one.trans (Local.ValuedHaar.residueCard_gt_one _)))
    _ _ _ Witness.witness_basic.2.2.1.ne',
    witness_residueCard D v hQ, Witness.shellLpMass_witness]

/-- Exact finite p-mass, independent of every signed reference label. -/
theorem witnessFiniteWeight_integral (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ) :
    (∫ x, witnessFiniteWeight D v n₀ x ∂localProductHaar D.prime) = Witness.tensorFiniteMass v := by
  change (∫ x, ∏ t, witnessLocalFactor D v n₀ t (x t) ^ Witness.p
    ∂Measure.pi (fun t => Local.ValuedHaar.normalizedHaar ((D.prime t).adicCompletion K))) = _
  rw [integral_fintype_prod_eq_prod
    (μ := fun t => Local.ValuedHaar.normalizedHaar ((D.prime t).adicCompletion K))
    (fun t x => witnessLocalFactor D v n₀ t x ^ Witness.p)]
  simp_rw [witnessLocalFactor_moment D v hQ n₀]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro s hs
  simp only [Fintype.prod_bool, witnessRadius, Bool.false_eq_true, ↓reduceIte]
  have hq : Witness.residueCard (v s) ≠ 0 := (zero_lt_one.trans (Witness.residueCard_gt_one (v s))).ne'
  rw [show Witness.residueCard (v s) ^ ((Witness.periodPower (v s) : ℤ) - n₀ s) *
      Witness.finiteLp (v s) * (Witness.residueCard (v s) ^ n₀ s * Witness.finiteLp (v s)) =
      (Witness.residueCard (v s) ^ ((Witness.periodPower (v s) : ℤ) - n₀ s) *
        Witness.residueCard (v s) ^ n₀ s) * Witness.finiteLp (v s) ^ 2 by ring,
    ← zpow_add₀ hq, sub_add_cancel, zpow_natCast]

theorem witnessFiniteProfile_period (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) {z : LocalProduct D.prime}
    (hz : z ∈ finitePeriod D.prime (witnessPeriodExponent v n₀)) (x : LocalProduct D.prime) :
    witnessFiniteProfile D v n₀ (x + z) = witnessFiniteProfile D v n₀ x := by
  apply Finset.prod_congr rfl
  intro t ht
  apply Local.BallSystem.shellFactor_period
  change Local.ValuedHaar.intValuation ((D.prime t).adicCompletion K) (z t) ≤
    WithZero.exp (witnessRadius v n₀ t)
  rw [canonical_intValuation_eq]
  simpa only [witnessPeriodExponent, neg_neg] using hz t

theorem witnessFiniteWeight_period (D : PrimePairFamily ι S) (v : S → Fin 11)
    (n₀ : S → ℤ) {z : LocalProduct D.prime}
    (hz : z ∈ finitePeriod D.prime (witnessPeriodExponent v n₀)) (x : LocalProduct D.prime) :
    witnessFiniteWeight D v n₀ (x + z) = witnessFiniteWeight D v n₀ x := by
  rw [witnessFiniteWeight_eq_rpow, witnessFiniteProfile_period D v n₀ hz,
    witnessFiniteWeight_eq_rpow]

/-- The exact period volume is unchanged by every reciprocal reference shift. -/
theorem witnessPeriod_volume (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ) :
    (localProductHaar D.prime).real (finitePeriod D.prime (witnessPeriodExponent v n₀)) =
      ∏ s, Witness.residueCard (v s) ^ Witness.periodPower (v s) := by
  rw [finitePeriod_volume, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro s hs
  simp only [Fintype.prod_bool, witnessPeriodExponent, witnessRadius, Bool.false_eq_true,
    ↓reduceIte, neg_neg, primePair_norm, hQ]
  rw [← zpow_add₀ (zero_lt_one.trans (Witness.residueCard_gt_one (v s))).ne',
    sub_add_cancel, zpow_natCast]

/-- The actual fractional period ideal, including all signed exponents, has
the norm forced by the displayed hard periods. -/
theorem witnessPeriod_norm (D : PrimePairFamily ι S) (v : S → Fin 11)
    (hQ : ∀ s, (Ideal.absNorm (D.prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v s))
    (n₀ : S → ℤ) :
    (FractionalIdeal.absNorm (periodIdeal D.prime (witnessPeriodExponent v n₀)).val : ℝ) =
      (∏ s, Witness.residueCard (v s) ^ Witness.periodPower (v s))⁻¹ := by
  have hv := witnessPeriod_volume D v hQ n₀
  rw [finitePeriod_volume_eq_inv_norm] at hv
  simpa only [inv_inv] using congrArg Inv.inv hv

end UnitDistance.SIntegerCRT
