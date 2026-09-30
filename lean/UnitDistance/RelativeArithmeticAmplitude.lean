module

public import UnitDistance.RelativeUnitsMass
public import UnitDistance.RelativeArchimedeanCoordinates
public import UnitDistance.TensorFunctional
public import UnitDistance.FiniteFunctionalCertificate

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact arithmetic normalization of the geometric amplitude

The quantities in this file are actual number-field invariants and the actual
Gaussian/Student integrals. The finite-place factor is kept separate so that
its later identification with an S-adic integral cannot be confused with the
scalar normalization proved here. No tower or graph existence is asserted.
-/

noncomputable section
open NumberField NumberField.InfinitePlace
open scoped Classical

namespace UnitDistance.RelativeUnits
open NumberFieldAnalysis

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

/-- The discriminant covolume of the actual diagonal S-integer lattice.
`SIntegerCRT.productDomain_volume` identifies this expression with its actual
product fundamental-domain volume for every finite set of selected primes. -/
def arithmeticCovolume (K : Type) [Field K] [NumberField K] : ℝ :=
  (2⁻¹ : ℝ)^nrComplexPlaces K * Real.sqrt (absoluteDiscriminant K)

omit [IsTotallyComplex K] in
theorem arithmeticCovolume_pos : 0 < arithmeticCovolume K := by
  unfold arithmeticCovolume
  positivity [absoluteDiscriminant_pos K]

/-- The signature parameter of the actual base field. -/
def signatureRatio (F : Type) [Field F] [NumberField F] : ℝ :=
  (nrComplexPlaces F : ℝ) / (Module.finrank ℚ F : ℝ)

theorem degree_pos_real : 0 < (Module.finrank ℚ F : ℝ) := by
  exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)

theorem signatureRatio_nonneg : 0 ≤ signatureRatio F := by
  unfold signatureRatio
  positivity

theorem signatureRatio_le_half : signatureRatio F ≤ 1/2 := by
  rw [signatureRatio, div_le_iff₀ (degree_pos_real (F := F))]
  have h : (nrRealPlaces F : ℝ) + 2*nrComplexPlaces F = Module.finrank ℚ F := by
    exact_mod_cast card_add_two_mul_card_eq_rank F
  have h₀ : (0 : ℝ) ≤ nrRealPlaces F := Nat.cast_nonneg _
  linarith

theorem log_rootDiscriminant :
    Real.log (rootDiscriminant F) =
      Real.log (absoluteDiscriminant F) / (Module.finrank ℚ F : ℝ) := by
  rw [rootDiscriminant, Real.log_rpow (absoluteDiscriminant_pos F)]
  ring

theorem log_arithmeticCovolume (hunr : FiniteUnramified F K) :
    Real.log (arithmeticCovolume K) =
      (Module.finrank ℚ F : ℝ) * (-Real.log 2 + Real.log (rootDiscriminant F)) := by
  rw [arithmeticCovolume,
    Real.log_mul (by positivity) (Real.sqrt_pos.mpr (absoluteDiscriminant_pos K)).ne',
    Real.log_pow, Real.log_inv,
    sqrt_absoluteDiscriminant_eq_base K F
      (Algebra.IsQuadraticExtension.finrank_eq_two F K) hunr,
    nrComplexPlaces_eq_base_degree K F (Algebra.IsQuadraticExtension.finrank_eq_two F K),
    log_rootDiscriminant]
  field_simp [(degree_pos_real (F := F)).ne']

theorem log_relativeUnitMass (hunr : FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F) :
    Real.log (relativeUnitMass ι) =
      ((Module.finrank ℚ F : ℝ)-1)*Real.log 2 +
        ((nrRealPlaces F : ℝ)+nrComplexPlaces F)*Real.log Real.pi -
        (Module.finrank ℚ F : ℝ)/2*Real.log (rootDiscriminant F) -
        Real.log (relativeResidue K F) := by
  rw [relativeUnitMass_eq_rootDiscriminant hunr ι hι hb,
    Real.log_div (by positivity) (by positivity [rootDiscriminant_pos F, relativeResidue_pos K F]),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity [rootDiscriminant_pos F]) (relativeResidue_pos K F).ne',
    Real.log_pow, Real.log_pow, Real.log_rpow (rootDiscriminant_pos F)]
  have hd : 1 ≤ Module.finrank ℚ F := Module.finrank_pos (R := ℚ) (M := F)
  rw [Nat.cast_sub hd, Nat.cast_one, Nat.cast_add]
  ring

/-- Actual mass, covolume and archimedean factors, multiplied by a separately
specified finite-place normalized functional. The factor `2^(2+δ)` is the
one in the proved unordered finite geometric transfer. -/
def arithmeticAmplitude (ι : K ≃ₐ[F] K) (finiteFactor ε : ℝ) : ℝ :=
  relativeUnitMass ι * (arithmeticCovolume K)^increment / (2:ℝ)^(2+increment) *
    Witness.tensorFunctional (RealPlaceIndex F) (PairPlaceIndex F) * finiteFactor *
      Real.exp (-4*(ε*(Module.finrank ℚ F : ℝ)))

theorem arithmeticAmplitude_pos (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    {finiteFactor ε : ℝ} (hfinite : 0 < finiteFactor) :
    0 < arithmeticAmplitude ι finiteFactor ε := by
  unfold arithmeticAmplitude
  positivity [relativeUnitMass_pos ι hι, arithmeticCovolume_pos (K := K),
    Witness.tensorFunctional_pos (RealPlaceIndex F) (PairPlaceIndex F)]

/-- The exact exponential rate from actual arithmetic invariants. -/
def arithmeticRate (F K : Type) [Field F] [Field K] [NumberField F] [NumberField K]
    (finiteRate ε : ℝ) : ℝ :=
  finiteRate - (1/2-increment)*Real.log (rootDiscriminant F) -
    Real.log (relativeResidue K F)/(Module.finrank ℚ F : ℝ) +
    (1-increment)*Real.log 2 + (1-signatureRatio F)*Real.log Real.pi +
    (1-2*signatureRatio F)*Witness.JCompact + signatureRatio F*Witness.JPair - 4*ε

theorem log_arithmeticAmplitude (hunr : FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    {finiteFactor : ℝ} (hfinite : 0 < finiteFactor) (ε : ℝ) :
    Real.log (arithmeticAmplitude ι finiteFactor ε) =
      (Module.finrank ℚ F : ℝ)*
        arithmeticRate F K (Real.log finiteFactor/(Module.finrank ℚ F : ℝ)) ε -
          (3+increment)*Real.log 2 := by
  have hm := relativeUnitMass_pos ι hι
  have hD := arithmeticCovolume_pos (K := K)
  have ht := Witness.tensorFunctional_pos (RealPlaceIndex F) (PairPlaceIndex F)
  rw [arithmeticAmplitude, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hfinite.ne', Real.log_mul (by positivity) ht.ne',
    Real.log_div (by positivity) (by positivity), Real.log_mul hm.ne' (by positivity),
    Real.log_rpow hD, Real.log_rpow (by norm_num : (0:ℝ)<2), Real.log_exp,
    log_relativeUnitMass hunr ι hι hb, log_arithmeticCovolume hunr,
    Witness.log_tensorFunctional]
  have hs : (nrRealPlaces F : ℝ)+2*nrComplexPlaces F = Module.finrank ℚ F := by
    exact_mod_cast card_add_two_mul_card_eq_rank F
  change _ + ((nrRealPlaces F : ℝ)*Witness.JCompact +
    (nrComplexPlaces F : ℝ)*Witness.JPair) + _ + _ = _
  unfold arithmeticRate signatureRatio
  field_simp [(degree_pos_real (F := F)).ne']
  rw [show (nrRealPlaces F : ℝ) = (Module.finrank ℚ F : ℝ)-2*nrComplexPlaces F by linarith]
  ring

/-- Exact normalization, including the remaining constant factor of two
from the arithmetic mass and every unordered-edge factor. -/
theorem arithmeticAmplitude_eq_exp (hunr : FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    {finiteFactor : ℝ} (hfinite : 0 < finiteFactor) (ε : ℝ) :
    arithmeticAmplitude ι finiteFactor ε =
      Real.exp ((Module.finrank ℚ F : ℝ)*
        arithmeticRate F K (Real.log finiteFactor/(Module.finrank ℚ F : ℝ)) ε) /
          (2:ℝ)^(3+increment) := by
  rw [← Real.exp_log (arithmeticAmplitude_pos ι hι hfinite),
    log_arithmeticAmplitude hunr ι hι hb hfinite ε, Real.exp_sub,
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  congr 2
  ring

omit [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K] in
/-- The published numerical margin bounds the actual arithmetic rate whenever
the actual discriminant, residue quotient, signature and finite factor satisfy
their stated inequalities. These field-family inequalities remain hypotheses. -/
theorem margin_le_arithmeticRate {finiteRate ε : ℝ}
    (hfinite : Witness.finiteProfit ≤ finiteRate)
    (hdisc : Real.log (rootDiscriminant F) ≤ Witness.logRD)
    (hresidue : Real.log (relativeResidue K F)/(Module.finrank ℚ F : ℝ) ≤ Witness.ceiling) :
    Witness.margin (signatureRatio F)-4*ε ≤ arithmeticRate F K finiteRate ε := by
  have hd := mul_le_mul_of_nonneg_left hdisc
    (show (0:ℝ) ≤ 1/2-increment by norm_num [increment])
  dsimp only [Witness.margin, arithmeticRate]
  linarith

/-- A positive, explicit growth rate from the one permitted pair-integral
enclosure and genuine arithmetic bounds. No existence of fields is asserted. -/
theorem arithmeticAmplitude_lower (hunr : FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F)
    {finiteFactor : ℝ} (hfinite : 0 < finiteFactor)
    (hpair : (1379635324335:ℝ)/10^12 ≤ Witness.JPair)
    (hfactor : Witness.finiteProfit ≤ Real.log finiteFactor/(Module.finrank ℚ F : ℝ))
    (hdisc : Real.log (rootDiscriminant F) ≤ Witness.logRD)
    (hresidue : Real.log (relativeResidue K F)/(Module.finrank ℚ F : ℝ) ≤ Witness.ceiling)
    (hsignature : Witness.thetaMin ≤ signatureRatio F) :
    Real.exp ((Module.finrank ℚ F : ℝ)*((533:ℝ)/10^8))/(2:ℝ)^(3+increment) ≤
      arithmeticAmplitude ι finiteFactor Witness.epsilon := by
  rw [arithmeticAmplitude_eq_exp hunr ι hι hb hfinite]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (degree_pos_real (F := F)).le
  exact (Witness.uniform_margin_of_pair hpair hsignature).le.trans
    (margin_le_arithmeticRate hfactor hdisc hresidue)

section Family
open Filter

variable (Fs Ks : ℕ → Type)
  [∀ j, Field (Fs j)] [∀ j, Field (Ks j)]
  [∀ j, NumberField (Fs j)] [∀ j, NumberField (Ks j)]
  [∀ j, Algebra (Fs j) (Ks j)]
  [∀ j, Algebra.IsQuadraticExtension (Fs j) (Ks j)]
  [∀ j, IsTotallyComplex (Ks j)]

/-- Exact arithmetic amplitudes diverge along every actual family of growing
degree satisfying the eventual manuscript bounds. Each nonnumerical family
condition is explicit; none is inferred from the finite numerical margin. -/
theorem arithmeticAmplitude_tendsto
    (ι : (j : ℕ) → Ks j ≃ₐ[Fs j] Ks j) (finiteFactor : ℕ → ℝ)
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Fs j)) atTop atTop)
    (hunr : ∀ᶠ j in atTop, FiniteUnramified (Fs j) (Ks j))
    (hι : ∀ᶠ j in atTop, ι j ≠ 1)
    (hb : ∀ᶠ j in atTop, 0 < nrRealPlaces (Fs j))
    (hfinite : ∀ᶠ j in atTop, 0 < finiteFactor j)
    (hpair : (1379635324335:ℝ)/10^12 ≤ Witness.JPair)
    (hfactor : ∀ᶠ j in atTop, Witness.finiteProfit ≤
      Real.log (finiteFactor j)/(Module.finrank ℚ (Fs j) : ℝ))
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Fs j)) ≤ Witness.logRD)
    (hresidue : ∀ᶠ j in atTop,
      Real.log (relativeResidue (Ks j) (Fs j))/(Module.finrank ℚ (Fs j) : ℝ) ≤ Witness.ceiling)
    (hsignature : ∀ᶠ j in atTop, Witness.thetaMin ≤ signatureRatio (Fs j)) :
    Tendsto (fun j => arithmeticAmplitude (ι j) (finiteFactor j) Witness.epsilon) atTop atTop := by
  have hd : Tendsto (fun j => (Module.finrank ℚ (Fs j) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdegree
  have hg : Tendsto (fun j => Real.exp ((Module.finrank ℚ (Fs j) : ℝ)*((533:ℝ)/10^8)) /
      (2:ℝ)^(3+increment)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (hd.atTop_mul_const (by norm_num))).atTop_div_const (by positivity)
  apply tendsto_atTop_mono' atTop _ hg
  filter_upwards [hunr, hι, hb, hfinite, hfactor, hdisc, hresidue, hsignature]
    with j hu hi hb hf hfac hd hr hs
  exact arithmeticAmplitude_lower hu (ι j) hi hb hf hpair hfac hd hr hs

end Family

end UnitDistance.RelativeUnits
