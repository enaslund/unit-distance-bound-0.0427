module

public import UnitDistance.RelativeHeckeGamma
public import UnitDistance.HeckePairedProduct

@[expose] public section
set_option backward.privateInPublic true


/-!
# Comparison from a paired product, and passage to the family boundary

The first theorem isolates the still-needed Hecke product identification:
the limits are required to be the *actual* completed relative zeta values.
The remaining results prove the two-limit passage uniformly in signature.
No field-family existence or unconditional prime-budget theorem is asserted
by these analytic transfer results.
-/

noncomputable section
open Filter Topology NumberField NumberField.InfinitePlace

namespace UnitDistance.NumberFieldAnalysis

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

/-- A genuine paired product for the actual completion proves its monotonicity.
This replaces a monotonicity premise by the explicit product identification
and zero-strip assertions to be supplied by relative Hecke theory. -/
theorem relativeCompletedReal_monotoneOn_of_paired_product (ell : ℝ)
    {ι : Type*} (zeros : ι → ℂ) (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hzeros : ∀ i, |(zeros i).re| ≤ (1/2 : ℝ))
    (hproduct : ∀ t ∈ Set.Ici (1/2 : ℝ),
      Tendsto (fun J : Finset ι => HeckeAnalysis.pairedPartialProduct zeros m A J t)
        atTop (𝓝 (relativeCompletedReal K F ell (t+1/2)))) :
    MonotoneOn (relativeCompletedReal K F ell) (Set.Ici 1) := by
  have hmono := HeckeAnalysis.monotoneOn_of_paired_product zeros m
    (by norm_num : (0:ℝ) ≤ 1/2) hA hzeros
    (fun t => relativeCompletedReal K F ell (t+1/2)) hproduct
  intro s hs t ht hst
  have h := hmono (a := s-1/2) (b := t-1/2)
    (by change 1/2 ≤ s-1/2; change 1 ≤ s at hs; linarith)
    (by change 1/2 ≤ t-1/2; change 1 ≤ t at ht; linarith)
    (by linarith)
  simpa only [sub_add_cancel] using h

variable [Algebra F K]

/-- Actual finite-field Euler comparison and the paired Hecke product give
the full finite-gamma estimate, with no monotonicity assumption. -/
theorem normalized_log_relativeResidue_le_of_paired_product
    (hdegree : Module.finrank F K = 2) (ell : ℝ)
    {ι : Type*} (zeros : ι → ℂ) (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hzeros : ∀ i, |(zeros i).re| ≤ (1/2 : ℝ))
    (hproduct : ∀ t ∈ Set.Ici (1/2 : ℝ),
      Tendsto (fun J : Finset ι => HeckeAnalysis.pairedPartialProduct zeros m A J t)
        atTop (𝓝 (relativeCompletedReal K F ell (t+1/2))))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Real.log (relativeResidue K F)/(Module.finrank ℚ F : ℝ) ≤
      Real.log (dedekindZeta K (1+epsilon)).re/(2*(Module.finrank ℚ F : ℝ)) +
        relativeGammaCorrection ell epsilon
          ((nrComplexPlaces F : ℝ)/(Module.finrank ℚ F : ℝ)) := by
  apply normalized_log_relativeResidue_le_zeta_of_completion_le K F hdegree ell hepsilon
  exact relativeCompletedReal_monotoneOn_of_paired_product K F ell zeros m hA hzeros hproduct
    (by simp) (by change 1 ≤ 1+epsilon; linarith) (by linarith)

/-- An elementary two-limit lemma. Pointwise limits of the Euler quantities
are taken first; the abscissa then approaches one. There is no interchange
of these limits and no finite-field Euler product evaluated at one. -/
theorem eventually_lt_of_boundary_comparison
    (x : ℕ → ℝ) (z : ℕ → ℝ → ℝ) (Z error : ℝ → ℝ) {C T : ℝ}
    (hboundary : Tendsto (fun epsilon => Z epsilon+error epsilon) (𝓝[>] 0) (𝓝 C))
    (hz : ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto (fun n => z n epsilon) atTop (𝓝 (Z epsilon)))
    (hbound : ∀ epsilon : ℝ, 0 < epsilon → ∀ n, x n ≤ z n epsilon+error epsilon)
    (hCT : C < T) : ∀ᶠ n in atTop, x n < T := by
  have hpos : ∀ᶠ epsilon : ℝ in 𝓝[>] 0, 0 < epsilon := self_mem_nhdsWithin
  obtain ⟨epsilon, he, hsmall⟩ :=
    (hpos.and (hboundary.eventually_lt_const hCT)).exists
  have hlim := (hz epsilon he).add_const (error epsilon)
  filter_upwards [hlim.eventually_lt_const hsmall] with n hn
  exact (hbound epsilon he n).trans_lt hn

section Family

variable (Ks Fs : ℕ → Type*)
  [∀ n, Field (Ks n)] [∀ n, NumberField (Ks n)]
  [∀ n, Field (Fs n)] [∀ n, NumberField (Fs n)]
  [∀ n, Algebra (Fs n) (Ks n)]

/-- Uniform passage to one for an actual sequence of number-field quotients.
The hypotheses record the completed-function comparisons and the two ordinary
Euler limits; the variable signatures cause no additional assumption. -/
theorem eventual_normalized_log_relativeResidue_lt
    (hdegree : ∀ n, Module.finrank (Fs n) (Ks n) = 2) (ell : ℝ)
    (Z : ℝ → ℝ) {C T : ℝ}
    (hcomp : ∀ epsilon : ℝ, 0 < epsilon → ∀ n,
      relativeCompletedReal (Ks n) (Fs n) ell 1 ≤
        relativeCompletedReal (Ks n) (Fs n) ell (1+epsilon))
    (hz : ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto (fun n => Real.log (dedekindZeta (Ks n) (1+epsilon)).re /
        (2*(Module.finrank ℚ (Fs n) : ℝ))) atTop (𝓝 (Z epsilon)))
    (hboundary : Tendsto Z (𝓝[>] 0) (𝓝 C)) (hCT : C < T) :
    ∀ᶠ n in atTop, Real.log (relativeResidue (Ks n) (Fs n)) /
      (Module.finrank ℚ (Fs n) : ℝ) < T := by
  apply eventually_lt_of_boundary_comparison
    (fun n => Real.log (relativeResidue (Ks n) (Fs n))/(Module.finrank ℚ (Fs n) : ℝ))
    (fun n epsilon => Real.log (dedekindZeta (Ks n) (1+epsilon)).re /
      (2*(Module.finrank ℚ (Fs n) : ℝ))) Z (relativeGammaError ell)
    (by simpa using hboundary.add ((tendsto_relativeGammaError_zero ell).mono_left nhdsWithin_le_nhds))
    hz ?_ hCT
  intro epsilon hepsilon n
  have hfinite := normalized_log_relativeResidue_le_zeta_of_completion_le
    (Ks n) (Fs n) (hdegree n) ell hepsilon (hcomp epsilon hepsilon n)
  refine hfinite.trans (add_le_add le_rfl ?_)
  exact (le_abs_self _).trans (abs_relativeGammaCorrection_le ell epsilon
    (complexPlaceRatio_mem (Fs n)))

end Family

end UnitDistance.NumberFieldAnalysis
