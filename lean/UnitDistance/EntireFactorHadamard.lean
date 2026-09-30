module

public import UnitDistance.HeckeEntireMonotonicity
public import Mathlib.Analysis.Analytic.IsolatedZeros

@[expose] public section
set_option backward.privateInPublic true


/-! A factor's canonical product is identified using growth of the two entire
functions in its factor identity; no growth hypothesis on that factor is needed. -/
noncomputable section
open Filter Set Complex
open scoped Topology
namespace UnitDistance.HeckeAnalysis
open OverflowResidueRH

theorem subquadraticLogNormGrowth_translate {f : ℂ → ℂ}
    (hf : HasSubquadraticLogNormGrowthAtInfinity f) (c : ℂ) :
    HasSubquadraticLogNormGrowthAtInfinity (fun z => f (z+c)) := by
  intro e he
  obtain ⟨R,hR,hbound⟩ := hf (e/4) (by positivity)
  refine ⟨max (R+‖c‖) (‖c‖+1), by positivity, ?_⟩
  intro z hz
  have hz₁ := (le_max_left (R+‖c‖) (‖c‖+1)).trans hz
  have hz₂ := (le_max_right (R+‖c‖) (‖c‖+1)).trans hz
  have htri : ‖z‖ ≤ ‖z+c‖+‖c‖ := by
    simpa using (norm_sub_le (z+c) c)
  have hlower : R ≤ ‖z+c‖ := by linarith
  have hupper : ‖z+c‖ ≤ 2*‖z‖ := by linarith [norm_add_le z c]
  have hsquare : ‖z+c‖^2 ≤ 4*‖z‖^2 := by nlinarith [norm_nonneg (z+c),norm_nonneg z]
  exact (hbound (z+c) hlower).trans (by nlinarith)

theorem exists_exp_affine_canonical_product_of_entire_factor
    {N D L : ℂ → ℂ} {ι : Type*} {zeros : ι → ℂ}
    (hN : Differentiable ℂ N) (hD : Differentiable ℂ D) (hL : Differentiable ℂ L)
    (hfactor : ∀ z, N z = D z*L z) (hDne : ∃ z, D z ≠ 0)
    (hNfinite : ∀ z, analyticOrderAt N z ≠ ⊤)
    (hNgrowth : HasSubquadraticLogNormGrowthAtInfinity N)
    (hDgrowth : HasSubquadraticLogNormGrowthAtInfinity D)
    (hinv : HadamardZeroInvSqSummability zeros) (hproper : HadamardZeroNormProper zeros)
    (m : ℕ)
    (hdivisor : ∀ z : ℂ, analyticOrderAt L z =
      (if z = 0 then (m : ENat) else 0)+(Nat.card {i : ι // zeros i = z} : ENat)) :
    ∃ A B : ℂ, ∀ z, L z = Complex.exp (A+B*z)*canonicalEntireProduct zeros m z := by
  have hP := canonicalEntireProduct_differentiable hinv hproper m
  have hDP := hD.mul hP
  have hord : ∀ z, analyticOrderAt N z =
      analyticOrderAt (D*canonicalEntireProduct zeros m) z := by
    intro z
    rw [show N = D*L from funext hfactor,
      analyticOrderAt_mul (hD.analyticAt z) (hL.analyticAt z),
      analyticOrderAt_mul (hD.analyticAt z) (hP.analyticAt z),
      hdivisor z, canonicalEntireProduct_analyticOrderAt hinv hproper]
  obtain ⟨A,B,heq⟩ := exists_exp_affine_mul_of_same_divisor hN hDP hord hNfinite
    hNgrowth (hDgrowth.mul (canonicalEntireProduct_growth hinv m))
  refine ⟨A,B,?_⟩
  obtain ⟨z₀,hz₀⟩ := hDne
  have hnear : ∀ᶠ z in 𝓝 z₀, D z ≠ 0 := hD.continuous.continuousAt.eventually_ne hz₀
  have hlocal : L =ᶠ[𝓝 z₀] (fun z => Complex.exp (A+B*z)*canonicalEntireProduct zeros m z) := by
    filter_upwards [hnear] with z hz
    apply mul_left_cancel₀ hz
    rw [← hfactor, heq]
    change Complex.exp (A+B*z)*(D z*canonicalEntireProduct zeros m z) = _
    ring
  have hright : Differentiable ℂ (fun z => Complex.exp (A+B*z)*canonicalEntireProduct zeros m z) := by
    exact ((differentiable_const A).add ((differentiable_const B).mul differentiable_id)).cexp.mul hP
  exact fun z => congrFun (AnalyticOnNhd.eq_of_eventuallyEq
    (fun z _ => hL.analyticAt z : AnalyticOnNhd ℂ L univ)
    (fun z _ => hright.analyticAt z) hlocal) z

theorem norm_monotoneOn_of_entire_factor
    {N D L : ℂ → ℂ} {ι : Type*} {zeros : ι → ℂ}
    (hN : Differentiable ℂ N) (hD : Differentiable ℂ D) (hL : Differentiable ℂ L)
    (hfactor : ∀ z, N z = D z*L z) (hDne : ∃ z, D z ≠ 0)
    (hNfinite : ∀ z, analyticOrderAt N z ≠ ⊤)
    (hNgrowth : HasSubquadraticLogNormGrowthAtInfinity N)
    (hDgrowth : HasSubquadraticLogNormGrowthAtInfinity D)
    (hinv : HadamardZeroInvSqSummability zeros) (hproper : HadamardZeroNormProper zeros)
    (P : HadamardNegationPairingData zeros) (m : ℕ)
    (hdivisor : ∀ z : ℂ, analyticOrderAt L z =
      (if z = 0 then (m : ENat) else 0)+(Nat.card {i : ι // zeros i = z} : ENat))
    (heven : ∀ z, L (-z) = L z) {a : ℝ} (ha : 0 ≤ a)
    (hzeros : ∀ i, |(zeros i).re| ≤ a) :
    MonotoneOn (fun t : ℝ => ‖L (t:ℂ)‖) (Set.Ici a) := by
  obtain ⟨A,B,hLfactor⟩ := exists_exp_affine_canonical_product_of_entire_factor
    hN hD hL hfactor hDne hNfinite hNgrowth hDgrowth hinv hproper m hdivisor
  have hB := exp_affine_canonical_product_slope_re_zero hinv P m heven ha hzeros hLfactor
  apply monotoneOn_of_paired_product P.repLoc m ha (Real.exp_nonneg _)
    (fun j => hzeros (P.pairEquiv (j,false)))
  intro t ht
  exact pairedPartialProduct_tendsto_norm_of_factorization hinv P m hB hLfactor (ha.trans ht)

end UnitDistance.HeckeAnalysis
