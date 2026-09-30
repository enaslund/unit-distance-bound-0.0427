module

public import UnitDistance.HadamardFactorization
public import UnitDistance.HeckePairedProduct

@[expose] public section
set_option backward.privateInPublic true


/-! The paired real-axis product follows from an entire function's actual
divisor, inverse-square summability and subquadratic logarithmic growth. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set Complex
open scoped Topology BigOperators
namespace UnitDistance.HeckeAnalysis
open OverflowResidueRH

private theorem pairedQuadraticProduct_neg {ι : Type*} (zeros : ι → ℂ) (z : ℂ) :
    pairedQuadraticProduct zeros (-z) = pairedQuadraticProduct zeros z := by
  unfold pairedQuadraticProduct
  apply tprod_congr
  intro i
  simp [neg_div]

private theorem norm_canonicalEntireProduct_neg {ι : Type*} {zeros : ι → ℂ}
    (hinv : HadamardZeroInvSqSummability zeros) (P : HadamardNegationPairingData zeros)
    (m : ℕ) (z : ℂ) :
    ‖canonicalEntireProduct zeros m (-z)‖ = ‖canonicalEntireProduct zeros m z‖ := by
  simp only [canonicalEntireProduct, norm_mul, norm_pow, norm_neg,
    P.infiniteHadamardProduct_eq_paired hinv, pairedQuadraticProduct_neg]

private theorem canonicalEntireProduct_ne_zero_beyond_strip {ι : Type*} {zeros : ι → ℂ}
    (hinv : HadamardZeroInvSqSummability zeros) {a t : ℝ} (ha : 0 ≤ a)
    (hzeros : ∀ i, |(zeros i).re| ≤ a) (ht : a < t) (m : ℕ) :
    canonicalEntireProduct zeros m (t:ℂ) ≠ 0 := by
  apply mul_ne_zero (pow_ne_zero m (Complex.ofReal_ne_zero.mpr (lt_of_le_of_lt ha ht).ne'))
  apply hinv.infiniteProduct_ne_zero
  intro i hi
  have hr := congrArg Complex.re hi
  simp only [Complex.ofReal_re] at hr
  have hz := (abs_le.mp (hzeros i)).2
  linarith

/-- Evenness eliminates the real part of the affine exponential slope.
Only the norm is needed for real-axis monotonicity. -/
theorem exp_affine_canonical_product_slope_re_zero {F : ℂ → ℂ} {ι : Type*} {zeros : ι → ℂ}
    (hinv : HadamardZeroInvSqSummability zeros) (P : HadamardNegationPairingData zeros)
    (m : ℕ) (hF : ∀ z, F (-z) = F z) {a : ℝ} (ha : 0 ≤ a)
    (hzeros : ∀ i, |(zeros i).re| ≤ a) {A B : ℂ}
    (hfactor : ∀ z : ℂ, F z = Complex.exp (A+B*z)*canonicalEntireProduct zeros m z) :
    B.re = 0 := by
  let t : ℝ := a+1
  have ht : a < t := by dsimp [t]; linarith
  have hne := canonicalEntireProduct_ne_zero_beyond_strip hinv ha hzeros ht m
  have h := congrArg norm (hF (t:ℂ))
  rw [hfactor (-(t:ℂ)), hfactor (t:ℂ), norm_mul, norm_mul,
    norm_canonicalEntireProduct_neg hinv P] at h
  have hn : ‖canonicalEntireProduct zeros m (t:ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have he := mul_right_cancel₀ hn h
  rw [Complex.norm_exp, Complex.norm_exp] at he
  have hr := Real.exp_injective he
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, mul_zero, sub_zero] at hr
  have ht0 : 0 < t := lt_of_le_of_lt ha ht
  nlinarith

/-- The quadratic paired factors have the actual full genus-one product as
their limit, including at its zeros. -/
theorem hasProd_paired_factors {ι : Type*} {zeros : ι → ℂ}
    (hinv : HadamardZeroInvSqSummability zeros) (P : HadamardNegationPairingData zeros)
    (z : ℂ) :
    HasProd (fun j : P.half => 1-(z/P.repLoc j)^2)
      (infiniteHadamardProduct zeros z) := by
  let f : P.half × Bool → ℂ := fun p => hadamardGenus1Factor (zeros (P.pairEquiv p)) z
  have hf : HasProd f (infiniteHadamardProduct zeros z) :=
    P.pairEquiv.hasProd_iff.mpr (hinv.product_multipliable z).hasProd
  apply hf.prod_fiberwise
  intro j
  have hb : HasProd (fun b : Bool => f (j,b)) (∏ b : Bool, f (j,b)) :=
    hasProd_fintype _
  convert hb using 1
  simp only [Fintype.prod_bool, f, P.loc_true]
  simpa only [HadamardNegationPairingData.repLoc, mul_comm] using
    (hadamardGenus1Factor_mul_neg_location (z := z)
      (hinv.zero_ne (P.pairEquiv (j,false)))).symm

theorem tendsto_paired_norm_products {ι : Type*} {zeros : ι → ℂ}
    (hinv : HadamardZeroInvSqSummability zeros) (P : HadamardNegationPairingData zeros)
    (t : ℝ) :
    Tendsto (fun J : Finset P.half => ∏ j ∈ J, pairedFactor (P.repLoc j) t)
      atTop (𝓝 ‖infiniteHadamardProduct zeros (t:ℂ)‖) := by
  have h := (hasProd_paired_factors hinv P (t:ℂ)).norm
  have heq : (fun j : P.half => pairedFactor (P.repLoc j) t) =
      (fun j : P.half => ‖1-((t:ℂ)/P.repLoc j)^2‖) := by
    funext j
    exact pairedFactor_eq_norm (hinv.zero_ne (P.pairEquiv (j,false))) t
  change HasProd (fun j : P.half => pairedFactor (P.repLoc j) t) _
  rw [heq]
  exact h

theorem pairedPartialProduct_tendsto_norm_of_factorization
    {ι : Type*} {zeros : ι → ℂ} {F : ℂ → ℂ}
    (hinv : HadamardZeroInvSqSummability zeros) (P : HadamardNegationPairingData zeros)
    (m : ℕ) {A B : ℂ} (hB : B.re = 0)
    (hfactor : ∀ z : ℂ, F z = Complex.exp (A+B*z)*canonicalEntireProduct zeros m z)
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun J : Finset P.half => pairedPartialProduct P.repLoc m (Real.exp A.re) J t)
      atTop (𝓝 ‖F (t:ℂ)‖) := by
  have hnorm : ‖F (t:ℂ)‖ =
      Real.exp A.re*t^m*‖infiniteHadamardProduct zeros (t:ℂ)‖ := by
    rw [hfactor, norm_mul, Complex.norm_exp, canonicalEntireProduct, norm_mul, norm_pow]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, hB, zero_mul, add_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht]
    ring
  rw [hnorm]
  exact (tendsto_paired_norm_products hinv P t).const_mul (Real.exp A.re*t^m)

/-- An even entire function with this actual zero divisor and subquadratic
logarithmic growth has nondecreasing norm beyond its vertical zero strip. -/
theorem norm_monotoneOn_of_entire_divisor
    {F : ℂ → ℂ} {ι : Type*} {zeros : ι → ℂ}
    (hF : Differentiable ℂ F) (hinv : HadamardZeroInvSqSummability zeros)
    (hproper : HadamardZeroNormProper zeros) (P : HadamardNegationPairingData zeros)
    (m : ℕ)
    (hdivisor : ∀ z : ℂ, analyticOrderAt F z =
      (if z = 0 then (m : ENat) else 0)+(Nat.card {i : ι // zeros i = z} : ENat))
    (hgrowth : HasSubquadraticLogNormGrowthAtInfinity F)
    (heven : ∀ z, F (-z) = F z) {a : ℝ} (ha : 0 ≤ a)
    (hzeros : ∀ i, |(zeros i).re| ≤ a) :
    MonotoneOn (fun t : ℝ => ‖F (t:ℂ)‖) (Set.Ici a) := by
  obtain ⟨A,B,hfactor⟩ :=
    exists_exp_affine_canonical_product hF hinv hproper m hdivisor hgrowth
  have hB := exp_affine_canonical_product_slope_re_zero hinv P m heven ha hzeros hfactor
  apply monotoneOn_of_paired_product P.repLoc m ha (Real.exp_nonneg _)
    (fun j => hzeros (P.pairEquiv (j,false)))
  intro t ht
  exact pairedPartialProduct_tendsto_norm_of_factorization hinv P m hB hfactor (ha.trans ht)

end UnitDistance.HeckeAnalysis
