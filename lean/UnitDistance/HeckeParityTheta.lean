module

public import UnitDistance.HeckeOddGaussian
public import UnitDistance.Upstream.AINTLIB.CompletedZeta.ThetaEstimates

@[expose] public section
set_option backward.privateInPublic true


open Complex MeasureTheory Filter TopologicalSpace
open scoped FourierTransform Real Topology
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis

variable {ι : Type*} [Fintype ι]

theorem exists_pos_le_finite_weights {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ a i := by
  classical
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨1, zero_lt_one, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i, hi⟩ := Finite.exists_min a
    exact ⟨a i, ha i, hi⟩

noncomputable def heckeParityKernelCM (p : ι → Bool) (a : ι → ℝ) :
    C(EuclideanSpace ℝ ι, ℂ) := ⟨heckeParityKernel p a, continuous_heckeParityKernel p a⟩

theorem norm_heckeParityKernelCM_le (p : ι → Bool) {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (x : EuclideanSpace ℝ ι) :
    ‖heckeParityKernelCM p a x‖ ≤
      ‖DedekindResidue.weightedGaussianCM (fun i => a i/2) x‖ := by
  rw [DedekindResidue.norm_weightedGaussianCM_apply]
  exact norm_heckeParityKernel_le p ha x

theorem summable_norm_restrict_heckeParityKernel (p : ι → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (K : Compacts (EuclideanSpace ℝ ι)) :
    Summable fun v : L =>
      ‖((heckeParityKernelCM p a).comp (ContinuousMap.addRight (v : EuclideanSpace ℝ ι))).restrict
        (K : Set (EuclideanSpace ℝ ι))‖ := by
  obtain ⟨m, hm, hma⟩ := exists_pos_le_finite_weights ha
  have hg := DedekindResidue.summable_norm_restrict_weightedGaussianCM L
    (show 0 < m/2 by positivity) (fun i => div_le_div_of_nonneg_right (hma i) (by norm_num)) K
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => ?_) hg
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  refine (norm_heckeParityKernelCM_le p ha ((x : EuclideanSpace ℝ ι) + v)).trans ?_
  exact ContinuousMap.norm_coe_le_norm
    (((DedekindResidue.weightedGaussianCM (fun i => a i/2)).comp
      (ContinuousMap.addRight (v : EuclideanSpace ℝ ι))).restrict (K : Set (EuclideanSpace ℝ ι))) x

theorem summable_norm_heckeParityKernel (p : ι → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    Summable fun v : L => ‖heckeParityKernel p a (v : EuclideanSpace ℝ ι)‖ := by
  obtain ⟨m, hm, hma⟩ := exists_pos_le_finite_weights ha
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun v => norm_heckeParityKernel_le p ha v)
    (DedekindResidue.summable_real_weightedGaussian L (show 0 < m/2 by positivity)
      (fun i => div_le_div_of_nonneg_right (hma i) (by norm_num)))

theorem summable_heckeParityKernel (p : ι → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    Summable fun v : L => heckeParityKernel p a (v : EuclideanSpace ℝ ι) :=
  (summable_norm_heckeParityKernel p L ha).of_norm

theorem summable_fourier_heckeParityKernel (p : ι → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    Summable fun w : DedekindResidue.dualZLattice L =>
      𝓕 (heckeParityKernel p a) (w : EuclideanSpace ℝ ι) := by
  simp_rw [fourier_heckeParityKernel p ha]
  exact (summable_heckeParityKernel p (DedekindResidue.dualZLattice L)
    (fun i => inv_pos.mpr (ha i))).mul_left _

noncomputable def heckeParityTheta (p : ι → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) (a : ι → ℝ) : ℂ :=
  ∑' v : L, heckeParityKernel p a (v : EuclideanSpace ℝ ι)

/-- Actual lattice Poisson summation for the normalized parity kernel. -/
theorem heckeParityTheta_transform (p : ι → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    heckeParityTheta p L a =
      ((ZLattice.covolume L volume)⁻¹ : ℝ) •
        ((∏ i, (if p i then -Complex.I else 1) / (Real.sqrt (a i) : ℂ)) *
          heckeParityTheta p (DedekindResidue.dualZLattice L) (fun i => (a i)⁻¹)) := by
  have hP := DedekindResidue.tsum_eq_tsum_fourier_zlattice L
    (g := heckeParityKernelCM p a)
    (fun K => summable_norm_restrict_heckeParityKernel p L ha K)
    (summable_fourier_heckeParityKernel p L ha)
  change heckeParityTheta p L a =
    ((ZLattice.covolume L volume)⁻¹ : ℝ) •
      ∑' w : DedekindResidue.dualZLattice L, 𝓕 (heckeParityKernel p a) (w : EuclideanSpace ℝ ι) at hP
  rw [hP]
  simp_rw [fourier_heckeParityKernel p ha]
  rw [tsum_mul_left]
  rfl

/-- A uniform positive lower bound on all weights gives a summable Gaussian majorant. -/
theorem norm_heckeParityTheta_le_gaussian (p : ι → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    {a : ι → ℝ} {m : ℝ} (hm : 0 < m) (ha : ∀ i, m ≤ a i) :
    ‖heckeParityTheta p L a‖ ≤
      ∑' v : L, Real.exp (-Real.pi * ∑ i, (m/2) * ((v : EuclideanSpace ℝ ι) i)^2) := by
  have hapos : ∀ i, 0 < a i := fun i => hm.trans_le (ha i)
  have hsum := summable_norm_heckeParityKernel p L hapos
  refine (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum ?_
    (DedekindResidue.summable_real_weightedGaussian L (show 0 < m/2 by positivity)
      (fun i => le_refl _)))
  intro v
  exact (norm_heckeParityKernel_le p hapos v).trans
    (DedekindResidue.exp_weighted_le_exp_iso
      (fun i => div_le_div_of_nonneg_right (ha i) (by norm_num)) v)

/-- An odd coordinate removes the zero mode; the resulting theta has an explicit
uniform tail bound whenever all weights have a common lower bound. -/
theorem norm_heckeParityTheta_le_tail (p : ι → Bool)
    (hp : ∃ i, p i = true)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    {a : ι → ℝ} {A a₀ δ : ℝ} (ha₀ : 0 < a₀) (hA : a₀ ≤ A/2)
    (hδ : 0 < δ) (hδL : ∀ v : L, v ≠ 0 → δ ≤ ‖(v : EuclideanSpace ℝ ι)‖)
    (ha : ∀ i, A ≤ a i) :
    ‖heckeParityTheta p L a‖ ≤
      Real.exp (-Real.pi*(A/2-a₀)*δ^2) *
        ∑' v : L, Real.exp (-Real.pi * ∑ i, a₀ * ((v : EuclideanSpace ℝ ι) i)^2) := by
  have hapos : ∀ i, 0 < a i := fun i => by linarith [ha i]
  have hsum := summable_norm_heckeParityKernel p L hapos
  have hgauss := DedekindResidue.summable_real_weightedGaussian L ha₀
    (fun i => (hA.trans (div_le_div_of_nonneg_right (ha i) (by norm_num))))
  have hsum' : Summable (fun v : L => if v = 0 then 0 else
      Real.exp (-Real.pi * ∑ i, (a i/2) * ((v : EuclideanSpace ℝ ι) i)^2)) := by
    classical
    exact (hgauss.indicator {v : L | v ≠ 0}).congr (by intro v; simp [Set.indicator, ite_not])
  calc
    _ ≤ ∑' v : L, ‖heckeParityKernel p a (v : EuclideanSpace ℝ ι)‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' v : L, if v = 0 then 0 else
        Real.exp (-Real.pi * ∑ i, (a i/2) * ((v : EuclideanSpace ℝ ι) i)^2) := by
      apply hsum.tsum_le_tsum _ hsum'
      intro v
      by_cases hv : v = 0
      · subst v
        simp [heckeParityKernel_zero p a hp]
      · rw [if_neg hv]
        exact norm_heckeParityKernel_le p hapos v
    _ ≤ _ := DedekindResidue.tsum_ite_gaussian_tail L ha₀ hA hδ hδL
      (fun i => div_le_div_of_nonneg_right (ha i) (by norm_num))



theorem continuous_heckeParityKernel_weights (p : ι → Bool) (x : EuclideanSpace ℝ ι) :
    Continuous (fun a : ι → ℝ => heckeParityKernel p a x) := by
  unfold heckeParityKernel heckeNormalizedGaussian heckeRealGaussian
  apply continuous_finsetProd
  intro i hi
  cases p i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

theorem continuousAt_heckeParityTheta (p : ι → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    ContinuousAt (heckeParityTheta p L) a := by
  classical
  obtain ⟨m, hm, hma⟩ := exists_pos_le_finite_weights ha
  let S : Set (ι → ℝ) := {b | ∀ i, m/2 < b i}
  have hS : IsOpen S := by
    change IsOpen {b : ι → ℝ | ∀ i, m/2 < b i}
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply (i := i) : Continuous (fun b : ι → ℝ => b i)))
  have haS : a ∈ S := fun i => by linarith [hma i]
  refine (show ContinuousOn (heckeParityTheta p L) S from ?_).continuousAt (hS.mem_nhds haS)
  unfold heckeParityTheta
  apply continuousOn_tsum (f := fun (v : L) (b : ι → ℝ) =>
      heckeParityKernel p b (v : EuclideanSpace ℝ ι))
    (u := fun v : L => Real.exp (-Real.pi * ∑ i, (m/4) * ((v : EuclideanSpace ℝ ι) i)^2))
    (fun v => (continuous_heckeParityKernel_weights p v).continuousOn)
    (DedekindResidue.summable_real_weightedGaussian L (show 0 < m/4 by positivity)
      (fun i => le_refl _))
  intro v b hb
  have hbpos : ∀ i, 0 < b i := fun i => by have := hb i; linarith
  refine (norm_heckeParityKernel_le p hbpos v).trans ?_
  apply DedekindResidue.exp_weighted_le_exp_iso
  intro i
  have := hb i
  linarith

/-- Uniform exponential decay as all weights grow at least like a positive power. -/
theorem exists_heckeParityTheta_radial_bound (p : ι → Bool) (hp : ∃ i, p i = true)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    {r m : ℝ} (hr : 0 < r) (hm : 0 < m) :
    ∃ C k : ℝ, 0 ≤ C ∧ 0 < k ∧ ∀ t : ℝ, 1 ≤ t → ∀ a : ι → ℝ,
      (∀ i, m*t^r ≤ a i) →
      ‖heckeParityTheta p L a‖ ≤ C * Real.exp (-k*t^r) := by
  obtain ⟨δ, hδ, hδL⟩ := DedekindResidue.exists_pos_norm_le_of_discrete L
  let C : ℝ := ∑' v : L, Real.exp (-Real.pi * ∑ i, (m/4) * ((v : EuclideanSpace ℝ ι) i)^2)
  have hC : 0 ≤ C := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨C, Real.pi*m*δ^2/4, hC, by positivity, fun t ht a ha => ?_⟩
  have ht' : 1 ≤ t^r := Real.one_le_rpow ht hr.le
  have h := norm_heckeParityTheta_le_tail p hp L
    (show 0 < m/4 by positivity) (show m/4 ≤ (m*t^r)/2 by nlinarith) hδ hδL ha
  apply h.trans
  change Real.exp (-Real.pi*(m*t^r/2-m/4)*δ^2) * C ≤ C * Real.exp (-(Real.pi*m*δ^2/4)*t^r)
  rw [mul_comm _ C]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  have hdiff : 0 ≤ Real.pi*δ^2*(m*t^r-m) :=
    mul_nonneg (by positivity) (by nlinarith)
  nlinarith

theorem norm_heckeParity_prefactor (p : ι → Bool) {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) :
    ‖∏ i, (if p i then -Complex.I else 1) / (Real.sqrt (a i) : ℂ)‖ =
      (Real.sqrt (∏ i, a i))⁻¹ := by
  rw [norm_prod]
  have hfac (i : ι) : ‖(if p i then -Complex.I else 1) / (Real.sqrt (a i) : ℂ)‖ =
      (Real.sqrt (a i))⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    cases p i <;> simp
  simp_rw [hfac]
  rw [Finset.prod_inv_distrib, ← Real.sqrt_prod Finset.univ (fun i _ => (ha i).le)]



/-- The norm of the Poisson prefactor depends only on the product of the weights. -/
theorem norm_heckeParityTheta_transform (p : ι → Bool)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    ‖heckeParityTheta p L a‖ =
      |(ZLattice.covolume L volume)⁻¹| * (Real.sqrt (∏ i, a i))⁻¹ *
        ‖heckeParityTheta p (DedekindResidue.dualZLattice L) (fun i => (a i)⁻¹)‖ := by
  rw [heckeParityTheta_transform p L ha, norm_smul, norm_mul,
    norm_heckeParity_prefactor p ha, Real.norm_eq_abs, mul_assoc]

/-- Poisson summation turns a weight upper bound into inverse stretched-exponential
small-parameter decay. The product condition is the actual Hecke normalization. -/
theorem exists_heckeParityTheta_inverse_radial_bound (p : ι → Bool) (hp : ∃ i, p i = true)
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
    {r M : ℝ} (hr : 0 < r) (hM : 0 < M) :
    ∃ C k : ℝ, 0 ≤ C ∧ 0 < k ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ a : ι → ℝ,
      (∀ i, 0 < a i) → (∀ i, a i ≤ M*t^r) → (∏ i, a i) = t →
      ‖heckeParityTheta p L a‖ ≤ C*t^(-(1/2 : ℝ)) * Real.exp (-k*t^(-r)) := by
  obtain ⟨C, k, hC, hk, hbound⟩ := exists_heckeParityTheta_radial_bound p hp
    (DedekindResidue.dualZLattice L) hr (inv_pos.mpr hM)
  refine ⟨|(ZLattice.covolume L volume)⁻¹| * C, k, by positivity, hk,
    fun t ht ht1 a ha hupper hprod => ?_⟩
  have htinv : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  have htpos : 0 < t^r := Real.rpow_pos_of_pos ht r
  have hinv : ∀ i, M⁻¹*(t⁻¹)^r ≤ (a i)⁻¹ := by
    intro i
    rw [Real.inv_rpow ht.le, ← mul_inv]
    exact (inv_le_inv₀ (mul_pos hM htpos) (ha i)).mpr (hupper i)
  have h := hbound t⁻¹ htinv (fun i => (a i)⁻¹) hinv
  rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at h
  rw [norm_heckeParityTheta_transform p L ha, hprod, Real.sqrt_eq_rpow,
    ← Real.rpow_neg ht.le]
  calc
    _ ≤ |(ZLattice.covolume L volume)⁻¹| * t^(-(1/2 : ℝ)) *
        (C * Real.exp (-k*t^(-r))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

end UnitDistance.NumberFieldAnalysis
