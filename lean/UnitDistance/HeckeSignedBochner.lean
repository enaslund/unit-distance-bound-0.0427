module

public import UnitDistance.HeckeBochnerParts
public import UnitDistance.HeckeSignedMellinTotal

@[expose] public section
set_option backward.privateInPublic true


/-! Ordinary signed theta functions and their genuine Bochner Mellin integrals,
reconstructed from the proved finite positive and negative lower masses. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped Real Classical nonZeroDivisors ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- The literal real signed theta, with the actual odd-norm filter. -/
def heckeOddSignedTheta (J : (Ideal (𝓞 K))⁰) (t : ℝ) (u : logSpace K) : ℝ :=
  ∑' v : idealZLattice K (FractionalIdeal.mk0 K J),
    heckeOddSignedTerm K t u (v : EuclideanSpace ℝ (index K))

/-- Torsion-normalized unit-box average of the real signed theta. -/
def heckeOddSignedG (J : (Ideal (𝓞 K))⁰) (t : ℝ) : ℝ :=
  (torsionOrder K : ℝ)⁻¹ *
    ∫ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
      heckeOddSignedTheta K J t u

/-- The actual normalized contribution of one odd integral ideal class representative. -/
def heckeOddSignedClassG (J : (Ideal (𝓞 K))⁰) (t : ℝ) : ℝ :=
  chiFourReal (Ideal.absNorm (J : Ideal (𝓞 K))) *
    heckeOddSignedG K J (heckeOddClassScale K J*t)

/-- The finite actual ideal-class sum; representatives are chosen with odd norm. -/
def heckeOddSignedTotalG (t : ℝ) : ℝ :=
  ∑ C : ClassGroup (𝓞 K), heckeOddSignedClassG K (heckeOddClassRep K C) t

theorem lintegral_scaled_heckeOddSignedLatticeMass_ne_top
    (r : K) (hr : r^2=7) (J : (Ideal (𝓞 K))⁰) (delta : ℝ)
    {c : ℝ} (hc : 0 < c) {σ : ℝ} (hσ : 1 < 2*σ) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1)) *
      heckeOddSignedLatticeMass K J delta (c*t)) ≠ ⊤ := by
  rw [lintegral_Ioi_mellin_scale hc σ _ (measurable_heckeOddSignedLatticeMass K J delta).aemeasurable]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (lintegral_mellin_heckeOddSignedLatticeMass_ne_top K r hr J delta hσ)

/-- Genuine weighted real Bochner reconstruction, allowing an arbitrary signed
coefficient and positive radial rescaling of the actual lattice theta. -/
theorem mellin_real_heckeOddSignedTheta_scaled
    (r : K) (hr : r^2=7) (J : (Ideal (𝓞 K))⁰) (delta : ℝ)
    {c : ℝ} (hc : 0 < c) {σ : ℝ} (hσ : 1 < 2*σ) :
    IntegrableOn (fun t => t^(σ-1) * (delta *
      ∫ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
        heckeOddSignedTheta K J (c*t) u)) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), t^(σ-1) * (delta *
      ∫ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
        heckeOddSignedTheta K J (c*t) u)) =
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1)) *
        heckeOddSignedLatticeMass K J delta (c*t)).toReal -
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1)) *
        heckeOddSignedLatticeMass K J (-delta) (c*t)).toReal := by
  let B := ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ)
  let f : idealZLattice K (FractionalIdeal.mk0 K J) → ℝ → logSpace K → ℝ :=
    fun v t u => delta * heckeOddSignedTerm K (c*t) u (v : EuclideanSpace ℝ (index K))
  have hf (v : idealZLattice K (FractionalIdeal.mk0 K J)) :
      Measurable (fun q : ℝ × logSpace K => f v q.1 q.2) := by
    exact (((continuous_heckeOddSignedTerm K v).comp
      ((continuous_const.mul continuous_fst).prodMk continuous_snd)).const_mul delta).measurable
  have hw : Measurable (fun t : ℝ => t^(σ-1)) := by fun_prop
  have hwn : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ t^(σ-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_of_lt ht) _
  have hpos : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1)) *
      (∫⁻ u in B, ∑' v, ENNReal.ofReal (f v t u))) ≠ ⊤ :=
    lintegral_scaled_heckeOddSignedLatticeMass_ne_top K r hr J delta hc hσ
  have hneg : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1)) *
      (∫⁻ u in B, ∑' v, ENNReal.ofReal (-f v t u))) ≠ ⊤ := by
    simpa only [heckeOddSignedLatticeMass, B, f, neg_mul] using
      lintegral_scaled_heckeOddSignedLatticeMass_ne_top K r hr J (-delta) hc hσ
  obtain ⟨hint, heq⟩ := weighted_iterated_tsum_reconstruction_of_parts
    (volume.restrict (Set.Ioi (0 : ℝ))) (volume.restrict B)
    (fun t : ℝ => t^(σ-1)) f hw hwn hf hpos hneg
  have hinner (t : ℝ) : (∫ u in B, ∑' v, f v t u) =
      delta * ∫ u in B, heckeOddSignedTheta K J (c*t) u := by
    unfold f heckeOddSignedTheta
    simp_rw [tsum_mul_left]
    rw [integral_const_mul]
  simp_rw [hinner] at hint heq
  refine ⟨hint, ?_⟩
  simpa only [heckeOddSignedLatticeMass, f, neg_mul] using heq


theorem mellin_real_heckeOddSignedG
    (r : K) (hr : r^2=7) (J : (Ideal (𝓞 K))⁰) {σ : ℝ} (hσ : 1 < 2*σ) :
    IntegrableOn (fun t => t^(σ-1)*heckeOddSignedG K J t) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), t^(σ-1)*heckeOddSignedG K J t) =
      (torsionOrder K : ℝ)⁻¹ *
        ((∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedLatticeMass K J 1 t).toReal -
         (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedLatticeMass K J (-1) t).toReal) := by
  obtain ⟨hint, heq⟩ := mellin_real_heckeOddSignedTheta_scaled K r hr J 1 (c := 1) zero_lt_one hσ
  simp only [one_mul] at hint heq
  have hfun : (fun t : ℝ => t^(σ-1)*heckeOddSignedG K J t) =
      fun t => (torsionOrder K : ℝ)⁻¹ * (t^(σ-1)*
        ∫ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
          heckeOddSignedTheta K J t u) := by
    funext t
    unfold heckeOddSignedG
    ring
  rw [hfun]
  exact ⟨hint.const_mul _, by rw [integral_const_mul, heq]⟩

theorem classMass_mellin_toReal (J : (Ideal (𝓞 K))⁰) (delta σ : ℝ) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedClassMass K J delta t).toReal =
      (torsionOrder K : ℝ)⁻¹ *
        (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1))*
          heckeOddSignedLatticeMass K J (delta*chiFourReal (Ideal.absNorm (J : Ideal (𝓞 K))))
            (heckeOddClassScale K J*t)).toReal := by
  have hshape (t : ℝ) : ENNReal.ofReal (t^(σ-1))*heckeOddSignedClassMass K J delta t =
      ENNReal.ofReal ((torsionOrder K : ℝ)⁻¹) * (ENNReal.ofReal (t^(σ-1))*
        heckeOddSignedLatticeMass K J (delta*chiFourReal (Ideal.absNorm (J : Ideal (𝓞 K))))
          (heckeOddClassScale K J*t)) := by
    unfold heckeOddSignedClassMass
    ring
  rw [lintegral_congr hshape, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem mellin_real_heckeOddSignedClassG
    (r : K) (hr : r^2=7) (J : (Ideal (𝓞 K))⁰) {σ : ℝ} (hσ : 1 < 2*σ) :
    IntegrableOn (fun t => t^(σ-1)*heckeOddSignedClassG K J t) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), t^(σ-1)*heckeOddSignedClassG K J t) =
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedClassMass K J 1 t).toReal -
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedClassMass K J (-1) t).toReal := by
  obtain ⟨hint, heq⟩ := mellin_real_heckeOddSignedTheta_scaled K r hr J
    (chiFourReal (Ideal.absNorm (J : Ideal (𝓞 K)))) (heckeOddClassScale_pos K J) hσ
  have hfun : (fun t : ℝ => t^(σ-1)*heckeOddSignedClassG K J t) =
      fun t => (torsionOrder K : ℝ)⁻¹ * (t^(σ-1)*
        (chiFourReal (Ideal.absNorm (J : Ideal (𝓞 K)))) *
        ∫ u in ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ),
          heckeOddSignedTheta K J (heckeOddClassScale K J*t) u) := by
    funext t
    unfold heckeOddSignedClassG heckeOddSignedG
    ring
  have hint' : IntegrableOn (fun t : ℝ => t^(σ-1)*heckeOddSignedClassG K J t) (Set.Ioi 0) := by
    rw [hfun]
    simpa only [IntegrableOn, mul_assoc] using hint.const_mul ((torsionOrder K : ℝ)⁻¹)
  refine ⟨hint', ?_⟩
  rw [hfun]
  simp_rw [mul_assoc]
  rw [integral_const_mul, heq, classMass_mellin_toReal, classMass_mellin_toReal]
  simp only [one_mul, neg_one_mul]
  ring


theorem totalMass_mellin_eq_sum (delta σ : ℝ) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedTotalMass K delta t) =
      ∑ C : ClassGroup (𝓞 K), ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1))*
        heckeOddSignedClassMass K (heckeOddClassRep K C) delta t := by
  have hp : Measurable (fun t : ℝ => ENNReal.ofReal (t^(σ-1))) := by fun_prop
  simp_rw [heckeOddSignedTotalMass, Finset.mul_sum]
  exact lintegral_finsetSum' _ (fun C _ => hp.aemeasurable.mul
    (measurable_heckeOddSignedClassMass K _ delta).aemeasurable)

theorem totalMass_mellin_toReal_eq_sum
    (r : K) (hr : r^2=7) (delta : ℝ) {σ : ℝ} (hσ : 1 < 2*σ) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedTotalMass K delta t).toReal =
      ∑ C : ClassGroup (𝓞 K),
        (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1))*
          heckeOddSignedClassMass K (heckeOddClassRep K C) delta t).toReal := by
  have hn := lintegral_mellin_heckeOddSignedTotalMass_ne_top K r hr delta hσ
  rw [totalMass_mellin_eq_sum] at hn ⊢
  exact ENNReal.toReal_sum (ENNReal.sum_ne_top.mp hn)

/-- The genuine Mellin integral of the complete real theta sum is the difference
of the already evaluated complete positive and negative lower masses. -/
theorem mellin_real_heckeOddSignedTotalG
    (r : K) (hr : r^2=7) {σ : ℝ} (hσ : 1 < 2*σ) :
    IntegrableOn (fun t => t^(σ-1)*heckeOddSignedTotalG K t) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), t^(σ-1)*heckeOddSignedTotalG K t) =
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedTotalMass K 1 t).toReal -
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t^(σ-1))*heckeOddSignedTotalMass K (-1) t).toReal := by
  have hfun : (fun t : ℝ => t^(σ-1)*heckeOddSignedTotalG K t) =
      fun t => ∑ C : ClassGroup (𝓞 K), t^(σ-1)*heckeOddSignedClassG K (heckeOddClassRep K C) t := by
    funext t
    simp only [heckeOddSignedTotalG, Finset.mul_sum]
  have hint (C : ClassGroup (𝓞 K)) := (mellin_real_heckeOddSignedClassG K r hr (heckeOddClassRep K C) hσ).1
  rw [hfun]
  refine ⟨integrable_finsetSum Finset.univ (fun C _ => hint C), ?_⟩
  rw [integral_finsetSum Finset.univ (fun C _ => hint C)]
  rw [Finset.sum_congr rfl (fun C _ =>
    (mellin_real_heckeOddSignedClassG K r hr (heckeOddClassRep K C) hσ).2), Finset.sum_sub_distrib]
  rw [totalMass_mellin_toReal_eq_sum K r hr 1 hσ, totalMass_mellin_toReal_eq_sum K r hr (-1) hσ]

/-- Real restriction of the complex Mellin transform, including totalized integrals. -/
theorem mellin_ofReal_real (f : ℝ → ℝ) (σ : ℝ) :
    mellin (fun t => (f t : ℂ)) (σ : ℂ) =
      ((∫ t in Set.Ioi (0 : ℝ), t^(σ-1)*f t : ℝ) : ℂ) := by
  unfold mellin
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show (σ : ℂ)-1 = ((σ-1 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (le_of_lt ht), smul_eq_mul, ← Complex.ofReal_mul]

end UnitDistance.NumberFieldAnalysis
