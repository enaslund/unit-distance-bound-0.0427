module

public import UnitDistance.PrimeFiberFactors
public import UnitDistance.HeckeNormCharacterEuler
public import UnitDistance.FiniteEulerDenominator

@[expose] public section
set_option backward.privateInPublic true


/-! Assembly of actual prime Euler factors with a finite unitary correction. -/
noncomputable section
namespace UnitDistance.NumberFieldAnalysis
open NumberField IsDedekindDomain UnitDistance.HeckeAnalysis
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

theorem norm_primeNorm_cpow_lt_one (p : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 0 < s.re) :
    ‖(Ideal.absNorm p.asIdeal:ℂ)^(-s)‖ < 1 := by
  have hq := primeIdeal_absNorm_gt_one F p
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < Ideal.absNorm p.asIdeal), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq) (by linarith)

/-- The identity theorem needs this finite correction in its entire exponential form. -/
theorem finiteEulerDenominator_primeNorm_eq (S : Finset (HeightOneSpectrum (𝓞 F)))
    (chi : HeightOneSpectrum (𝓞 F) → ℂ) (s : ℂ) :
    finiteEulerDenominator S (fun p => (Ideal.absNorm p.asIdeal:ℝ)) chi s =
      ∏ p ∈ S, (1-chi p*(Ideal.absNorm p.asIdeal:ℂ)^(-s)) := by
  apply Finset.prod_congr rfl
  intro p _
  have hq := primeIdeal_absNorm_gt_one F p
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)),
    ← Complex.natCast_log]
  rw [mul_comm (Real.log (Ideal.absNorm p.asIdeal):ℂ) (-s)]

/-- Global ideal-series identity from verified local factor identities. -/
theorem dedekindZeta_mul_finiteEuler_of_factors
    (S : Finset (HeightOneSpectrum (𝓞 F))) (chi : HeightOneSpectrum (𝓞 F) → ℂ)
    (hchi : ∀ p ∈ S, ‖chi p‖=1)
    (hzero : ∀ p ∈ S, chiFourComplex (Ideal.absNorm p.asIdeal)=0)
    {s : ℂ} (hs : 1 < s.re)
    (hlocal : ∀ p : HeightOneSpectrum (𝓞 F),
      (∏ Q : PrimeFiber F K p, (1-(Ideal.absNorm Q.val.asIdeal:ℂ)^(-s))) =
        (1-(Ideal.absNorm p.asIdeal:ℂ)^(-s)) *
          (if p ∈ S then 1-chi p*(Ideal.absNorm p.asIdeal:ℂ)^(-s)
            else 1-chiFourComplex (Ideal.absNorm p.asIdeal)*(Ideal.absNorm p.asIdeal:ℂ)^(-s))) :
    dedekindZeta K s * finiteEulerDenominator S (fun p => (Ideal.absNorm p.asIdeal:ℝ)) chi s =
      dedekindZeta F s * chiFourIdealSeries F s := by
  let d : HeightOneSpectrum (𝓞 F) → ℂ := fun p =>
    if p ∈ S then 1-chi p*(Ideal.absNorm p.asIdeal:ℂ)^(-s) else 1
  have hD : HasProd d (∏ p ∈ S, (1-chi p*(Ideal.absNorm p.asIdeal:ℂ)^(-s))) := by
    have h : HasProd d (∏ p ∈ S, d p) :=
      hasProd_prod_of_ne_finset_one (s := S) (f := d)
        (fun p hp => by simp only [d,hp,↓reduceIte])
    convert h using 1
    apply Finset.prod_congr rfl
    intro p hp
    simp only [d,hp,↓reduceIte]
  have hK0 : HasProd (fun Q : HeightOneSpectrum (𝓞 K) =>
      (1-(Ideal.absNorm Q.asIdeal:ℂ)^(-s))⁻¹) (dedekindZeta K s) :=
    DedekindEuler.dedekindZeta_eulerProduct K hs
  have hsig := ((Equiv.sigmaFiberEquiv
    (fun Q : HeightOneSpectrum (𝓞 K) => Q.under (𝓞 F))).hasProd_iff).mpr hK0
  have hK : HasProd (fun p : HeightOneSpectrum (𝓞 F) =>
      ∏ Q : PrimeFiber F K p, (1-(Ideal.absNorm Q.val.asIdeal:ℂ)^(-s))⁻¹)
      (dedekindZeta K s) :=
    hsig.sigma (fun p => hasProd_fintype
      (fun Q : PrimeFiber F K p => (1-(Ideal.absNorm Q.val.asIdeal:ℂ)^(-s))⁻¹))
  have hKD := hK.mul hD
  have hFC := (DedekindEuler.dedekindZeta_eulerProduct F hs).mul (chiFourIdealSeries_eulerProduct F hs)
  rw [finiteEulerDenominator_primeNorm_eq]
  apply hKD.unique
  apply hFC.congr_fun
  intro p
  symm
  change (1-(Ideal.absNorm p.asIdeal:ℂ)^(-s))⁻¹ *
      (1-chiFourComplex (Ideal.absNorm p.asIdeal)*(Ideal.absNorm p.asIdeal:ℂ)^(-s))⁻¹ =
    (∏ Q : PrimeFiber F K p, (1-(Ideal.absNorm Q.val.asIdeal:ℂ)^(-s))⁻¹)*d p
  rw [Finset.prod_inv_distrib, hlocal p]
  by_cases hp : p ∈ S
  · have hd : 1-chi p*(Ideal.absNorm p.asIdeal:ℂ)^(-s) ≠ 0 := by
      apply IsUnit.ne_zero
      apply isUnit_one_sub_of_norm_lt_one
      rw [norm_mul,hchi p hp,one_mul]
      exact norm_primeNorm_cpow_lt_one F p (by linarith)
    simp only [hp,↓reduceIte,d,hzero p hp,zero_mul,sub_zero,inv_one,mul_one]
    simp only [mul_inv_rev]
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  · simp only [hp,↓reduceIte,d,mul_one,mul_inv_rev]
    exact mul_comm _ _

end UnitDistance.NumberFieldAnalysis
