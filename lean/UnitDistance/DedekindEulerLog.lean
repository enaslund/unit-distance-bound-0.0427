module

public import UnitDistance.DedekindEuler

@[expose] public section
set_option backward.privateInPublic true


/-!
# Logarithms of the actual Dedekind Euler product

The summands below are the ordinary real prime-ideal Euler logarithms.
Their sum is proved to be the logarithm of Mathlib's actual zeta function,
on the real half-line above one. This is a prerequisite of the relative
Euler comparison, not an assumed field-family analytic ceiling.
-/

noncomputable section
open Filter Topology NumberField IsDedekindDomain
open scoped ComplexOrder

namespace UnitDistance.NumberFieldAnalysis

/-- The ordinary logarithmic Euler factor, with natural norm argument. -/
def primeEulerLog (q : ℕ) (s : ℝ) : ℝ := -Real.log (1 - (q : ℝ) ^ (-s))

theorem prime_rpow_lt_one {q : ℕ} (hq : 1 < q) {s : ℝ} (hs : 0 < s) :
    (q : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq) (neg_neg_of_pos hs)

theorem primeEulerLog_nonneg {q : ℕ} (hq : 1 < q) {s : ℝ} (hs : 0 < s) :
    0 ≤ primeEulerLog q s := by
  apply neg_nonneg.mpr
  exact Real.log_nonpos (by linarith [prime_rpow_lt_one hq hs])
    (by linarith [Real.rpow_nonneg (Nat.cast_nonneg q) (-s)])

/-- A positive product with positive limit can be passed through the real
logarithm directly on its finite partial products. -/
theorem hasSum_log_of_hasProd {ι : Type*} {f : ι → ℝ} {a : ℝ}
    (hf : ∀ i, 0 < f i) (ha : 0 < a) (hprod : HasProd f a) :
    HasSum (fun i => Real.log (f i)) (Real.log a) := by
  have h := (Real.continuousAt_log ha.ne').tendsto.comp hprod
  apply h.congr
  intro t
  exact Real.log_prod (fun i _ => (hf i).ne')

variable (K : Type*) [Field K] [NumberField K]

theorem primeIdeal_absNorm_gt_one (v : HeightOneSpectrum (𝓞 K)) :
    1 < Ideal.absNorm v.asIdeal := by
  have hn0 : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hn1 : Ideal.absNorm v.asIdeal ≠ 1 :=
    fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem dedekindZeta_real_eulerProduct {s : ℝ} (hs : 1 < s) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-s))⁻¹)
      (dedekindZeta K s).re := by
  have h := (DedekindEuler.dedekindZeta_eulerProduct K (s := (s : ℂ))
    (by simpa using hs)).norm
  rw [← Complex.re_eq_norm.mpr (dedekindZeta_positive K hs).le] at h
  apply h.congr
  intro t
  apply Finset.prod_congr rfl
  intro v _
  dsimp only
  have he : (((Ideal.absNorm v.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) =
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)) := by
    simpa using Complex.ofReal_cpow (Nat.cast_nonneg (Ideal.absNorm v.asIdeal)) (-s)
  rw [← he, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  exact inv_pos.mpr (sub_pos.mpr (prime_rpow_lt_one (primeIdeal_absNorm_gt_one K v)
    (by linarith)))

theorem dedekindZeta_log_hasSum {s : ℝ} (hs : 1 < s) :
    HasSum (fun v : HeightOneSpectrum (𝓞 K) => primeEulerLog (Ideal.absNorm v.asIdeal) s)
      (Real.log (dedekindZeta K s).re) := by
  have h := hasSum_log_of_hasProd
    (fun v : HeightOneSpectrum (𝓞 K) => inv_pos.mpr
      (sub_pos.mpr (prime_rpow_lt_one (primeIdeal_absNorm_gt_one K v) (by linarith))))
    (dedekindZeta_re_pos K hs) (dedekindZeta_real_eulerProduct K hs)
  simpa only [Real.log_inv, primeEulerLog] using h

end UnitDistance.NumberFieldAnalysis
