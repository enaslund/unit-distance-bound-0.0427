module

public import UnitDistance.TensorFiniteProfiles

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact finite-place tensor functional

The finite masses below are the proved ordinary local integrals of the actual
six-shell witness. Their product normalization is exactly the exponential of
the sum of the published local logarithmic functionals. Counting places of
each prescribed type then gives the degree-normalized finite profit.
-/

noncomputable section
open MeasureTheory
open scoped Classical BigOperators

namespace UnitDistance.Witness

/-- The independently evaluated actual local overlap integral. -/
def finiteOverlapMass (v : Fin 11) : ℝ :=
  residueCard v ^ periodPower v *
    (((periodPower v : ℝ)+1)*finiteSecond v^2 + 2*finiteSecond v*finiteTransition v)

theorem finiteOverlapMass_pos (v : Fin 11) : 0 < finiteOverlapMass v :=
  mul_pos (pow_pos (zero_lt_one.trans (residueCard_gt_one v)) _)
    ((energyLower_pos v).trans_le (energyLower_le v))

theorem finiteLogFunctional_eq_log_mass (v : Fin 11) :
    finiteLogFunctional v = Real.log (finiteOverlapMass v) -
      (1+increment)*Real.log (residueCard v^periodPower v*finiteLp v^2) := by
  have hQ := pow_pos (zero_lt_one.trans (residueCard_gt_one v)) (periodPower v)
  have hE := (energyLower_pos v).trans_le (energyLower_le v)
  rw [finiteOverlapMass, Real.log_mul hQ.ne' hE.ne',
    Real.log_mul hQ.ne' (sq_pos_of_pos (finiteLp_pos v)).ne']
  simp only [Real.log_pow, finiteLogFunctional]
  ring

section Integral
variable {G U : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
  [MeasurableSpace U] {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
  (v : Fin 11) (B : Local.BallSystem G μ (residueCard v))
  (S : B.ReciprocalSteps U) (ν : Measure U) [IsProbabilityMeasure ν]

/-- Identification with the literal Haar/counting/unit overlap integral. -/
theorem localShellProfile_profileEnergy (hs : ∀ n, Measurable (S.step n)) :
    B.profileEnergy S ν (localShellProfile v B) = finiteOverlapMass v := by
  rw [localShellProfile, B.shellProfile_energy_operator S ν
    (zero_lt_one.trans (residueCard_gt_one v)) hs]
  exact localShellProfile_energy v B S ν hs

end Integral

variable {ι : Type*} [Fintype ι] (v : ι → Fin 11)

/-- Product of the exact local overlap masses. -/
def tensorFiniteOverlapMass : ℝ := ∏ i, finiteOverlapMass (v i)

theorem tensorFiniteOverlapMass_pos : 0 < tensorFiniteOverlapMass v :=
  Finset.prod_pos (fun i _ => finiteOverlapMass_pos (v i))

/-- The actual tensor overlap divided by the p-mass to the required power. -/
def tensorFiniteFunctional : ℝ :=
  tensorFiniteOverlapMass v / (tensorFiniteMass v)^(1+increment)

theorem tensorFiniteFunctional_pos : 0 < tensorFiniteFunctional v :=
  div_pos (tensorFiniteOverlapMass_pos v)
    (Real.rpow_pos_of_pos (tensorFiniteMass_pos v) _)

theorem log_tensorFiniteFunctional :
    Real.log (tensorFiniteFunctional v) = ∑ i, finiteLogFunctional (v i) := by
  rw [tensorFiniteFunctional,
    Real.log_div (tensorFiniteOverlapMass_pos v).ne'
      (Real.rpow_pos_of_pos (tensorFiniteMass_pos v) _).ne',
    Real.log_rpow (tensorFiniteMass_pos v), tensorFiniteOverlapMass,
    Real.log_prod (fun i _ => (finiteOverlapMass_pos (v i)).ne'),
    tensorFiniteMass, Real.log_prod (fun i _ => by
      positivity [residueCard_gt_one (v i), finiteLp_pos (v i)])]
  simp_rw [finiteLogFunctional_eq_log_mass]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

theorem tensorFiniteFunctional_eq_exp :
    tensorFiniteFunctional v = Real.exp (∑ i, finiteLogFunctional (v i)) := by
  rw [← log_tensorFiniteFunctional, Real.exp_log (tensorFiniteFunctional_pos v)]

/-- Regrouping a sum by the actual finite fibers of the prime-type map. -/
theorem sum_by_primeType (f : Fin 11 → ℝ) :
    ∑ i, f (v i) = ∑ a, (Fintype.card {i // v i = a} : ℝ)*f a := by
  rw [← Fintype.sum_fiberwise v (fun i => f (v i))]
  apply Finset.sum_congr rfl
  intro a _
  simp only [(·.property : ∀ i : {i // v i = a}, v i.val = a)]
  simp

/-- Exact prescribed splitting multiplicities give the full degree-scaled
finite profit. The multiplicities are an arithmetic assertion about the
actual selected places and must be supplied by the field construction. -/
theorem sum_finiteLogFunctional_of_multiplicities (d : ℝ)
    (hmultiplicity : ∀ a, (Fintype.card {i // v i = a} : ℝ) *
      ((ramification a : ℝ)*residueDegree a) = d) :
    ∑ i, finiteLogFunctional (v i) = d*finiteProfit := by
  rw [sum_by_primeType, finiteProfit, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have he : ((ramification a : ℝ)*residueDegree a) ≠ 0 := by
    fin_cases a <;> norm_num [ramification, residueDegree]
  have h := hmultiplicity a
  apply (eq_div_iff he).mpr at h
  rw [h]
  ring

/-- The literal normalized finite tensor functional is precisely the
exponential factor used by the arithmetic amplitude. -/
theorem tensorFiniteFunctional_eq_exp_profit (d : ℝ)
    (hmultiplicity : ∀ a, (Fintype.card {i // v i = a} : ℝ) *
      ((ramification a : ℝ)*residueDegree a) = d) :
    tensorFiniteFunctional v = Real.exp (d*finiteProfit) := by
  rw [tensorFiniteFunctional_eq_exp, sum_finiteLogFunctional_of_multiplicities v d hmultiplicity]

theorem log_tensorFiniteFunctional_div_degree {d : ℝ} (hd : d ≠ 0)
    (hmultiplicity : ∀ a, (Fintype.card {i // v i = a} : ℝ) *
      ((ramification a : ℝ)*residueDegree a) = d) :
    Real.log (tensorFiniteFunctional v)/d = finiteProfit := by
  rw [tensorFiniteFunctional_eq_exp_profit v d hmultiplicity, Real.log_exp]
  field_simp

/-- The prescribed eleven local degrees give exactly 69/32 local blocks per
base-field degree. This finite rational identity also controls total variance. -/
theorem card_primeTypes_of_multiplicities (d : ℝ)
    (hmultiplicity : ∀ a, (Fintype.card {i // v i = a} : ℝ) *
      ((ramification a : ℝ)*residueDegree a) = d) :
    (Fintype.card ι : ℝ) = (69/32:ℝ)*d := by
  have h := sum_by_primeType v (fun _ => (1:ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [h]
  have hf (a : Fin 11) : (Fintype.card {i // v i = a} : ℝ) =
      d/((ramification a : ℝ)*residueDegree a) := by
    apply (eq_div_iff (show ((ramification a : ℝ)*residueDegree a) ≠ 0 by
      fin_cases a <;> norm_num [ramification, residueDegree])).mpr
    exact hmultiplicity a
  simp_rw [hf, div_eq_mul_inv, ← Finset.mul_sum]
  norm_num [Fin.sum_univ_succ, ramification, residueDegree]
  ring

end UnitDistance.Witness
