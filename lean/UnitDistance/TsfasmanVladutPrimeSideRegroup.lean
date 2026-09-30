module

public import UnitDistance.TsfasmanVladutPrimeRegroup
public import UnitDistance.TsfasmanVladutPrimeSide

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual prime-side regrouping for the Tsfasman–Vlăduţ kernel

The literal series in `TsfasmanVladutPrimeRegroup` is identified with the
explicit formula's actual `primeSideH`, and its summability is discharged
by the proved prime-side estimate. No convergence hypothesis remains.
-/

noncomputable section
open NumberField Filter Topology
open scoped BigOperators

namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

theorem tvPrimeOrigin_eq_primeSideH (e a : ℝ) :
    tvPrimeOrigin K e a = DedekindResidue.primeSideH K a (tvKernel e) 0 := by
  simp only [tvPrimeOrigin, tvPrimePairTerm, DedekindResidue.primeSideH, zero_add, neg_mul]

theorem summable_tvPrimePairTerm {e a : ℝ} (ha : 0 < a) (hae : a ≤ e) :
    Summable (tvPrimePairTerm K e a) := by
  change Summable (fun pk => tvPrimePairTerm K e a pk)
  simpa only [tvPrimePairTerm, tvPrimeSideWeight, tvWeighted, tvPrimeSideShift, zero_add, neg_mul] using
    summable_primeSideH_tvKernel K ha hae 0

/-- The complete actual norm-count series equals the actual prime side,
with convergence proved from the kernel's decay. -/
theorem primeSideH_tvKernel_primeNormCount_hasSum {e a : ℝ}
    (ha : 0 < a) (hae : a ≤ e) :
    HasSum (fun q : ℕ => (primeNormCount K (q+2) : ℝ)*tvPrimeWeight e (q+2))
      (DedekindResidue.primeSideH K a (tvKernel e) 0).re := by
  rw [← tvPrimeOrigin_eq_primeSideH]
  exact tvPrimeOrigin_primeNormCount_hasSum K (ha.le.trans hae)
    (summable_tvPrimePairTerm K ha hae)

/-- Every finite collection of actual prime norms is bounded by the genuine
explicit-formula prime side at zero. -/
theorem finite_primeNormCount_tvPrimeWeight_le_primeSideH {e a : ℝ}
    (ha : 0 < a) (hae : a ≤ e) (J : Finset ℕ) :
    (∑ q ∈ J, (primeNormCount K (q+2) : ℝ)*tvPrimeWeight e (q+2)) ≤
      (DedekindResidue.primeSideH K a (tvKernel e) 0).re := by
  rw [← tvPrimeOrigin_eq_primeSideH]
  exact finite_primeNormCount_tvPrimeWeight_le_origin K (ha.le.trans hae)
    (summable_tvPrimePairTerm K ha hae) J

end UnitDistance.NumberFieldAnalysis
