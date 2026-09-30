module

public import UnitDistance.SharperPairFixedBaseBridgeRun20260920
public import UnitDistance.PrimeDebitLogDerivative
public import UnitDistance.NumberFieldNumericInvariance

@[expose] public section
set_option backward.privateInPublic true


/-!
The exact planar sequence conclusion from one displayed fixed-field
inequality at the relaxed threshold supported by the sharper pair margin.
The nineteen-radical field is specified independently of the target.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace UnitDistance
open NumberField NumberFieldAnalysis Witness

/-- A literal numerical hypothesis on the canonical retained field. The
conclusion is the exact sequence target, with exponent 2083647/2000000. -/
theorem target_of_canonical_sharper_zeta_bound
    (hfinite : Real.log (dedekindZeta CanonicalRetained.Carrier
          ((1 + (1 / 12000 : ℝ) : ℝ) : ℂ)).re / (524288 : ℝ) +
        (1 / 12000 : ℝ) *
          ((logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
            (logDeriv (dedekindZeta CanonicalRetained.Carrier) 2).re /
              (524288 : ℝ)) < (42165819 : ℝ) / 1000000000) :
    Target := by
  apply target_of_retained_fixedBaseCeiling_sharperPair_run20260920
  rw [fixedBaseResidueCeiling_eq_zeta_logDeriv,
    ArithmeticRetained.retainedField_degree,
    sharperFixedBaseCeilingRun20260920_eq]
  have hden : (1000000000 : ℝ) = 10 ^ 9 := by norm_num
  simpa only [Nat.cast_ofNat,
    hden,
    dedekindZeta_eq_of_algEquiv CanonicalRetained.equiv,
    logDeriv_dedekindZeta_eq_of_algEquiv CanonicalRetained.equiv] using hfinite

end UnitDistance
