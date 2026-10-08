module

public import UnitDistance.Sqrt241.V2.Tower
public import UnitDistance.Sqrt241.V2.Outer
public import UnitDistance.Sqrt241.V2.Census
public import UnitDistance.Sqrt241.Analytic.WideBridge
public import UnitDistance.Sqrt241.Wide.Character
public import UnitDistance.Sqrt241.Wide.Degree
public import UnitDistance.Sqrt241.Wide.LocalTypes
public import UnitDistance.Sqrt241.DyadicLink.Concrete

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Version 2: the planar theorem at exponent `20863/20000` from one inequality for `E_W`

The library endpoint of version 2. It combines

* the tower data `towerDataV2` of the 41-cap tower (`V2/Tower.lean`) and the outer theorem
  `V2.TowerData.target` (`V2/Outer.lean`);
* the root discriminant of the fixed base `M = input.M` (`DyadicLink.log_rootDiscriminant_input_M`,
  unchanged from version 1);
* the analytic bridge over the field `E_W = CanonicalWide.Carrier` of degree `8192`
  (`Analytic.fixedBaseCeiling_lt_425_of_wide_types`), with the map `E_W → M`
  (`Wide.wideToM`), the type `(8,4)` of `M` at `2` and the census of `M` at fifty split primes
  (`Retained.M_censusV2`).

The local data of `E_W` are `Wide.wideLocalTypes`; the only hypothesis of the endpoint
`target_of_wide_zeta_bound` is the displayed inequality `H_W` for the Dedekind zeta function of
`E_W`.
-/

noncomputable section

open NumberField

namespace UnitDistance.Sqrt241.V2

open Retained Analytic UnitDistance.NumberFieldAnalysis

/-- `M` has ramification index `8` and residue degree `4` at `2`. -/
theorem M_type_two :
    (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 input.M) = 8 ∧
      (rationalPrimeIdeal 2).inertiaDegIn (𝓞 input.M) = 4 :=
  sym_ramification_residue (K := input.M) M_kernelHat_sym M_fixing_le_core 0

/-- The census primes of the analytic bridge are among those of the version 2 census of `M`. -/
theorem wideCensus_subset : ∀ p ∈ wideCensusOne ∪ wideCensusTwo, p ∈ censusPrimesV2 := by
  decide

/-- The algebra structure of `M` over `E_W` given by `Wide.wideToM`. -/
abbrev wideAlgebraM : Algebra CanonicalWide.Carrier input.M :=
  (Wide.wideToM input).toRingHom.toAlgebra

/-- **The fixed-base ceiling of `M`** from the local data of `E_W` and the inequality `H_W`. -/
theorem fixedBaseCeiling_input_M (hE : WideLocalTypes CanonicalWide.Carrier)
    (H : Real.log (dedekindZeta CanonicalWide.Carrier ((1 + (1 / 4411 : ℝ) : ℝ) : ℂ)).re / 8192 +
        (1 / 4411 : ℝ) * ((Witness.logRD - Real.eulerMascheroniConstant -
          Real.log (4 * Real.pi)) / 4 -
            (logDeriv (dedekindZeta CanonicalWide.Carrier) 2).re / 8192) <
        50969 / 1000000) :
    fixedBaseResidueCeiling input.M Witness.logRD (1 / 4411) < Witness.ceiling := by
  let := wideAlgebraM
  have h := fixedBaseCeiling_lt_425_of_wide_types (E := CanonicalWide.Carrier) (M := input.M)
    Wide.finrank_field hE M_type_two
    (fun p hp => M_censusV2 p (wideCensus_subset p hp)) H
  simpa [Witness.ceiling] using h

/-- **The planar theorem at exponent `20863/20000`** from the local data of `E_W` and `H_W`. -/
theorem target_of_wide_types (hE : WideLocalTypes CanonicalWide.Carrier)
    (H : Real.log (dedekindZeta CanonicalWide.Carrier ((1 + (1 / 4411 : ℝ) : ℝ) : ℂ)).re / 8192 +
        (1 / 4411 : ℝ) * ((Witness.logRD - Real.eulerMascheroniConstant -
          Real.log (4 * Real.pi)) / 4 -
            (logDeriv (dedekindZeta CanonicalWide.Carrier) 2).re / 8192) <
        50969 / 1000000) :
    Target :=
  towerDataV2.target DyadicLink.log_rootDiscriminant_input_M (fixedBaseCeiling_input_M hE H)

/-- **The planar theorem at exponent `20863/20000` from the inequality `H_W`**, the endpoint
of version 2. -/
theorem target_of_wide_zeta_bound
    (hfinite : Real.log (dedekindZeta CanonicalWide.Carrier
          ((1 + (1 / 4411 : ℝ) : ℝ) : ℂ)).re / (8192 : ℝ) + (1 / 4411 : ℝ) *
        ((Witness.logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
          (logDeriv (dedekindZeta CanonicalWide.Carrier) 2).re / (8192 : ℝ)) <
        50969 / 1000000) :
    Target :=
  target_of_wide_types Wide.wideLocalTypes hfinite

end UnitDistance.Sqrt241.V2
