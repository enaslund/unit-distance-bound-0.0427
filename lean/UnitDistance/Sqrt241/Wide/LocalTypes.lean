module

public import UnitDistance.Sqrt241.Wide.Dyadic
public import UnitDistance.Sqrt241.Wide.CensusData

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# `WideLocalTypes` for the concrete field `E_W`

`CanonicalWide.Carrier` (the field `E_W` of degree `8192`, `finrank_field`) satisfies the local
interface of the version-2 analytic bridge: the dyadic part `wide_two` (`Wide/Dyadic.lean`) and
the census parts `wide_censusOne`, `wide_censusTwo` (`Wide/CensusData.lean`). Together with
`wideToM`, `E_W` embeds into the field `M` of every retained input.
-/

noncomputable section

namespace UnitDistance.Sqrt241.Wide

open NumberField UnitDistance.Sqrt241.Analytic

/-- **The local data of `E_W`.** -/
theorem wideLocalTypes : WideLocalTypes CanonicalWide.Carrier where
  two := wide_two
  censusOne := wide_censusOne
  censusTwo := wide_censusTwo

/-- **`E_W` in one statement**: degree `8192`, the local data of the analytic bridge, and the
embedding into `M`. -/
theorem wideField_summary :
    Module.finrank ℚ CanonicalWide.Carrier = 8192 ∧ WideLocalTypes CanonicalWide.Carrier ∧
      Nonempty (CanonicalWide.Carrier →ₐ[ℚ] Retained.input.M) :=
  ⟨finrank_field, wideLocalTypes, ⟨wideToM Retained.input⟩⟩

end UnitDistance.Sqrt241.Wide
