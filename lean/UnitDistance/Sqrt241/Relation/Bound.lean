/-
B-analogue of `UnitDistance/MaximalSigmaH2Bound.lean`: both arithmetic inputs of
`Relation/Reduction.lean` are discharged.
-/
module

public import UnitDistance.Sqrt241.Relation.Reduction
public import UnitDistance.Sqrt241.Relation.PairDetection
public import UnitDistance.Sqrt241.Relation.Character

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The relation bound: `dim H²(Gal(Ω_B/B), ℤ/2) ≤ 7`

`Ω_B` is the maximal pro-2 extension of `B = ℚ(√241)` unramified outside the
six primes above `2, 3, 5` (infinite places unrestricted). Its Galois group
has finite continuous `H²` with coefficients `ℤ/2` of dimension at most seven.
No hypothesis is assumed: the finite-place detection kernel of every finite
stage has at most two elements (`finiteDetectionPair_B`), and every finite
local family of quadratic characters is realized on inertia outside `S`
(`prescribedQuadraticInertia_B`).
-/

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.Relation

open ClassFieldTower.Cohomology UnitDistance.Sqrt241.Tower

/-- **Relation bound.** `H²(Gal(Ω_B/B), ℤ/2)` is finite-dimensional of dimension
at most seven. -/
theorem OmegaB_h2 :
    FiniteDimensional (ZMod 2) (continuousCohomologyZModPLifted 2 GBw 2) ∧
      Module.finrank (ZMod 2) (continuousCohomologyZModPLifted 2 GBw 2) ≤ 7 :=
  OmegaB_h2_of_inputs finiteDetectionPair_B prescribedQuadraticInertia_B

/-- The relation bound transported along any continuous group isomorphism (for
instance the bridge `Tower.bridge : Gal(Ω_B/B) ≃ₜ* G_B`). -/
theorem h2_le_seven_of_continuousMulEquiv
    {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    (e : GBw ≃ₜ* G') :
    FiniteDimensional (ZMod 2) (continuousCohomologyZModPLifted 2 G' 2) ∧
      Module.finrank (ZMod 2) (continuousCohomologyZModPLifted 2 G' 2) ≤ 7 := by
  obtain ⟨hfd, hrank⟩ := OmegaB_h2
  let L : continuousCohomologyZModPLifted 2 G' 2 ≃ₗ[ZMod 2]
      continuousCohomologyZModPLifted 2 GBw 2 :=
    continuousCohomologyZModPLiftedLinearEquiv e 2
  exact ⟨LinearEquiv.finiteDimensional L.symm, (LinearEquiv.finrank_eq L).le.trans hrank⟩

end UnitDistance.Sqrt241.Relation
