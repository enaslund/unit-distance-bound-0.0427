module

public import UnitDistance.Sqrt241.ProP.MaximalProPGroup
public import UnitDistance.Sqrt241.ProP.AbsoluteProPRestriction
public import UnitDistance.Sqrt241.ProP.AbsoluteProPUnramified
public import UnitDistance.Sqrt241.ProP.AbsoluteProPFactor
public import UnitDistance.Sqrt241.ProP.ProPStageRestriction
public import UnitDistance.Sqrt241.ProP.ProPStageLocalConditions
public import UnitDistance.Sqrt241.Base.Selmer

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The maximal pro-2 extension `Ω_B` of `B = ℚ(√241)` unramified outside `S`

`S = Base.S` is the set of the six primes of `B` above `2, 3, 5` (those
containing `30`); `Base.SFin` lists them as `vP2, vP2', vP3, vP3', vP5, vP5'`
(`Base/Selmer.lean`). `OmegaB` is the compositum, inside `AlgebraicClosure B`, of all
finite Galois 2-extensions of `B` unramified at every finite place outside `S`; infinite
places are unrestricted. Its Galois group `GBw = Gal(Ω_B/B)` is pro-2, and the
finite Galois subextensions of `Ω_B` are exactly the admissible layers.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.Tower

open Base

/-- The fixed algebraic closure of `B` (the "B-world"). -/
abbrev Bbar : Type := AlgebraicClosure B

/-- The maximal pro-2 extension of `B` unramified outside `S` (infinite places
unrestricted), inside `AlgebraicClosure B`. -/
def OmegaB : IntermediateField B Bbar := ProP.maximalProPOutside B 2 S

instance OmegaB_isGalois : IsGalois B OmegaB :=
  ProP.maximalProPOutside_isGalois B 2 S

/-- The B-world group `Gal(Ω_B/B)`. -/
abbrev GBw : Type := OmegaB ≃ₐ[B] OmegaB

instance GBw_t2Space : T2Space GBw :=
  ProP.maximalProPOutside_galoisGroup_t2Space B 2 S

/-- `Gal(Ω_B/B)` is pro-2. -/
theorem OmegaB_hasPGroupOpenNormalBasis :
    ProCGroups.ProC.HasPGroupOpenNormalBasis 2 GBw := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ProP.maximalProPOutside_galoisGroup_hasPGroupOpenNormalBasis B 2 S

/-- The finite Galois subextensions of `Ω_B` are exactly the admissible layers:
finite Galois 2-extensions of `B` unramified at all finite places outside `S`. -/
theorem finiteLayer_le_OmegaB_iff
    (E : FiniteGaloisIntermediateField B Bbar) :
    E.toIntermediateField ≤ OmegaB ↔ ProP.IsAdmissibleFiniteLayer B 2 S E :=
  (ProP.isAdmissibleFiniteLayer_iff_le_maximalProPOutside B 2 S E).symm

/-- Restriction `Gal(B̄/B) → Gal(Ω_B/B)`, continuous and surjective. -/
def absoluteToOmegaB : Field.absoluteGaloisGroup B →ₜ* GBw :=
  ProP.absoluteToMaximalProPOutside B 2 S

theorem absoluteToOmegaB_surjective : Function.Surjective absoluteToOmegaB :=
  ProP.absoluteToMaximalProPOutside_surjective B 2 S

/-- Absolute inertia at a finite place outside `S` dies in `Gal(Ω_B/B)`. -/
theorem absoluteToOmegaB_inertia (v : HeightOneSpectrum (𝓞 B)) (hv : v ∉ S)
    (σ : ClassFieldTower.Martinet.Shafarevich.finitePlaceAbsoluteInertiaSubgroup B v) :
    absoluteToOmegaB
      (ClassFieldTower.Martinet.Shafarevich.finitePlaceAbsoluteDecompositionInclusion B v σ.1) =
      1 :=
  ProP.absoluteToMaximalProPOutside_inertia B 2 S v hv σ

end UnitDistance.Sqrt241.Tower
