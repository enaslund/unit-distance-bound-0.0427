/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch. The Mathlib
4.35 Denumerable import relocation is recorded in
third-party/yamaguchi/lean-v4.35-migration.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FinitePlaceH1CharacterLocalization
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.Concrete.SUnitPreparation.PrimePowerKernelCoordinates
public import Mathlib.LinearAlgebra.Pi

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false
/-!
# Finite-place ramification restriction of absolute H¹ characters

Absolute continuous mod-`p` characters first restrict to a finite-place decomposition subgroup
and then to its inertia subgroup.  The resulting maps are assembled over all finite places, and
their kernels recover the local unramified subspaces.
-/

open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP KummerTheory

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

local instance finitePlaceH1RamificationZModTopology :
    TopologicalSpace (ZMod p) := ⊥

local instance finitePlaceH1RamificationZModDiscreteTopology :
    DiscreteTopology (ZMod p) :=
  discreteTopology_bot _

local instance finitePlaceH1RamificationCharacterCommGroup :
    CommGroup (Multiplicative (ZMod p)) :=
  Multiplicative.commGroup

local instance finitePlaceH1RamificationCharacterTopology :
    TopologicalSpace (Multiplicative (ZMod p)) := ⊥

local instance finitePlaceH1RamificationCharacterDiscreteTopology :
    DiscreteTopology (Multiplicative (ZMod p)) :=
  discreteTopology_bot _
local instance finitePlaceH1RamificationCharacterContinuousMul :
    ContinuousMul (Multiplicative (ZMod p)) :=
  ⟨continuous_of_discreteTopology⟩

local instance finitePlaceH1RamificationCharacterContinuousInv :
    ContinuousInv (Multiplicative (ZMod p)) :=
  ⟨continuous_of_discreteTopology⟩

local instance finitePlaceH1RamificationCharacterTopologicalGroup :
    IsTopologicalGroup (Multiplicative (ZMod p)) :=
  ⟨⟩

local instance finitePlaceH1RamificationAddCommGroup
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    AddCommGroup (ContinuousH1ZMod (p := p) (G := H)) :=
  ContinuousAddMonoidHom.instAddCommGroup (Additive H) (ZMod p)

local instance finitePlaceH1RamificationModule
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := H)) :=
  continuousH1ZModModule

/-- Reinterpret a decomposition-group multiplicative character as an additive continuous
degree-one character. -/
def finitePlaceDecompositionCharacterToH1AddHom
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Additive
        (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
          Multiplicative (ZMod p)) →+
      ContinuousH1ZMod
        (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) where
  toFun chi := h1OfCharacter (Additive.toMul chi)
  map_zero' := by
    ext sigma
    rfl
  map_add' chi psi := by
    ext sigma
    rfl

/-- The character-to-`H¹` reinterpretation as a `ZMod p`-linear map. -/
noncomputable def finitePlaceDecompositionCharacterToH1
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceDecompositionContinuousZModCharacterModP F p v →ₗ[ZMod p]
      ContinuousH1ZMod
        (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) := by
  let characterModule :=
    finitePlaceDecompositionContinuousZModCharacterModP F p v
  letI : AddCommGroup
      (Additive
        (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
          Multiplicative (ZMod p))) := characterModule.isAddCommGroup
  letI : Module (ZMod p)
      (Additive
        (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
          Multiplicative (ZMod p))) := characterModule.isModule
  let f := finitePlaceDecompositionCharacterToH1AddHom F p v
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro a chi
        exact @ZMod.map_smul p
          (Additive
            (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
              Multiplicative (ZMod p)))
          (ContinuousH1ZMod
            (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v))
          (Additive
              (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
                Multiplicative (ZMod p)) →+
            ContinuousH1ZMod
              (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v))
          characterModule.isAddCommGroup
          (finitePlaceH1RamificationAddCommGroup
            (p := p) (H := finitePlaceAbsoluteDecompositionGroup F v))
          inferInstance inferInstance characterModule.isModule
          (finitePlaceH1RamificationModule
            (p := p) (H := finitePlaceAbsoluteDecompositionGroup F v))
          f a chi }

@[simp]
theorem finitePlaceDecompositionCharacterToH1_apply
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (chi : finitePlaceDecompositionContinuousZModCharacterModP F p v)
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    finitePlaceDecompositionCharacterToH1 F p v chi (Additive.ofMul sigma) =
      (Additive.toMul
        (show Additive
            (finitePlaceAbsoluteDecompositionGroup F v →ₜ*
              Multiplicative (ZMod p))
          from chi)) sigma :=
  rfl

/-- Restriction of an absolute character to the additive `H¹` of the decomposition subgroup. -/
noncomputable def finitePlaceAbsoluteH1DecompositionRestriction
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    absoluteContinuousZModCharacterModP F p →ₗ[ZMod p]
      ContinuousH1ZMod
        (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) :=
  (finitePlaceDecompositionCharacterToH1 F p v).comp
    (finitePlaceH1CharacterRestriction F p v)

@[simp]
theorem finitePlaceAbsoluteH1DecompositionRestriction_apply
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (chi : absoluteContinuousZModCharacterModP F p)
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    finitePlaceAbsoluteH1DecompositionRestriction F p v chi (Additive.ofMul sigma) =
      (Additive.toMul
        (show Additive
            (Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod p))
          from chi)) (finitePlaceAbsoluteDecompositionInclusion F v sigma) :=
  rfl

/-- The ramification component of an absolute character at `v`, obtained by restricting further
from decomposition to inertia. -/
noncomputable def finitePlaceAbsoluteH1RamificationRestriction
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    absoluteContinuousZModCharacterModP F p →ₗ[ZMod p]
      ContinuousH1ZMod
        (p := p) (G := finitePlaceAbsoluteInertiaSubgroup F v) :=
  (finitePlaceH1InertiaRestriction F p v).comp
    (finitePlaceAbsoluteH1DecompositionRestriction F p v)

@[simp]
theorem finitePlaceAbsoluteH1RamificationRestriction_apply
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (chi : absoluteContinuousZModCharacterModP F p)
    (sigma : finitePlaceAbsoluteInertiaSubgroup F v) :
    finitePlaceAbsoluteH1RamificationRestriction F p v chi (Additive.ofMul sigma) =
      (Additive.toMul
        (show Additive
            (Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod p))
          from chi))
        (finitePlaceAbsoluteDecompositionInclusion F v
          (finitePlaceAbsoluteInertiaInclusion F v sigma)) :=
  rfl

/-- The decomposition restriction is unramified exactly when its inertia component vanishes. -/
theorem finitePlaceAbsoluteH1DecompositionRestriction_mem_unramified_iff
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (chi : absoluteContinuousZModCharacterModP F p) :
    finitePlaceAbsoluteH1DecompositionRestriction F p v chi ∈
        finitePlaceUnramifiedH1 F p v ↔
      finitePlaceAbsoluteH1RamificationRestriction F p v chi = 0 := by
  rfl

/-- The dependent product of all finite-place inertia-character spaces. -/
abbrev FinitePlaceH1RamificationLocalizationTarget :=
  (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) →
    ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteInertiaSubgroup F v)

/-- All finite-place ramification components of an absolute continuous mod-`p` character. -/
noncomputable def finitePlaceAbsoluteH1RamificationRestrictionFamily :
    absoluteContinuousZModCharacterModP F p →ₗ[ZMod p]
      FinitePlaceH1RamificationLocalizationTarget F p :=
  LinearMap.pi fun v ↦ finitePlaceAbsoluteH1RamificationRestriction F p v

/-- Each component of the family is the ramification restriction at that place. -/
@[simp]
theorem finitePlaceAbsoluteH1RamificationRestrictionFamily_apply
    (chi : absoluteContinuousZModCharacterModP F p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteH1RamificationRestrictionFamily F p chi v =
      finitePlaceAbsoluteH1RamificationRestriction F p v chi :=
  rfl

/-- Evaluation of a family component is restriction along inertia and decomposition inclusions. -/
@[simp]
theorem finitePlaceAbsoluteH1RamificationRestrictionFamily_apply_apply
    (chi : absoluteContinuousZModCharacterModP F p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (sigma : finitePlaceAbsoluteInertiaSubgroup F v) :
    finitePlaceAbsoluteH1RamificationRestrictionFamily F p chi v
        (Additive.ofMul sigma) =
      (Additive.toMul
        (show Additive
            (Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod p))
          from chi))
        (finitePlaceAbsoluteDecompositionInclusion F v
          (finitePlaceAbsoluteInertiaInclusion F v sigma)) :=
  rfl

end ClassFieldTower.Martinet.Shafarevich
