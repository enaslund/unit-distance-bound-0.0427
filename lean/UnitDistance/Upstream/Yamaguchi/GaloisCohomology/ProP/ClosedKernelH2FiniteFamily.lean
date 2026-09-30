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

public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.FiniteStageTransgression
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.FiniteStageTransgressionKernel
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.FiniteStageTransgressionLinear
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.FiniteTransgressionLinear
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.TrivialZModP
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Cohomology.InvariantCharacterFiniteFamily
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Cohomology.InvariantCharacterFiniteStage
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProC.InverseLimits.Predicates
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProP.ContinuousH1
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProP.FrattiniPowers
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Pi
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Instances.ZMod

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Independent characters of a closed kernel and degree-two cohomology

A finite independent family of ambient-invariant characters of a closed normal subgroup
contained in the power--commutator subgroup gives independent classes in the quotient's H².
No presentation or finite normal generating family is assumed.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC ClassFieldTower.Cohomology

noncomputable section

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

local instance kernelFamilyCoefficientTopology : TopologicalSpace (ZMod p) := ⊥
local instance kernelFamilyCoefficientDiscrete : DiscreteTopology (ZMod p) :=
  discreteTopology_bot _

local instance kernelFamilyH1Module
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := H)) := continuousH1ZModModule

/-- Independent invariant characters of a closed subgroup in the Frattini subgroup
are bounded in number by the quotient's degree-two cohomology dimension. -/
theorem invariant_character_family_card_le_finrank_h2
    {ι : Type v} [Fintype ι]
    (hF : HasPGroupOpenNormalBasis p F)
    (R : ClosedSubgroup F) [R.Normal]
    (hR : (R : Subgroup F) ≤ closedPowerCommutator p F)
    (χ : ι → R →ₜ* Multiplicative (ZMod p))
    (hχinv : ∀ (i : ι) (f : F) (r : R), χ i (MulAut.conjNormal f r) = χ i r)
    (hχind : LinearIndependent (ZMod p) (fun i ↦ fun r : R ↦ (χ i r).toAdd))
    [FiniteDimensional (ZMod p)
      (continuousCohomologyZModPLifted p (F ⧸ (R : Subgroup F)) 2)] :
    Fintype.card ι ≤ Module.finrank (ZMod p)
      (continuousCohomologyZModPLifted p (F ⧸ (R : Subgroup F)) 2) := by
  classical
  letI : IsTopologicalGroup R :=
    inferInstanceAs (IsTopologicalGroup (R : Subgroup F))
  letI h1Group : AddCommGroup (ContinuousH1ZMod (p := p) (G := R)) :=
    ContinuousAddMonoidHom.instAddCommGroup (Additive R) (ZMod p)
  letI h1Module : Module (ZMod p) (ContinuousH1ZMod (p := p) (G := R)) :=
    continuousH1ZModModule
  letI coefficientModule : Module (ZMod p) (ZMod p) := Semiring.toModule
  letI characterFunctionModule : Module (ZMod p) (R → ZMod p) :=
    Pi.Function.module R (ZMod p) (ZMod p)
  obtain ⟨U, χbar, hpull, hχbarInv, _hcomb⟩ :=
    exists_finiteStage_invariant_character_family hF R χ hχinv
  let vχ : ι → InvariantFiniteCharacter (p := p) (finiteStageImage R U) :=
    fun i ↦ ⟨Additive.ofMul (χbar i), hχbarInv i⟩
  let w : ι → continuousCohomologyZModPLifted p (F ⧸ (R : Subgroup F)) 2 :=
    fun i ↦ inflatedFiniteTransgressionLinearMap R U (vχ i)
  have hw : LinearIndependent (ZMod p) w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    let ηsum : ContinuousH1ZMod (p := p) (G := R) :=
      ∑ i, a i • h1OfCharacter (χ i)
    let χsum : R →ₜ* Multiplicative (ZMod p) := characterOfH1 ηsum
    let vSum : InvariantFiniteCharacter (p := p) (finiteStageImage R U) :=
      ∑ i, a i • vχ i
    have hvalue (r : R) : (χsum r).toAdd = ∑ i, a i * (χ i r).toAdd := by
      let ev : ContinuousH1ZMod (p := p) (G := R) →+ ZMod p :=
        { toFun := fun η ↦ η (Additive.ofMul r)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      change ev ηsum = _
      rw [show ηsum = ∑ i, a i • h1OfCharacter (χ i) by rfl, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have h := @ZMod.map_smul p
        (ContinuousH1ZMod (p := p) (G := R)) (ZMod p)
        (ContinuousH1ZMod (p := p) (G := R) →+ ZMod p)
        h1Group inferInstance inferInstance inferInstance
        h1Module coefficientModule ev (a i) (h1OfCharacter (χ i))
      change ev (a i • h1OfCharacter (χ i)) =
        a i * (χ i r).toAdd at h
      exact h
    have hpullSum :
        (InvariantFiniteCharacter.toMonoidHom (finiteStageImage R U) vSum).comp
          (finiteStageImageMap R U) = χsum.toMonoidHom := by
      apply MonoidHom.ext
      intro r
      apply Multiplicative.toAdd.injective
      change (InvariantFiniteCharacter.toMonoidHom (finiteStageImage R U) vSum
        (finiteStageImageMap R U r)).toAdd = (χsum r).toAdd
      rw [hvalue]
      let ev : InvariantFiniteCharacter (p := p) (finiteStageImage R U) →+ ZMod p :=
        { toFun := fun η ↦ (InvariantFiniteCharacter.toMonoidHom
            (finiteStageImage R U) η (finiteStageImageMap R U r)).toAdd
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      change ev vSum = _
      rw [show vSum = ∑ i, a i • vχ i by rfl, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have h := @ZMod.map_smul p
        (InvariantFiniteCharacter (p := p) (finiteStageImage R U)) (ZMod p)
        (InvariantFiniteCharacter (p := p) (finiteStageImage R U) →+ ZMod p)
        inferInstance inferInstance inferInstance inferInstance
        inferInstance coefficientModule ev (a i) (vχ i)
      have hir := DFunLike.congr_fun (hpull i) r
      calc
        ev (a i • vχ i) = a i * ev (vχ i) := by
          change ev (a i • vχ i) = a i * ev (vχ i) at h
          exact h
        _ = a i * ((χbar i) (finiteStageImageMap R U r)).toAdd := rfl
        _ = a i * (χ i r).toAdd :=
          congrArg (fun z : Multiplicative (ZMod p) ↦ a i * z.toAdd) hir
    have hχsumInv (f : F) (r : R) : χsum (MulAut.conjNormal f r) = χsum r := by
      apply Multiplicative.toAdd.injective
      rw [hvalue, hvalue]
      exact Finset.sum_congr rfl fun i _ ↦
        congrArg (fun z : Multiplicative (ZMod p) ↦ a i * z.toAdd) (hχinv i f r)
    have hzero : inflatedFiniteTransgressionClass R U
        (InvariantFiniteCharacter.toMonoidHom (finiteStageImage R U) vSum)
        (InvariantFiniteCharacter.isInvariant (finiteStageImage R U) vSum) = 0 := by
      rw [← inflatedFiniteTransgressionLinearMap_apply]
      simpa only [vSum, map_sum, map_smul, w] using ha
    obtain ⟨ψ, hψ⟩ :=
      exists_continuous_extension_of_inflatedFiniteTransgressionClass_eq_zero R U
        (InvariantFiniteCharacter.toMonoidHom (finiteStageImage R U) vSum)
        (InvariantFiniteCharacter.isInvariant (finiteStageImage R U) vSum)
        χsum hχsumInv hpullSum hzero
    have hsum : ∑ i, a i • (fun r : R ↦ (χ i r).toAdd) = 0 := by
      funext r
      have hkill : ψ (r : F) = 1 := closedPowerCommutator_le_character_ker ψ (hR r.2)
      have hrestrict : ψ (r : F) = χsum r := DFunLike.congr_fun hψ r
      have hχzero : (χsum r).toAdd = 0 :=
        congrArg Multiplicative.toAdd (hrestrict.symm.trans hkill)
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hvalue]
        using hχzero
    exact ((@Fintype.linearIndependent_iff ι (ZMod p) (R → ZMod p)
      inferInstance inferInstance characterFunctionModule
      (fun i r ↦ (χ i r).toAdd) inferInstance).mp hχind a hsum) j
  exact hw.fintype_card_le_finrank

end

end ClassFieldTower.ProP
