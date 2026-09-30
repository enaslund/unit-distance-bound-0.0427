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

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceDecompositionAdicEquiv
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FinitePlaceH1RamificationLocalization

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false
/-!
# Actual absolute-character restriction to the adic completion

The inverse of the decomposition--adic equivalence transports the already
constructed decomposition-group restriction to intrinsic local `H¹`.
-/

open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

local instance finitePlaceH1AdicZModTopology : TopologicalSpace (ZMod p) := ⊥
local instance finitePlaceH1AdicZModDiscreteTopology : DiscreteTopology (ZMod p) :=
  discreteTopology_bot _

local instance finitePlaceH1AdicCharacterTopology :
    TopologicalSpace (Multiplicative (ZMod p)) := ⊥

local instance finitePlaceH1AdicCharacterDiscreteTopology :
    DiscreteTopology (Multiplicative (ZMod p)) := discreteTopology_bot _

local instance finitePlaceH1AdicAddCommGroup
    {q : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    AddCommGroup (ContinuousH1ZMod (p := q) (G := G)) :=
  ContinuousAddMonoidHom.instAddCommGroup (Additive G) (ZMod q)

local instance finitePlaceH1AdicModule
    {q : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := G)) :=
  continuousH1ZModModule

/-- Transport decomposition-group `H¹` through the actual inverse localization. -/
noncomputable def finitePlaceDecompositionH1ToAdic
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) →ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup (v.adicCompletion F)) := by
  let f :
      ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v) →+
        ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup (v.adicCompletion F)) :=
    { toFun := fun chi ↦ h1OfCharacter ((characterOfH1 chi).comp
       (ContinuousMonoidHom.toContinuousMonoidHom
         (finitePlaceDecompositionAdicContinuousMulEquiv F v).symm))
      map_zero' := by ext sigma; rfl
      map_add' := by intro chi psi; ext sigma; rfl }
  exact f.toZModLinearMap p

@[simp] theorem finitePlaceDecompositionH1ToAdic_apply
    (v : HeightOneSpectrum (RingOfIntegers F))
    (chi : ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v))
    (sigma : Additive (Field.absoluteGaloisGroup (v.adicCompletion F))) :
    finitePlaceDecompositionH1ToAdic F p v chi sigma =
      chi (Additive.ofMul ((finitePlaceDecompositionAdicContinuousMulEquiv F v).symm
        (Additive.toMul sigma))) := by
  rfl

@[simp] theorem finitePlaceAdicH1Restriction_decompositionH1ToAdic
    (v : HeightOneSpectrum (RingOfIntegers F))
    (chi : ContinuousH1ZMod (p := p) (G := finitePlaceAbsoluteDecompositionGroup F v)) :
    finitePlaceAdicH1Restriction F p v (finitePlaceDecompositionH1ToAdic F p v chi) =
      chi := by
  ext sigma
  change finitePlaceAdicH1Restriction F p v
      (finitePlaceDecompositionH1ToAdic F p v chi)
      (Additive.ofMul (Additive.toMul sigma)) = chi sigma
  rw [finitePlaceAdicH1Restriction_apply (K := F) (p := p) (v := v)
    (chi := finitePlaceDecompositionH1ToAdic F p v chi)
    (sigma := Additive.toMul sigma)]
  rw [finitePlaceDecompositionH1ToAdic_apply]
  change chi (Additive.ofMul ((finitePlaceDecompositionAdicContinuousMulEquiv F v).symm
    (finitePlaceDecompositionToAdicAbsoluteGaloisGroup F v (Additive.toMul sigma)))) =
      chi sigma
  have h :
      (finitePlaceDecompositionAdicContinuousMulEquiv F v).symm
          (finitePlaceDecompositionToAdicAbsoluteGaloisGroup F v (Additive.toMul sigma)) =
        Additive.toMul sigma := by
    rw [← finitePlaceDecompositionAdicContinuousMulEquiv_apply]
    exact (finitePlaceDecompositionAdicContinuousMulEquiv F v).symm_apply_apply _
  rw [h]
  rfl

@[simp] theorem finitePlaceDecompositionH1ToAdic_adicH1Restriction
    (v : HeightOneSpectrum (RingOfIntegers F))
    (chi : ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup (v.adicCompletion F))) :
    finitePlaceDecompositionH1ToAdic F p v (finitePlaceAdicH1Restriction F p v chi) =
      chi := by
  ext sigma
  rw [finitePlaceDecompositionH1ToAdic_apply]
  change finitePlaceAdicH1Restriction F p v chi
      (Additive.ofMul ((finitePlaceDecompositionAdicContinuousMulEquiv F v).symm
        (Additive.toMul sigma))) = chi sigma
  rw [finitePlaceAdicH1Restriction_apply (K := F) (p := p) (v := v)
    (chi := chi)
    (sigma := (finitePlaceDecompositionAdicContinuousMulEquiv F v).symm
      (Additive.toMul sigma))]
  rw [← finitePlaceDecompositionAdicContinuousMulEquiv_apply]
  simp

/-- Actual global absolute-character restriction, now valued in intrinsic adic `H¹`. -/
noncomputable def finitePlaceAbsoluteH1AdicRestriction
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    absoluteContinuousZModCharacterModP F p →ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := Field.absoluteGaloisGroup (v.adicCompletion F)) :=
  (finitePlaceDecompositionH1ToAdic F p v).comp
    (finitePlaceAbsoluteH1DecompositionRestriction F p v)

/-- Pulling back the intrinsic local restriction recovers the original actual
decomposition-group restriction, with no change of character. -/
@[simp] theorem finitePlaceAbsoluteH1AdicRestriction_decomposition
    (v : HeightOneSpectrum (RingOfIntegers F))
    (chi : absoluteContinuousZModCharacterModP F p) :
    finitePlaceAdicH1Restriction F p v (finitePlaceAbsoluteH1AdicRestriction F p v chi) =
      finitePlaceAbsoluteH1DecompositionRestriction F p v chi :=
  finitePlaceAdicH1Restriction_decompositionH1ToAdic F p v _

end ClassFieldTower.Martinet.Shafarevich
