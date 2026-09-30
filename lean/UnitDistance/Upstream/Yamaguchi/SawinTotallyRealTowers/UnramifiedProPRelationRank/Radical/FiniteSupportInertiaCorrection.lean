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

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportIdeleCorrection
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceAbsoluteArtinCompatibility
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceAdicInertiaTransport
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceReciprocityUnramifiedUnits

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false
/-!
# Global characters with prescribed finite inertia values

The ideal-radical annihilator condition supplies a genuine global abelian
character. Actual local Artin compatibility and the integral-unit criterion
turn its idele values into equality on inertia, including places outside the
prescribed finite support. No roots-of-unity assumption is needed.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology

noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich
open ClassFieldTower.ProP GlobalClassFieldTheory.Reciprocity LocalClassFieldTheory

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime]

local instance finiteSupportInertiaCorrectionTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance finiteSupportInertiaCorrectionDiscrete : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _
local instance finiteSupportInertiaCorrectionValuative (v : HeightOneSpectrum (𝓞 F)) :
    ValuativeRel (v.adicCompletion F) := finitePlaceAdicCompletionValuativeRel F v
local instance finiteSupportInertiaCorrectionLocalField (v : HeightOneSpectrum (𝓞 F)) :
    IsNonarchimedeanLocalField (v.adicCompletion F) :=
  finitePlaceAdicCompletionIsNonarchimedeanLocalField F v
local instance finiteSupportInertiaCorrectionH1Module
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod (n : ℕ)) (ContinuousH1ZMod (p := (n : ℕ)) (G := G)) :=
  continuousH1ZModModule
local instance finiteSupportInertiaCorrectionH1AddCommGroup
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    AddCommGroup (ContinuousH1ZMod (p := (n : ℕ)) (G := G)) :=
  ContinuousAddMonoidHom.instAddCommGroup (Additive G) (ZMod (n : ℕ))

local instance finiteSupportInertiaCorrectionPairingDualAddCommGroup
    {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    AddCommGroup
      (Module.Dual (ZMod (n : ℕ))
        (absolutePowerClassModP K (n : ℕ))) := by
  letI : AddCommGroup (absolutePowerClassModP K (n : ℕ)) :=
    (absolutePowerClassModP K (n : ℕ)).isAddCommGroup
  letI : Module (ZMod (n : ℕ))
      (absolutePowerClassModP K (n : ℕ)) :=
    (absolutePowerClassModP K (n : ℕ)).isModule
  letI : Semiring (ZMod (n : ℕ)) :=
    (inferInstance : CommRing (ZMod (n : ℕ))).toCommSemiring.toSemiring
  letI : Module (ZMod (n : ℕ)) (ZMod (n : ℕ)) := Semiring.toModule
  letI : SMulCommClass (ZMod (n : ℕ)) (ZMod (n : ℕ))
      (ZMod (n : ℕ)) :=
    ⟨fun r s x => by
      change r * (s * x) = s * (r * x)
      ac_rfl⟩
  exact @LinearMap.addCommGroup
    (ZMod (n : ℕ)) (ZMod (n : ℕ))
    (absolutePowerClassModP K (n : ℕ)) (ZMod (n : ℕ))
    _ _ _ _ (absolutePowerClassModP K (n : ℕ)).isModule
    Semiring.toModule (RingHom.id (ZMod (n : ℕ)))

local instance finiteSupportInertiaCorrectionPairingDualAddZeroClass
    {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    AddZeroClass
      (Module.Dual (ZMod (n : ℕ))
        (absolutePowerClassModP K (n : ℕ))) :=
  (inferInstance : AddCommGroup
    (Module.Dual (ZMod (n : ℕ))
      (absolutePowerClassModP K (n : ℕ)))).toAddGroup.toAddZeroClass

private theorem localReciprocityUnitCharacter_sub_eq_one
    (v : HeightOneSpectrum (𝓞 F))
    (chi psi : ContinuousH1ZMod (p := (n : ℕ))
      (G := Field.absoluteGaloisGroup (v.adicCompletion F)))
    (a : (v.adicCompletion F)ˣ)
    (h : localReciprocityUnitCharacter (v.adicCompletion F) (n : ℕ) chi a =
      localReciprocityUnitCharacter (v.adicCompletion F) (n : ℕ) psi a) :
    localReciprocityUnitCharacter (v.adicCompletion F) (n : ℕ) (chi - psi) a = 1 := by
  apply Multiplicative.toAdd.injective
  let qa : absolutePowerClassModP (v.adicCompletion F) (n : ℕ) :=
    Additive.ofMul (QuotientGroup.mk'
      (powMonoidHom (n : ℕ) : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range a)
  change localReciprocityH1PowerClassPairing (v.adicCompletion F) (n : ℕ) (chi - psi)
    qa = 0
  rw [map_sub]
  change localReciprocityH1PowerClassPairing (v.adicCompletion F) (n : ℕ) chi qa -
    localReciprocityH1PowerClassPairing (v.adicCompletion F) (n : ℕ) psi qa = 0
  have hchi : localReciprocityH1PowerClassPairing (v.adicCompletion F) (n : ℕ) chi qa =
      (localReciprocityAbelianCharacter (v.adicCompletion F) (n : ℕ) chi
        (absoluteLocalArtinMap (v.adicCompletion F) a)).toAdd := by
    simpa only [qa] using
      localReciprocityH1PowerClassPairing_mk (v.adicCompletion F) (n : ℕ) chi a
  have hpsi : localReciprocityH1PowerClassPairing (v.adicCompletion F) (n : ℕ) psi qa =
      (localReciprocityAbelianCharacter (v.adicCompletion F) (n : ℕ) psi
        (absoluteLocalArtinMap (v.adicCompletion F) a)).toAdd := by
    simpa only [qa] using
      localReciprocityH1PowerClassPairing_mk (v.adicCompletion F) (n : ℕ) psi a
  rw [hchi, hpsi]
  have hvalue := congrArg Multiplicative.toAdd h
  change
    (localReciprocityAbelianCharacter (v.adicCompletion F) (n : ℕ) chi
      (absoluteLocalArtinMap (v.adicCompletion F) a)).toAdd =
    (localReciprocityAbelianCharacter (v.adicCompletion F) (n : ℕ) psi
      (absoluteLocalArtinMap (v.adicCompletion F) a)).toAdd at hvalue
  exact sub_eq_zero.mpr hvalue

/-- A finite local family annihilating the ideal radical is realized on
actual inertia by one global character, unramified outside that family. -/
theorem exists_absoluteCharacter_of_finiteSupport_radical_annihilator
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (chi : ∀ v : ↥S, finitePlaceAbsoluteDecompositionGroup F v.1 →ₜ*
      Multiplicative (ZMod (n : ℕ)))
    (hchi : absolutePowerClassDualRestriction F (n : ℕ)
      (finiteSupportLocalReciprocityPowerClassFunctional F (n : ℕ) S
        (fun v => finitePlaceDecompositionH1ToAdic F (n : ℕ) v.1
          (h1OfCharacter (chi v)))) = 0) :
    ∃ gamma : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod (n : ℕ)),
      (∀ (v : ↥S) (sigma : finitePlaceAbsoluteInertiaSubgroup F v.1),
        chi v sigma.1 = gamma (finitePlaceAbsoluteDecompositionInclusion F v.1 sigma.1)) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F)), v ∉ S →
        ∀ sigma : finitePlaceAbsoluteInertiaSubgroup F v,
          gamma (finitePlaceAbsoluteDecompositionInclusion F v sigma.1) = 1) := by
  let family := fun v : ↥S => finitePlaceDecompositionH1ToAdic F (n : ℕ) v.1
    (h1OfCharacter (chi v))
  obtain ⟨psi, hpsi⟩ :=
    exists_maximalAbelianCharacter_of_finiteSupport_radical_annihilator F (n : ℕ) S family hchi
  let gamma := psi.comp (globalMaximalAbelianRestriction F)
  have hvalue (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
      (ha : a ∈ (v.adicCompletionIntegers F).units) :
      localReciprocityUnitCharacter (v.adicCompletion F) (n : ℕ)
        (finitePlaceAbsoluteH1AdicRestriction F (n : ℕ) v (Additive.ofMul gamma)) a =
        finiteSupportLocalReciprocityIdeleCharacter F (n : ℕ) S family
          (IdeleGroup.finitePlaceIdele v a) := by
    exact (localReciprocityUnitCharacter_globalMaximalAbelian F v (n : ℕ) psi a).trans
      (hpsi v a ha)
  refine ⟨gamma, ?_, ?_⟩
  · intro v sigma
    have hunram : finitePlaceDecompositionH1ToAdic F (n : ℕ) v.1
        (h1OfCharacter (chi v) -
          finitePlaceAbsoluteH1DecompositionRestriction F (n : ℕ) v.1
            (Additive.ofMul gamma)) ∈ localStandardUnramifiedH1 (v.1.adicCompletion F) n := by
      apply (finitePlaceLocalReciprocityUnitCharacter_integralUnits_iff_unramified
        F n v.1 _).1
      intro a ha
      rw [map_sub]
      apply localReciprocityUnitCharacter_sub_eq_one F n v.1
      exact ((hvalue v.1 a ha).trans
        (finiteSupportLocalReciprocityIdeleCharacter_finitePlace_mem
          F (n : ℕ) S family v a)).symm
    rw [finitePlaceDecompositionH1ToAdic_mem_unramified_iff,
      mem_finitePlaceUnramifiedH1_iff] at hunram
    apply Multiplicative.toAdd.injective
    exact sub_eq_zero.mp (hunram sigma)
  · intro v hv sigma
    have hunram : finitePlaceDecompositionH1ToAdic F (n : ℕ) v
        (finitePlaceAbsoluteH1DecompositionRestriction F (n : ℕ) v
          (Additive.ofMul gamma)) ∈ localStandardUnramifiedH1 (v.adicCompletion F) n := by
      apply (finitePlaceLocalReciprocityUnitCharacter_integralUnits_iff_unramified
        F n v _).1
      intro a ha
      exact (hvalue v a ha).trans
        (finiteSupportLocalReciprocityIdeleCharacter_finitePlace_notMem F (n : ℕ) S family v hv a)
    rw [finitePlaceDecompositionH1ToAdic_mem_unramified_iff,
      mem_finitePlaceUnramifiedH1_iff] at hunram
    exact Multiplicative.toAdd.injective (hunram sigma)

end ClassFieldTower.Martinet.Shafarevich
