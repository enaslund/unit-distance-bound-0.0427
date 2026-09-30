module

public import UnitDistance.FreeThreeQuadratic
public import UnitDistance.PadicTwoNoQuarticCharacter
public import UnitDistance.PadicTwoQuadraticModel

@[expose] public section
set_option backward.privateInPublic true


/-! A genuine relation of the actual maximal pro-two Galois group of Q₂,
with its nonzero quadratic image computed in the universal finite detector. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace UnitDistance.PadicTwoQuadraticRelation
open ProCGroups ProCGroups.ProC ClassFieldTower.ProP
open ClassTwo
namespace U
abbrev Q := FreeThreeQuadratic.Q
instance topology : TopologicalSpace Q := ⊥
instance discrete : DiscreteTopology Q := ⟨rfl⟩
instance topologicalGroup : IsTopologicalGroup Q := inferInstance
instance t2 : T2Space Q := inferInstance

theorem proTwo : HasPGroupOpenNormalBasis 2 Q :=
  HasOpenNormalBasisInClass.of_finite_discrete (FiniteGroupClass.pGroup_formation 2).quotientClosed
    ⟨inferInstance,GroupModel.isTwoGroup FreeThreeQuadratic.cocycle⟩

def base : Q →ₜ* PadicTwoMaximalProTwo.VectorGroup where
  toFun q := Multiplicative.ofAdd q.base
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_of_discreteTopology

def quartic : Q →ₜ* FreeThreeQuadratic.C4 :=
  ⟨FreeThreeQuadratic.quartic,continuous_of_discreteTopology⟩

theorem base_zero_of_quartic_eq_one (q : Q) (h : quartic q=1) : q.base 0=0 := by
  have hh : ∀a c : ZMod 2,(a.val+2*c.val : ZMod 4)=0 → a=0 := by decide +kernel
  exact hh (q.base 0) (q.central 0) (congrArg Multiplicative.toAdd h)
end U

abbrev Source := FiniteFreeProTwo.Carrier 3
abbrev G := PadicTwoMaximalProTwo.Group

def detector : Source →ₜ* U.Q :=
  (FiniteFreeProTwo.isFree 3).liftHom U.proTwo FreeThreeQuadratic.basis continuous_of_discreteTopology

@[simp] theorem detector_generator (i : Fin 3) : detector (FiniteFreeProTwo.generator 3 i)=
    FreeThreeQuadratic.basis i :=
  (FiniteFreeProTwo.isFree 3).liftHom_apply U.proTwo FreeThreeQuadratic.basis continuous_of_discreteTopology i

def quartic : Source →ₜ* FreeThreeQuadratic.C4 := U.quartic.comp detector

theorem quartic_surjective : Function.Surjective quartic := by
  intro z
  refine ⟨FiniteFreeProTwo.generator 3 0 ^ z.toAdd.val,?_⟩
  rw [map_pow]
  change (FreeThreeQuadratic.quartic (detector (FiniteFreeProTwo.generator 3 0)))^z.toAdd.val=z
  rw [detector_generator,FreeThreeQuadratic.quartic_basis,if_pos rfl]
  apply Multiplicative.toAdd.injective
  change z.toAdd.val • (1 : ZMod 4)=z.toAdd
  simp

theorem detector_base (π : Source →ₜ* G)
    (hπ : ∀i,PadicTwoMaximalProTwo.signs (π (FiniteFreeProTwo.generator 3 i))=
      PadicTwoMaximalProTwo.genusBasis i) (r : Source) :
    U.base (detector r)=PadicTwoMaximalProTwo.signs (π r) := by
  have h := (FiniteFreeProTwo.isFree 3).hom_ext PadicTwoMaximalProTwo.vector_proTwo
    (f := (U.base.comp detector).toMonoidHom)
    (g := (PadicTwoMaximalProTwo.signs.comp π).toMonoidHom)
    (U.base.comp detector).continuous (PadicTwoMaximalProTwo.signs.comp π).continuous (by
      intro i
      change U.base (detector (FiniteFreeProTwo.generator 3 i))=PadicTwoMaximalProTwo.signs (π (FiniteFreeProTwo.generator 3 i))
      rw [detector_generator,hπ]
      rfl)
  exact congrArg (fun f : Source →* PadicTwoMaximalProTwo.VectorGroup => f r) h

/-- If the cyclic-four character vanished on the full arithmetic kernel, it
would descend to a forbidden actual cyclic quartic extension. -/
theorem exists_relation_quartic_ne_one (π : Source →ₜ* G) (hπsurj : Function.Surjective π)
    (hπ : ∀i,PadicTwoMaximalProTwo.signs (π (FiniteFreeProTwo.generator 3 i))=
      PadicTwoMaximalProTwo.genusBasis i) :
    ∃r : Source,π r=1 ∧ quartic r≠1 := by
  classical
  by_contra h
  have hk : π.toMonoidHom.ker ≤ quartic.toMonoidHom.ker := by
    intro r hr
    by_contra hn
    exact h ⟨r,hr,hn⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective π.toMonoidHom hπsurj
  have hecont : Continuous e.toMonoidHom := by
    apply (QuotientGroup.isQuotientMap_mk π.toMonoidHom.ker).continuous_iff.mpr
    exact π.continuous
  let ec := ContinuousMulEquiv.ofBijectiveCompactToT2 e.toMonoidHom hecont e.bijective
  let qbar := ProCGroups.QuotientGroup.liftₜ π.toMonoidHom.ker quartic hk
  let q : G →ₜ* FreeThreeQuadratic.C4 := qbar.comp ⟨ec.symm.toMulEquiv.toMonoidHom,ec.symm.continuous⟩
  have heval (r : Source) : q (π r)=quartic r := by
    have hm : ec (QuotientGroup.mk' π.toMonoidHom.ker r)=π r := rfl
    change qbar (ec.symm (π r))=quartic r
    rw [←hm,ec.symm_apply_apply]
    rfl
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨r,hr⟩ := quartic_surjective z
    exact ⟨π r,(heval r).trans hr⟩
  apply PadicTwoMaximalProTwo.no_cyclic_four_quotient (C := FreeThreeQuadratic.C4)
    (by rw [Nat.card_congr (Multiplicative.toAdd : FreeThreeQuadratic.C4 ≃ ZMod 4)]; simp) q hq
  intro g hg
  obtain ⟨r,rfl⟩ := hπsurj g
  have hz := U.base_zero_of_quartic_eq_one (detector r) ((heval r).symm.trans hg)
  have hb := congrArg (fun a : PadicTwoMaximalProTwo.VectorGroup => a.toAdd 0) (detector_base π hπ r)
  exact hb.symm.trans hz

/-- Generators aligned with the actual degree-256 arithmetic model. -/
def generator (i : Fin 3) : G := Function.surjInv PadicTwoMaximalProTwo.quadraticRestriction_surjective
  (PadicTwoQuadratic.quadraticModelEquiv (LocalQuadraticModel.basis i))

theorem generator_restriction (i : Fin 3) : PadicTwoMaximalProTwo.quadraticRestriction (generator i)=
    PadicTwoQuadratic.quadraticModelEquiv (LocalQuadraticModel.basis i) :=
  Function.surjInv_eq PadicTwoMaximalProTwo.quadraticRestriction_surjective _

theorem generator_signs (i : Fin 3) : PadicTwoMaximalProTwo.signs (generator i)=
    PadicTwoMaximalProTwo.genusBasis i := by
  apply Multiplicative.toAdd.injective
  rw [←PadicTwoMaximalProTwo.quadraticRestriction_genusVector,generator_restriction]
  exact PadicTwoQuadratic.genusVector_quadraticModelHom _

def modelMap : U.Q →ₜ* PadicTwoQuadratic.G :=
  ⟨PadicTwoQuadratic.quadraticModelEquiv.toMonoidHom.comp FreeThreeQuadratic.quotient,
    continuous_of_discreteTopology⟩

theorem modelMap_detector (π : Source →ₜ* G)
    (hπ : ∀i,π (FiniteFreeProTwo.generator 3 i)=generator i) (r : Source) :
    modelMap (detector r)=PadicTwoMaximalProTwo.quadraticRestriction (π r) := by
  have h := (FiniteFreeProTwo.isFree 3).hom_ext
    (PadicTwoMaximalProTwo.finiteGalois_proTwo PadicTwoQuadratic.isPGroup)
    (f := (modelMap.comp detector).toMonoidHom)
    (g := (PadicTwoMaximalProTwo.quadraticRestriction.comp π).toMonoidHom)
    (modelMap.comp detector).continuous (PadicTwoMaximalProTwo.quadraticRestriction.comp π).continuous (by
      intro i
      change modelMap (detector (FiniteFreeProTwo.generator 3 i))=PadicTwoMaximalProTwo.quadraticRestriction (π (FiniteFreeProTwo.generator 3 i))
      rw [detector_generator,hπ,generator_restriction]
      change PadicTwoQuadratic.quadraticModelEquiv (FreeThreeQuadratic.quotient (FreeThreeQuadratic.basis i))=_
      rw [FreeThreeQuadratic.quotient_basis])
  exact congrArg (fun f : Source →* PadicTwoQuadratic.G => f r) h

/-- An actual minimal free presentation admits a genuine kernel element whose
universal quadratic image is exactly a²+[b,c]. -/
theorem exists_actual_quadratic_relation :
    ∃π : Source →ₜ* G,Function.Surjective π ∧
      π.toMonoidHom.ker ≤ closedPowerCommutator 2 Source ∧
      (∀i,π (FiniteFreeProTwo.generator 3 i)=generator i) ∧
      ∃r : Source,π r=1 ∧ detector r=FreeThreeQuadratic.relation := by
  obtain ⟨π,hsurj,hker,hgen⟩ := FiniteFreeProTwo.exists_minimal_surjection_for_generators
    PadicTwoMaximalProTwo.proTwo 3 generator
    (PadicTwoMaximalProTwo.generates_of_genusBasis generator generator_signs)
    PadicTwoMaximalProTwo.generatorRank_three.2
  have hsign i : PadicTwoMaximalProTwo.signs (π (FiniteFreeProTwo.generator 3 i))=
      PadicTwoMaximalProTwo.genusBasis i := by rw [hgen,generator_signs]
  obtain ⟨r,hr,hqr⟩ := exists_relation_quartic_ne_one π hsurj hsign
  refine ⟨π,hsurj,hker,hgen,r,hr,?_⟩
  have hm : FreeThreeQuadratic.quotient (detector r)=1 := by
    apply PadicTwoQuadratic.quadraticModelEquiv.injective
    change modelMap (detector r)=PadicTwoQuadratic.quadraticModelEquiv 1
    rw [modelMap_detector π hgen,hr,map_one,map_one]
  rcases (FreeThreeQuadratic.quotient_eq_one_iff _).mp hm with hz | hz
  · exact False.elim (hqr (by change U.quartic (detector r)=1; rw [hz,map_one]))
  · exact hz
end UnitDistance.PadicTwoQuadraticRelation
