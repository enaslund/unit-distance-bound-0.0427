/-
B-analogue of `UnitDistance/MaximalSigmaH2Reduction.lean` (adapted from
Yamaguchi/Sawin RealProTwoH2Bound at commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4,
Apache-2.0). The base ℚ is replaced by `B = ℚ(√241)`, the six rational primes by
the six primes of `B` above `2, 3, 5`, the stage bound `2^6` by `2^7`, and the
two arithmetic inputs by `FiniteDetectionPair B` and
`PrescribedQuadraticInertia B S`.
-/
module

public import UnitDistance.Sqrt241.Tower.OmegaB
public import UnitDistance.Sqrt241.Relation.KummerCount
public import UnitDistance.Sqrt241.Relation.AbsoluteKernel
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.TrivialZModP
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2FiniteStageFamily
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2InflationRangeCardinality
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.PresentationQuotientEquiv
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.DiscreteH2Comparison
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.FiniteKummerCoefficientH2

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Seven-dimensional degree two for `Gal(Ω_B/B)`, from two arithmetic inputs

At every finite stage `E` of `Ω_B/B` the field-unit Kummer image has at most
`2^6 · 2` elements (six places in `S`, and a finite-place detection kernel of
order at most two coming from the two real places of `B`). Its kernel dies
under inflation to `Gal(Ω_B/B)` (stage-kernel theorem, using a quadratic
character with prescribed inertia). Hence every finite-stage inflation image
has at most `2^7` elements, and continuous `H²(Gal(Ω_B/B), ℤ/2)` is finite of
dimension at most seven.
-/

open scoped NumberField Topology
open NumberField IsDedekindDomain CategoryTheory

noncomputable section

namespace UnitDistance.Sqrt241.Relation

open ClassFieldTower.Cohomology ClassFieldTower.ProP ClassFieldTower.Sawin
open ClassFieldTower.Martinet.Shafarevich ProCGroups ProCGroups.ProC
open UnitDistance.Sqrt241.ProP UnitDistance.Sqrt241.Tower UnitDistance.Sqrt241.Base

theorem natCard_le_range_of_ker_le
    {A B' C : Type} [AddCommGroup A] [AddCommGroup B'] [AddCommGroup C]
    (f : A →+ B') (g : A →+ C) (hker : f.ker ≤ g.ker)
    (hg : Function.Surjective g) [Finite f.range] : Nat.card C ≤ Nat.card f.range := by
  let q : A ⧸ f.ker →+ C := QuotientAddGroup.lift f.ker g hker
  have hq : Function.Surjective q :=
    QuotientAddGroup.lift_surjective_of_surjective f.ker g hg hker
  let e := (QuotientAddGroup.quotientKerEquivRange f).symm
  exact Nat.card_le_card_of_surjective (fun x : f.range => q (e x))
    (hq.comp e.surjective)

/-- `-1` is a primitive square root of unity in `B`. -/
theorem primitiveRoots_two_nonempty : (primitiveRoots ((2 : ℕ+) : ℕ) B).Nonempty :=
  ⟨-1, (mem_primitiveRoots (by decide : 0 < ((2 : ℕ+) : ℕ))).mpr
    (IsPrimitiveRoot.neg_one 0 (by decide))⟩

/-- Stage bound: every finite-stage inflation image has at most `2^7` elements. -/
theorem stage_inflationRange_natCard_le
    (hpair : FiniteDetectionPair B)
    (hchar : PrescribedQuadraticInertia B S)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup 2) GBw) :
    Nat.card (degreeTwoInflationRange (p := 2) U) ≤ 2 ^ 7 := by
  let G : Type := GBw
  let E : FiniteGaloisIntermediateField B Bbar := (proPOpenNormalStage B 2 S U.1).val
  have : NumberField E := NumberField.of_module_finite B E
  have : IsGalois B E.toIntermediateField := E.isGalois
  let hmu := primitiveRoots_two_nonempty
  let f := (finiteKummerCoefficientH2Map B E (2 : ℕ+) hmu).hom.toAddMonoidHom
  have hP : IsPGroup 2 Gal(E/B) := (proPOpenNormalStage B 2 S U.1).property.1
  have hfield := finiteKummerH2_range_natCard_le_of_pair B E SFin hmu hP
    (by
      intro v hv
      exact finitePExtension_chosenFinitePlaceIsUnramified B 2 S
        (proPOpenNormalStage B 2 S U.1) v
        (fun h => hv ((mem_SFin_iff v).mpr h)))
    (hpair E hP)
  have : Finite f.range := hfield.1
  let e : (G ⧸ (U.1 : Subgroup G)) ≃ₜ* Gal(E/B) :=
    proPOpenNormalQuotientContinuousEquivStage B 2 S U.1
  let he : continuousCohomologyZModPLifted 2 Gal(E/B) 2 ≃ₗ[ZMod 2]
      continuousCohomologyZModPLifted 2 (G ⧸ (U.1 : Subgroup G)) 2 :=
    continuousCohomologyZModPLiftedLinearEquiv e 2
  let dc : continuousCohomologyZModPLifted 2 Gal(E/B) 2 ≃+
      groupCohomology (Rep.trivial ℤ Gal(E/B) (ULift.{0} (ZMod 2))) 2 :=
    discreteContinuousH2AddEquiv (p := 2) (Q := Gal(E/B))
  let I : continuousCohomologyZModPLifted 2 (G ⧸ (U.1 : Subgroup G)) 2 →ₗ[ZMod 2]
      continuousCohomologyZModPLifted 2 G 2 :=
    (continuousCohomologyZModPMapLifted 2
      (OpenNormalSubgroupInClass.quotientProj U) 2).hom.toLinearMap
  have hMap (x : continuousCohomologyZModPLifted 2 Gal(E/B) 2) :
      I (he x) = (continuousCohomologyZModPMapLifted 2
        (proPOpenNormalStageRestriction B 2 S U.1) 2).hom x := by
    let eHom : (G ⧸ (U.1 : Subgroup G)) →ₜ* Gal(E/B) := e
    have hDef : eHom.comp (OpenNormalSubgroupInClass.quotientProj U) =
        proPOpenNormalStageRestriction B 2 S U.1 := by rfl
    have h := continuousCohomologyZModPMapLifted_comp 2 eHom
      (OpenNormalSubgroupInClass.quotientProj U) 2
    rw [hDef] at h
    exact (ConcreteCategory.congr_hom h x).symm
  let g := I.rangeRestrict.toAddMonoidHom.comp
    (he.toAddEquiv.toAddMonoidHom.comp dc.symm.toAddMonoidHom)
  have hg : Function.Surjective g :=
    I.surjective_rangeRestrict.comp (he.surjective.comp dc.symm.surjective)
  have hker : f.ker ≤ g.ker := by
    intro x hx
    have hc : (finiteKummerContinuousH2Map B (2 : ℕ+) E hmu) (dc.symm x) = 0 := by
      change f (dc (dc.symm x)) = 0
      exact (congrArg f (dc.apply_symm_apply x)).trans hx
    have hzero := finiteKummerContinuousH2Map_ker_le_proPStageInflation_ker B S hchar
      U.1 hmu hc
    apply Subtype.ext
    change I (he (dc.symm x)) = 0
    exact (hMap _).trans hzero
  have hcard : Nat.card I.range ≤ Nat.card f.range :=
    natCard_le_range_of_ker_le f g hker hg
  have hfcard : Nat.card f.range ≤ 2 ^ SFin.card * 2 := hfield.2
  rw [SFin_card] at hfcard
  exact hcard.trans (hfcard.trans (by norm_num))

/-- The two arithmetic inputs imply finite continuous `H²` of `Gal(Ω_B/B)` of
dimension at most seven. -/
theorem OmegaB_h2_of_inputs
    (hpair : FiniteDetectionPair B)
    (hchar : PrescribedQuadraticInertia B S) :
    FiniteDimensional (ZMod 2) (continuousCohomologyZModPLifted 2 GBw 2) ∧
      Module.finrank (ZMod 2) (continuousCohomologyZModPLifted 2 GBw 2) ≤ 7 :=
  finiteDimensional_and_finrank_degree_two_le_of_inflationRange_natCard 7
    OmegaB_hasPGroupOpenNormalBasis (stage_inflationRange_natCard_le hpair hchar)

end UnitDistance.Sqrt241.Relation
