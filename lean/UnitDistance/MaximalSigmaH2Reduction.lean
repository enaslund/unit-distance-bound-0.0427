/- Adapted from Yamaguchi/Sawin RealProTwoH2Bound at commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4 (Apache-2.0). The actual maximal
extension allows complex places; the finite image bound is supplied by the
proved rational finite-place detector, not an infinite-unramified premise.
Private conditional reduction: the cyclic detection and actual stage-kernel
inclusion are explicit inputs, to be discharged by the separate arithmetic proofs. -/
module

public import UnitDistance.SigmaPrimeSupport
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.FiniteKummerContinuousKernel
public import UnitDistance.ProPOpenNormalStage
public import UnitDistance.MaximalProPOutside
public import UnitDistance.ProPStageRestriction
public import UnitDistance.ProPStageLocalConditions
public import UnitDistance.MaximalProPGroup
public import UnitDistance.SigmaFinitePrimeSupport
public import UnitDistance.RationalFiniteKummerReduction
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.TrivialZModP
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2FiniteStageFamily
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2InflationRangeCardinality
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.PresentationQuotientEquiv
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.DiscreteH2Comparison
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.FiniteKummerCoefficientH2
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Six-dimensional degree two for the initial pro-two group

Under the two explicitly supplied arithmetic inputs, at every actual
finite arithmetic stage the field-unit Kummer image has
at most 64 elements. Its kernel is killed by inflation to the constructed
maximal group. Discrete comparison and the finite-stage Galois equivalence
therefore give a surjection from that Kummer image onto the stage inflation
image. Uniform finite-stage cardinality bounds imply finite continuous H²
and dimension at most six, with no cohomological finiteness assumption.
-/

open scoped NumberField Topology
open NumberField IsDedekindDomain CategoryTheory

noncomputable section

namespace UnitDistance.ArithmeticProP

open ClassFieldTower.Cohomology ClassFieldTower.ProP ClassFieldTower.Sawin
open ClassFieldTower.Martinet.Shafarevich ProCGroups ProCGroups.ProC

private theorem natCard_le_range_of_ker_le
    {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : A →+ C) (hker : f.ker ≤ g.ker)
    (hg : Function.Surjective g) [Finite f.range] : Nat.card C ≤ Nat.card f.range := by
  let q : A ⧸ f.ker →+ C := QuotientAddGroup.lift f.ker g hker
  have hq : Function.Surjective q :=
    QuotientAddGroup.lift_surjective_of_surjective f.ker g hg hker
  let e := (QuotientAddGroup.quotientKerEquivRange f).symm
  exact Nat.card_le_card_of_surjective (fun x : f.range => q (e x))
    (hq.comp e.surjective)

private theorem initialStage_inflationRange_natCard_le
    (hcyc : ImaginaryFieldUnitsFiniteDetection)
    (hkernel : ∀ (U : OpenNormalSubgroup
      (maximalProPOutside 2 sigmaPrimeSupport ≃ₐ[ℚ]
        maximalProPOutside 2 sigmaPrimeSupport))
      (hmu : (primitiveRoots 2 ℚ).Nonempty),
      (finiteKummerContinuousH2Map ℚ (2 : ℕ+)
        (proPOpenNormalStage 2 sigmaPrimeSupport U).val hmu).ker ≤
      (continuousCohomologyZModPMapLifted 2
        (proPOpenNormalStageRestriction 2 sigmaPrimeSupport U) 2).hom.toLinearMap.toAddMonoidHom.ker)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup 2)
      (maximalProPOutside 2 sigmaPrimeSupport ≃ₐ[ℚ]
        maximalProPOutside 2 sigmaPrimeSupport)) :
    Nat.card (degreeTwoInflationRange (p := 2) U) ≤ 2 ^ 6 := by
  let T := sigmaPrimeSupport
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := maximalProPOutside 2 T
  let G : Type := M ≃ₐ[ℚ] M
  let E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    (proPOpenNormalStage 2 T U.1).val
  let : IsGalois ℚ M := maximalProPOutside_isGalois 2 T
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : IsGalois ℚ E.toIntermediateField := E.isGalois
  let e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  have hThree : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ T := by
    change (e (e.symm (⟨3, Nat.prime_three⟩ : Nat.Primes)) : ℕ) ∈
      sigmaRationalPrimes
    have he : e (e.symm (⟨3, Nat.prime_three⟩ : Nat.Primes)) =
        (⟨3, Nat.prime_three⟩ : Nat.Primes) := e.apply_symm_apply _
    rw [he]
    decide
  have hmu : (primitiveRoots 2 ℚ).Nonempty :=
    ⟨-1, (mem_primitiveRoots (by decide : 0 < 2)).mpr
      (IsPrimitiveRoot.neg_one 0 (by decide))⟩
  let f := (finiteKummerCoefficientH2Map ℚ E (2 : ℕ+) hmu).hom.toAddMonoidHom
  have hfield := rationalFiniteKummerH2_range_finite_natCard_le_of_imaginary_detection
    E hcyc sigmaFinitePrimeSupport hmu
    (proPOpenNormalStage 2 T U.1).property.1
    (by
      intro v hv
      exact finitePExtension_chosenFinitePlaceIsUnramified 2 T
        (proPOpenNormalStage 2 T U.1) v
        (fun h => hv ((mem_sigmaFinitePrimeSupport_iff v).mpr h)))
  let : Finite f.range := hfield.1
  let e : (G ⧸ (U.1 : Subgroup G)) ≃ₜ* Gal(E/ℚ) :=
    proPOpenNormalQuotientContinuousEquivStage 2 T U.1
  let he : continuousCohomologyZModPLifted 2 Gal(E/ℚ) 2 ≃ₗ[ZMod 2]
      continuousCohomologyZModPLifted 2 (G ⧸ (U.1 : Subgroup G)) 2 :=
    continuousCohomologyZModPLiftedLinearEquiv e 2
  let dc : continuousCohomologyZModPLifted 2 Gal(E/ℚ) 2 ≃+
      groupCohomology (Rep.trivial ℤ Gal(E/ℚ) (ULift.{0} (ZMod 2))) 2 :=
    discreteContinuousH2AddEquiv (p := 2) (Q := Gal(E/ℚ))
  let I : continuousCohomologyZModPLifted 2 (G ⧸ (U.1 : Subgroup G)) 2 →ₗ[ZMod 2]
      continuousCohomologyZModPLifted 2 G 2 :=
    (continuousCohomologyZModPMapLifted 2
      (OpenNormalSubgroupInClass.quotientProj U) 2).hom.toLinearMap
  have hMap (x : continuousCohomologyZModPLifted 2 Gal(E/ℚ) 2) :
      I (he x) = (continuousCohomologyZModPMapLifted 2
        (proPOpenNormalStageRestriction 2 T U.1) 2).hom x := by
    let eHom : (G ⧸ (U.1 : Subgroup G)) →ₜ* Gal(E/ℚ) := e
    have hDef : eHom.comp (OpenNormalSubgroupInClass.quotientProj U) =
        proPOpenNormalStageRestriction 2 T U.1 := by rfl
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
    have hc : (finiteKummerContinuousH2Map ℚ (2 : ℕ+) E hmu) (dc.symm x) = 0 := by
      change f (dc (dc.symm x)) = 0
      exact (congrArg f (dc.apply_symm_apply x)).trans hx
    have hzero := hkernel U.1 hmu hc
    apply Subtype.ext
    change I (he (dc.symm x)) = 0
    exact (hMap _).trans hzero
  have hcard : Nat.card I.range ≤ Nat.card f.range :=
    natCard_le_range_of_ker_le f g hker hg
  have hfcard : Nat.card f.range ≤ 2 ^ sigmaFinitePrimeSupport.card := hfield.2
  rw [sigmaFinitePrimeSupport_card] at hfcard
  exact hcard.trans hfcard

/-- The two stated arithmetic inputs imply finite continuous H² of the
actual maximal group and dimension at most six. -/
theorem maximalSigmaProTwoH2_finiteDimensional_finrank_le_of_finite_inputs
    (hcyc : ImaginaryFieldUnitsFiniteDetection)
    (hkernel : ∀ (U : OpenNormalSubgroup
      (maximalProPOutside 2 sigmaPrimeSupport ≃ₐ[ℚ]
        maximalProPOutside 2 sigmaPrimeSupport))
      (hmu : (primitiveRoots 2 ℚ).Nonempty),
      (finiteKummerContinuousH2Map ℚ (2 : ℕ+)
        (proPOpenNormalStage 2 sigmaPrimeSupport U).val hmu).ker ≤
      (continuousCohomologyZModPMapLifted 2
        (proPOpenNormalStageRestriction 2 sigmaPrimeSupport U) 2).hom.toLinearMap.toAddMonoidHom.ker)
    :
    FiniteDimensional (ZMod 2)
      (continuousCohomologyZModPLifted 2
        (maximalProPOutside 2 sigmaPrimeSupport ≃ₐ[ℚ]
          maximalProPOutside 2 sigmaPrimeSupport) 2) ∧
    Module.finrank (ZMod 2)
      (continuousCohomologyZModPLifted 2
        (maximalProPOutside 2 sigmaPrimeSupport ≃ₐ[ℚ]
          maximalProPOutside 2 sigmaPrimeSupport) 2) ≤ 6 := by
  let : IsGalois ℚ (maximalProPOutside 2 sigmaPrimeSupport) :=
    maximalProPOutside_isGalois 2 sigmaPrimeSupport
  exact finiteDimensional_and_finrank_degree_two_le_of_inflationRange_natCard 6
    (maximalProPOutside_galoisGroup_hasPGroupOpenNormalBasis
      2 sigmaPrimeSupport) (initialStage_inflationRange_natCard_le hcyc hkernel)

end UnitDistance.ArithmeticProP
