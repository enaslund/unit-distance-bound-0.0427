module

public import UnitDistance.RetainedDyadicDifferentNorm
public import UnitDistance.RationalInertiaBaseChange
public import UnitDistance.DyadicIntrinsicBaseInertia
public import UnitDistance.AbsolutePrimeIndices

@[expose] public section
set_option backward.privateInPublic true


/-!
# The unramified retained complement

The first statements in this file isolate the exact local inertia kernel
needed to show that the retained extension above the ramified quadratic
direction is unramified.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped ValuativeRel
namespace UnitDistance
namespace ArithmeticDyadic

open NumberField LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open ArithmeticChosenGenus ArithmeticRetained Multiquadratic
local instance retainedComplementFactTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance retainedComplementNormedField : NontriviallyNormedField LocalField :=
  intrinsicNormedField
local instance retainedComplementValuativeRel : ValuativeRel LocalField :=
  intrinsicValuativeRel
local instance retainedComplementLocalField : IsNonarchimedeanLocalField LocalField :=
  intrinsicLocalField
local instance retainedComplementHasExtension :
    Valuation.HasExtension (ValuativeRel.valuation ℚ_[2])
      (ValuativeRel.valuation LocalField) := intrinsicHasExtension
local instance retainedComplementIntegralClosure :
    IsIntegralClosure 𝒪[LocalField] 𝒪[ℚ_[2]] LocalField := intrinsicIntegralClosure

/-- The actual ramified quadratic number field embedded in the dyadic base
change of the retained field. -/
def ramifiedLocalEmbedding : RamifiedField →ₐ[ℚ] LocalField :=
  retainedEmbedding.comp
    ((RamifiedQuadraticField.val).restrictScalars ℚ)

/-- Actual dyadic inertia acts faithfully on the quadratic field generated
by the genus field and the eleventh retained root. -/
theorem inertia_eq_one_of_model_base_zero_of_fix_root
    (sigma : Gal(LocalField/ℚ_[2])) (hsigma : sigma ∈ inertia)
    (hbase : (model sigma).base = 0)
    (hroot : restriction sigma (retainedRoot 11) = retainedRoot 11) :
    sigma = 1 := by
  let d : Dyadic.D := galoisEquiv.symm sigma
  have hgd : galoisEquiv d = sigma := galoisEquiv.apply_symm_apply sigma
  have hdI : galoisEquiv d ∈ intrinsicInertia := by
    rw [intrinsicInertia_eq]
    simpa only [hgd] using hsigma
  have hdbase : (dyadicModelMap d).base = 0 := by
    rw [← model_galoisEquiv, hgd]
    exact hbase
  rcases (galoisEquiv_mem_intrinsicInertia_and_base_zero_iff d).mp
      ⟨hdI, hdbase⟩ with hd | hd
  · rw [hd] at hgd
    simpa only [map_one] using hgd.symm
  · have hw : restriction (galoisEquiv Dyadic.D.w) (retainedRoot 11) =
        -retainedRoot 11 := by
      have hbit : (2048 : ℕ).testBit 11 = true := by decide
      simpa [RetainedQuadratic.binaryVector, binarySign, binarySignInteger,
        hbit] using
        restriction_galoisEquiv_w_action (11 : Fin 12)
    have hneg : -(retainedRoot 11) = retainedRoot 11 := by
      rw [← hw, ← hd, hgd]
      exact hroot
    exact (retainedRoot_ne_zero 11
      (CharZero.neg_eq_self_iff.mp hneg)).elim

/-- Equivalently, no nontrivial actual dyadic inertia element fixes the
embedded ramified quadratic field pointwise. -/
theorem inertia_eq_one_of_fixes_ramifiedLocalEmbedding
    (sigma : Gal(LocalField/ℚ_[2])) (hsigma : sigma ∈ inertia)
    (hfix : ∀ x : RamifiedField,
      sigma (ramifiedLocalEmbedding x) = ramifiedLocalEmbedding x) :
    sigma = 1 := by
  apply inertia_eq_one_of_model_base_zero_of_fix_root sigma hsigma
  · rw [model_base]
    apply ArithmeticRetained.genusVector_eq_zero_of_fixes
    intro a
    apply retainedEmbedding.injective
    calc
      retainedEmbedding
          (restriction sigma (algebraMap GenusField RetainedField a)) =
          sigma (retainedEmbedding
            (algebraMap GenusField RetainedField a)) :=
        RationalGaloisBaseChange.restriction_commutes RetainedField ℚ_[2]
          sigma (algebraMap GenusField RetainedField a)
      _ = retainedEmbedding (algebraMap GenusField RetainedField a) := by
        simpa [ramifiedLocalEmbedding] using
          hfix (algebraMap GenusField RamifiedField a)
  · apply retainedEmbedding.injective
    calc
      retainedEmbedding (restriction sigma (retainedRoot 11)) =
          sigma (retainedEmbedding (retainedRoot 11)) :=
        RationalGaloisBaseChange.restriction_commutes RetainedField ℚ_[2]
          sigma (retainedRoot 11)
      _ = retainedEmbedding (retainedRoot 11) := by
        simpa [ramifiedLocalEmbedding, ramifiedRoot] using hfix ramifiedRoot

end ArithmeticDyadic

namespace ArithmeticRetained

open ArithmeticChosenGenus ArithmeticCatalog Multiquadratic

/-- The same quadratic intermediate field, regarded as a rational
intermediate field of the retained field. -/
def RamifiedRationalField : IntermediateField ℚ RetainedField :=
  RamifiedQuadraticField.restrictScalars ℚ

/-- Every absolute retained automorphism preserves the displayed quadratic
field.  Squareclass invariance supplies the multiplier explicitly. -/
theorem absoluteAutomorphism_retainedRoot_eleven_mem_ramified
    (sigma : Gal(RetainedField/ℚ)) :
    sigma (retainedRoot 11) ∈ RamifiedQuadraticField := by
  let tau : Gal(GenusField/ℚ) := sigma.restrictNormal GenusField
  obtain ⟨u, hu⟩ := retainedRadicand_invariant 11 tau
  let y : RetainedField :=
    algebraMap GenusField RetainedField u * retainedRoot 11
  have hsquare : (sigma (retainedRoot 11)) ^ 2 = y ^ 2 := by
    calc
      (sigma (retainedRoot 11)) ^ 2 =
          sigma ((retainedRoot 11) ^ 2) := by rw [map_pow]
      _ = sigma (algebraMap GenusField RetainedField
          (retainedRadicand 11)) := by rw [retainedRoot_sq]
      _ = algebraMap GenusField RetainedField
          (tau (retainedRadicand 11)) := by
        rw [AlgEquiv.restrictNormal_commutes]
      _ = algebraMap GenusField RetainedField
          (retainedRadicand 11 * u ^ 2) := by rw [hu]
      _ = y ^ 2 := by
        dsimp [y]
        rw [map_mul, map_pow, mul_pow, retainedRoot_sq]
        ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with heq | heq
  · rw [heq]
    exact RamifiedQuadraticField.mul_mem
      (RamifiedQuadraticField.algebraMap_mem u)
      (IntermediateField.subset_adjoin GenusField _ (Set.mem_singleton _))
  · rw [heq]
    exact RamifiedQuadraticField.neg_mem
      (RamifiedQuadraticField.mul_mem
        (RamifiedQuadraticField.algebraMap_mem u)
        (IntermediateField.subset_adjoin GenusField _ (Set.mem_singleton _)))

/-- The ramified quadratic field is normal over the rationals. -/
noncomputable instance ramifiedRationalNormal :
    Normal ℚ RamifiedRationalField := by
  apply IntermediateField.normal_iff_forall_map_le'.2
  intro sigma
  rintro z ⟨x, hx, rfl⟩
  change sigma x ∈ RamifiedQuadraticField
  change x ∈ RamifiedQuadraticField at hx
  apply IntermediateField.adjoin_induction GenusField
    (s := ({retainedRoot 11} : Set RetainedField))
    (p := fun x _ => sigma x ∈ RamifiedQuadraticField) _ _ _ _ _ hx
  · intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact absoluteAutomorphism_retainedRoot_eleven_mem_ramified sigma
  · intro a
    rw [← AlgEquiv.restrictNormal_commutes sigma GenusField a]
    exact RamifiedQuadraticField.algebraMap_mem _
  · intro x y hx hy hxm hym
    simpa only [map_add] using RamifiedQuadraticField.add_mem hxm hym
  · intro x hx hxm
    simpa only [map_inv₀] using RamifiedQuadraticField.inv_mem hxm
  · intro x y hx hy hxm hym
    simpa only [map_mul] using RamifiedQuadraticField.mul_mem hxm hym

noncomputable instance ramifiedRationalGalois :
    IsGalois ℚ RamifiedRationalField where
  to_isSeparable := inferInstance
  to_normal := ramifiedRationalNormal

noncomputable instance ramifiedFieldRationalGalois :
    IsGalois ℚ RamifiedField := by
  change IsGalois ℚ RamifiedRationalField
  infer_instance

end ArithmeticRetained

namespace ArithmeticDyadic

open NumberField LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open ArithmeticChosenGenus ArithmeticRetained Multiquadratic
local instance retainedComplementRestrictionFactTwo : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩
local instance retainedComplementRestrictionNormedField :
    NontriviallyNormedField LocalField := intrinsicNormedField
local instance retainedComplementRestrictionValuativeRel : ValuativeRel LocalField :=
  intrinsicValuativeRel
local instance retainedComplementRestrictionLocalField :
    IsNonarchimedeanLocalField LocalField := intrinsicLocalField
local instance retainedComplementRestrictionHasExtension :
    Valuation.HasExtension (ValuativeRel.valuation ℚ_[2])
      (ValuativeRel.valuation LocalField) := intrinsicHasExtension
local instance retainedComplementRestrictionIntegralClosure :
    IsIntegralClosure 𝒪[LocalField] 𝒪[ℚ_[2]] LocalField := intrinsicIntegralClosure

/-- Restriction from the actual dyadic Galois group to the normal quadratic
number field. -/
def localRamifiedRestriction :
    Gal(LocalField/ℚ_[2]) →* Gal(RamifiedRationalField/ℚ) :=
  (AlgEquiv.restrictNormalHom RamifiedRationalField).comp restriction

theorem localRamifiedRestriction_eq_one_of_inertia
    (sigma : Gal(LocalField/ℚ_[2])) (hsigma : sigma ∈ inertia)
    (hres : localRamifiedRestriction sigma = 1) : sigma = 1 := by
  change (restriction sigma).restrictNormal RamifiedRationalField = 1 at hres
  apply inertia_eq_one_of_fixes_ramifiedLocalEmbedding sigma hsigma
  intro x
  have hglobal : restriction sigma (x : RetainedField) = (x : RetainedField) := by
    let xr : RamifiedRationalField := x
    have hx : (restriction sigma).restrictNormal RamifiedRationalField xr = xr := by
      have := DFunLike.congr_fun hres xr
      simpa only [AlgEquiv.one_apply] using this
    calc
      restriction sigma (x : RetainedField) =
          ((restriction sigma).restrictNormal RamifiedRationalField xr :
            RamifiedRationalField) :=
        (AlgEquiv.restrictNormal_apply RamifiedRationalField
          (restriction sigma) xr).symm
      _ = (x : RetainedField) := congrArg Subtype.val hx
  calc
    sigma (ramifiedLocalEmbedding x) =
        retainedEmbedding (restriction sigma (x : RetainedField)) :=
      (RationalGaloisBaseChange.restriction_commutes RetainedField ℚ_[2]
        sigma (x : RetainedField)).symm
    _ = ramifiedLocalEmbedding x := by
      rw [hglobal]
      rfl

theorem localRamifiedRestriction_injective_on_inertia :
    Function.Injective
      (localRamifiedRestriction.comp inertia.subtype) := by
  intro sigma tau heq
  apply Subtype.ext
  have hmem : (sigma : Gal(LocalField/ℚ_[2]))⁻¹ * tau ∈ inertia :=
    inertia.mul_mem (inertia.inv_mem sigma.property) tau.property
  have hone : localRamifiedRestriction
      ((sigma : Gal(LocalField/ℚ_[2]))⁻¹ * tau) = 1 := by
    change localRamifiedRestriction (sigma : Gal(LocalField/ℚ_[2])) =
      localRamifiedRestriction (tau : Gal(LocalField/ℚ_[2])) at heq
    rw [map_mul, map_inv, heq]
    simp
  have := localRamifiedRestriction_eq_one_of_inertia
    ((sigma : Gal(LocalField/ℚ_[2]))⁻¹ * tau) hmem hone
  exact inv_mul_eq_one.mp this

theorem localRamifiedInertiaImage_card :
    Nat.card (localRamifiedRestriction.comp inertia.subtype).range = 8 := by
  calc
    Nat.card (localRamifiedRestriction.comp inertia.subtype).range =
        Nat.card inertia := by
      simpa [MonoidHom.range_eq_map] using
        (Subgroup.card_map_of_injective
          (K := (⊤ : Subgroup inertia))
          localRamifiedRestriction_injective_on_inertia)
    _ = 8 := actual_residueDegree_inertia_card.2

theorem localRamifiedRestriction_commutes
    (sigma : Gal(LocalField/ℚ_[2])) (x : RamifiedRationalField) :
    ramifiedLocalEmbedding (localRamifiedRestriction sigma x) =
      sigma (ramifiedLocalEmbedding x) := by
  change retainedEmbedding
      (((restriction sigma).restrictNormal RamifiedRationalField x :
        RamifiedRationalField) : RetainedField) =
    sigma (retainedEmbedding (x : RetainedField))
  rw [AlgEquiv.restrictNormal_apply]
  exact RationalGaloisBaseChange.restriction_commutes
    RetainedField ℚ_[2] sigma (x : RetainedField)

section RationalBaseComparison

open ArithmeticProP LocalClassFieldTheory
attribute [local instance] PrimeCompletion.primeFact
  PrimeCompletion.baseRationalAlgebra
local instance complementRationalAlgebra : Algebra RationalBase LocalField :=
  PrimeCompletion.targetAlgebra rationalPrime LocalField
local instance complementRationalFinite : Module.Finite RationalBase LocalField :=
  PrimeCompletion.targetFinite rationalPrime LocalField
local instance complementRationalGalois : IsGalois RationalBase LocalField :=
  PrimeCompletion.targetGalois rationalPrime LocalField
local instance complementRationalNormed : NontriviallyNormedField LocalField :=
  intrinsicNormedField
local instance complementRationalValuative : ValuativeRel LocalField :=
  intrinsicValuativeRel
local instance complementRationalLocal : IsNonarchimedeanLocalField LocalField :=
  intrinsicLocalField
local instance complementRationalQpExtension :
    Valuation.HasExtension (ValuativeRel.valuation ℚ_[2])
      (ValuativeRel.valuation LocalField) := intrinsicHasExtension
local instance complementRationalCompatible :
    (PadicFiniteGalois.target 2 LocalField).valuation.Compatible :=
  PadicFiniteGalois.target_intrinsicCompatible 2 LocalField
local instance complementRationalBaseExtension :
    Valuation.HasExtension (ValuativeRel.valuation RationalBase)
      (ValuativeRel.valuation LocalField) :=
  PrimeCompletion.targetHasExtension rationalPrime LocalField
local instance complementRationalBaseIntegerAlgebra :
    Algebra 𝒪[RationalBase] LocalField :=
  Algebra.ofSubsemiring (ValuativeRel.valuation RationalBase).integer
local instance complementRationalBaseIntegral :
    IsIntegralClosure 𝒪[LocalField] 𝒪[RationalBase] LocalField :=
  localCompleteDVF_integerRing_isIntegralClosure RationalBase LocalField

def rationalBaseRamifiedRestriction :
    Gal(LocalField/RationalBase) →* Gal(RamifiedRationalField/ℚ) :=
  localRamifiedRestriction.comp
    (PrimeCompletion.galoisEquiv rationalPrime LocalField).toMonoidHom

theorem rationalBaseRamifiedRestriction_injective_on_inertia :
    Function.Injective
      (rationalBaseRamifiedRestriction.comp rationalBaseInertia.subtype) := by
  intro sigma tau heq
  let sigma' : Gal(LocalField/ℚ_[2]) :=
    PrimeCompletion.galoisEquiv rationalPrime LocalField sigma
  let tau' : Gal(LocalField/ℚ_[2]) :=
    PrimeCompletion.galoisEquiv rationalPrime LocalField tau
  have hsigma' : sigma' ∈ inertia :=
    (rationalBaseInertia_iff sigma).mp sigma.property
  have htau' : tau' ∈ inertia :=
    (rationalBaseInertia_iff tau).mp tau.property
  have heq' : localRamifiedRestriction sigma' =
      localRamifiedRestriction tau' := heq
  have heqsub : (localRamifiedRestriction.comp inertia.subtype)
      (⟨sigma', hsigma'⟩ : inertia) =
      (localRamifiedRestriction.comp inertia.subtype)
        (⟨tau', htau'⟩ : inertia) := heq'
  have hlocal := localRamifiedRestriction_injective_on_inertia heqsub
  exact Subtype.ext
    ((PrimeCompletion.galoisEquiv rationalPrime LocalField).injective
      (congrArg Subtype.val hlocal))

theorem rationalBaseRamifiedInertiaImage_card :
    Nat.card
      (rationalBaseRamifiedRestriction.comp rationalBaseInertia.subtype).range = 8 := by
  calc
    _ = Nat.card rationalBaseInertia := by
      simpa [MonoidHom.range_eq_map] using
        (Subgroup.card_map_of_injective
          (K := (⊤ : Subgroup rationalBaseInertia))
          rationalBaseRamifiedRestriction_injective_on_inertia)
    _ = Nat.card inertia := rationalBaseInertia_card
    _ = 8 := actual_residueDegree_inertia_card.2

def ramifiedAbsoluteEmbedding :
    RamifiedRationalField →ₐ[ℚ] AlgebraicClosure ℚ :=
  IsSepClosed.lift

def ramifiedLocalSeparableEmbedding
    (f : LocalField →ₐ[RationalBase] SeparableClosure RationalBase) :
    RamifiedRationalField →ₐ[ℚ] SeparableClosure RationalBase :=
  f.toRingHom.toRatAlgHom.comp ramifiedLocalEmbedding

theorem ramifiedLocalRestriction_absolute_commuting
    (f : LocalField →ₐ[RationalBase] SeparableClosure RationalBase) :
    (GaloisEmbedding.restriction
      (ramifiedLocalSeparableEmbedding f)).toMonoidHom.comp
        (AlgEquiv.restrictScalarsHom ℚ) =
      rationalBaseRamifiedRestriction.comp
        (finiteAbsoluteRestriction RationalBase LocalField f) := by
  apply MonoidHom.ext
  intro sigma
  apply GaloisEmbedding.restriction_unique
  intro x
  change f (ramifiedLocalEmbedding
      (rationalBaseRamifiedRestriction
        (finiteAbsoluteRestriction RationalBase LocalField f sigma) x)) =
    sigma (f (ramifiedLocalEmbedding x))
  rw [rationalBaseRamifiedRestriction, MonoidHom.comp_apply,
    localRamifiedRestriction_commutes]
  exact (finiteAbsoluteRestriction_commutes RationalBase LocalField f sigma
    (ramifiedLocalEmbedding x)).symm

/-- Absolute dyadic inertia has eight distinct images already on the normal
ramified quadratic number field. -/
theorem ramified_inertiaRestriction_card :
    Nat.card (PrimeCompletion.inertiaRestriction rationalPrime
      RamifiedRationalField ramifiedAbsoluteEmbedding).range = 8 := by
  let f : LocalField →ₐ[RationalBase] SeparableClosure RationalBase :=
    IsSepClosed.lift
  let I := (localResidueDegree RationalBase).toMonoidHom.ker
  let a : I →* Gal(SeparableClosure RationalBase/ℚ) :=
    (AlgEquiv.restrictScalarsHom ℚ).comp I.subtype
  have hc := GaloisEmbedding.restriction_image_card_eq
    ((PrimeCompletion.absoluteEmbedding rationalPrime).comp
      ramifiedAbsoluteEmbedding)
    (ramifiedLocalSeparableEmbedding f) a
  have hleft :
      ((GaloisEmbedding.restriction
        ((PrimeCompletion.absoluteEmbedding rationalPrime).comp
          ramifiedAbsoluteEmbedding)).toMonoidHom.comp a).range =
        (PrimeCompletion.inertiaRestriction rationalPrime
          RamifiedRationalField ramifiedAbsoluteEmbedding).range := by
    rw [PrimeCompletion.inertiaRestriction_range]
    change ((PrimeCompletion.localRestriction rationalPrime
      RamifiedRationalField ramifiedAbsoluteEmbedding).comp I.subtype).range =
      I.map (PrimeCompletion.localRestriction rationalPrime
        RamifiedRationalField ramifiedAbsoluteEmbedding)
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hright :
      ((GaloisEmbedding.restriction
        (ramifiedLocalSeparableEmbedding f)).toMonoidHom.comp a).range =
      (finiteAbsoluteInertiaImage RationalBase LocalField f).map
        rationalBaseRamifiedRestriction := by
    change (((GaloisEmbedding.restriction
      (ramifiedLocalSeparableEmbedding f)).toMonoidHom.comp
        (AlgEquiv.restrictScalarsHom ℚ)).comp I.subtype).range = _
    rw [ramifiedLocalRestriction_absolute_commuting,
      MonoidHom.comp_assoc, MonoidHom.range_comp,
      MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hfinite : finiteAbsoluteInertiaImage RationalBase LocalField f =
      rationalBaseInertia := by
    exact finiteAbsoluteInertiaImage_eq_residueInertia
      RationalBase LocalField f
  have hrightCard : Nat.card
      ((GaloisEmbedding.restriction
        (ramifiedLocalSeparableEmbedding f)).toMonoidHom.comp a).range = 8 := by
    rw [hright, hfinite]
    have hc := rationalBaseRamifiedInertiaImage_card
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at hc
    exact hc
  rw [hleft] at hc
  exact hc.trans hrightCard

def retainedAbsoluteEmbedding : RetainedField →ₐ[ℚ] AlgebraicClosure ℚ :=
  IsSepClosed.lift

theorem retained_inertiaRestriction_card :
    Nat.card (PrimeCompletion.inertiaRestriction rationalPrime
      RetainedField retainedAbsoluteEmbedding).range = 8 := by
  let f : LocalField →ₐ[RationalBase] SeparableClosure RationalBase :=
    IsSepClosed.lift
  rw [PrimeCompletion.inertiaRestriction_card_eq_baseChange rationalPrime
    RetainedField retainedAbsoluteEmbedding f,
    finiteAbsoluteInertiaImage_eq_residueInertia]
  change Nat.card rationalBaseInertia = 8
  rw [rationalBaseInertia_card, actual_residueDegree_inertia_card.2]

theorem ramifiedRationalField_dyadic_ramificationIdxIn :
    (NumberFieldAnalysis.rationalPrimeIdeal 2).ramificationIdxIn
      (RingOfIntegers RamifiedRationalField) = 8 := by
  rw [← PrimeCompletion.inertiaRestriction_card rationalPrime
    RamifiedRationalField ramifiedAbsoluteEmbedding]
  exact ramified_inertiaRestriction_card

theorem retainedField_dyadic_ramificationIdxIn :
    (NumberFieldAnalysis.rationalPrimeIdeal 2).ramificationIdxIn
      (RingOfIntegers RetainedField) = 8 := by
  rw [← PrimeCompletion.inertiaRestriction_card rationalPrime
    RetainedField retainedAbsoluteEmbedding]
  exact retained_inertiaRestriction_card

end RationalBaseComparison

end ArithmeticDyadic

namespace ArithmeticRetained

open NumberField ArithmeticChosenGenus QuadraticRamification
open IsDedekindDomain

/-- Odd-prime unramifiedness descends from the already proved
`GenusField`-relative statement by restriction of scalars. -/
theorem ramifiedComplement_unramifiedAtOddPrimes :
    UnramifiedAtOddPrimes RamifiedField RetainedField := by
  intro P hP htwo
  haveI : Algebra.IsUnramifiedAt (RingOfIntegers GenusField) P :=
    retainedField_unramifiedAtOddPrimes P htwo
  exact Algebra.IsUnramifiedAt.of_restrictScalars
    (RingOfIntegers GenusField) P

/-- The complementary retained extension is unramified at every finite
prime.  At two, both absolute ramification indices are eight; away from two,
the catalog local-unit proof descends by restriction of scalars. -/
theorem ramifiedComplement_finiteUnramified :
    NumberFieldAnalysis.FiniteUnramified RamifiedField RetainedField := by
  intro P hP
  letI : P.IsPrime := hP.isPrime
  by_cases htwo : (2 : RingOfIntegers RetainedField) ∈ P
  · let p := P.under (RingOfIntegers RamifiedField)
    let q := NumberFieldAnalysis.rationalPrimeIdeal 2
    haveI : p.IsPrime := Ideal.comap_isPrime _ P
    haveI : q.IsPrime := inferInstance
    have htwoZ : (2 : ℤ) ∈ P.under ℤ := by
      change algebraMap ℤ (RingOfIntegers RetainedField) (2 : ℤ) ∈ P
      simpa only [map_ofNat] using htwo
    have hqle : q ≤ P.under ℤ := by
      dsimp [q]
      rw [NumberFieldAnalysis.rationalPrimeIdeal,
        Ideal.span_singleton_le_iff_mem]
      exact htwoZ
    have hqunder : q = P.under ℤ :=
      Ideal.IsMaximal.eq_of_le (inferInstance : q.IsMaximal)
        (Ideal.IsPrime.ne_top (inferInstance : (P.under ℤ).IsPrime)) hqle
    letI : P.LiesOver p := inferInstance
    letI : P.LiesOver q := ⟨hqunder⟩
    letI : p.LiesOver q := by
      constructor
      change q = (P.under (RingOfIntegers RamifiedField)).under ℤ
      rw [Ideal.under_under]
      exact hqunder
    have hL : P.ramificationIdx ℤ = 8 := by
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx q P Gal(RetainedField/ℚ)]
      exact ArithmeticDyadic.retainedField_dyadic_ramificationIdxIn
    have hK : p.ramificationIdx ℤ = 8 := by
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx q p
        Gal(RamifiedField/ℚ)]
      exact ArithmeticDyadic.ramifiedRationalField_dyadic_ramificationIdxIn
    have ht := Ideal.ramificationIdx_tower (R := ℤ) p P
    have hrel : P.ramificationIdx (RingOfIntegers RamifiedField) = 1 := by
      rw [hL, hK] at ht
      omega
    exact Ideal.ramificationIdx_eq_one_iff.mp hrel
  · exact ramifiedComplement_unramifiedAtOddPrimes P htwo

theorem retainedRelativeDifferentTwoExponent_le :
    retainedRelativeDifferentTwoExponent ≤ 131072 :=
  retainedRelativeDifferentTwoExponent_le_of_finiteUnramifiedComplement
    ramifiedComplement_finiteUnramified

end ArithmeticRetained
end UnitDistance
