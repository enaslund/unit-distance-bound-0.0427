module

public import UnitDistance.RationalFiniteFieldUnitsH2Reduction
public import UnitDistance.SupportedIdeleOutsideH2
public import UnitDistance.SupportedIdeleLocalization
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerSPlaceCardinality

@[expose] public section
set_option backward.privateInPublic true


/-! The finite rational Kummer image has at most 2^|S| elements with infinite
places unrestricted. The single Q(i)/Q cyclic detection premise is explicit; the final global
norm wrapper will discharge it.
The elementary quotient-cardinality argument adapts FiniteKummerSPlaceCardinality
at Yamaguchi/Sawin commit3a455e1aa9140dbbe7b7d68f508392a69c86d0f4 (Apache-2.0). -/
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct
namespace UnitDistance.ArithmeticProP

-- Fix the actual completion algebra, which differs definitionally from the
-- generic rational algebra on a characteristic-zero field.
local instance kummerReductionAdicAlgebra (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (v.adicCompletion ℚ) :=
  HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
open ClassFieldTower.Martinet.Shafarevich

variable (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
local instance kummerReductionIdeleAction : MulDistribMulAction Gal(L/ℚ) (RelativeIdeleGroup ℚ L) :=
  RelativeIdeleGroup.relativeIdeleMulDistribMulAction ℚ L
local instance kummerReductionSupportedAction (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    MulDistribMulAction Gal(L/ℚ)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := ℚ) (L := L) S) :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := ℚ) (L := L) S
local instance kummerReductionTensorAction (v : HeightOneSpectrum (𝓞 ℚ)) :
    MulDistribMulAction Gal(L/ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)ˣ :=
  scalarTensorUnitsAction (K := ℚ) (L := L) (A := v.adicCompletion ℚ)

/-- The support-factorized Kummer coefficient has the actual tensor
localization as its literal finite coordinate. -/
theorem rationalKummerSupported_tensor_factor
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hmu : (primitiveRoots 2 ℚ).Nonempty) (v : HeightOneSpectrum (𝓞 ℚ)) :
    finiteKummerSSupportedIdeleRepHom ℚ L S (2 : ℕ+) hmu ≫
        supportedIdeleInclusionRepHom ℚ L S ≫ ideleFiniteRepHom ℚ L v =
      finiteKummerCoefficientRepHom ℚ L (2 : ℕ+) hmu ≫
        fieldUnitsTensorRepHom ℚ L (v.adicCompletion ℚ) := by
  ext z
  apply Units.ext
  rfl

/-- A rational Kummer class vanishing at S dies in field-unit H².
The discarded finite blocks are unramified; there is no infinity hypothesis. -/
theorem rationalFiniteKummerSPlaceH2Localization_ker_le_of_imaginary_detection
    (hcyc : ImaginaryFieldUnitsFiniteDetection)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hmu : (primitiveRoots 2 ℚ).Nonempty) (hP : IsPGroup 2 Gal(L/ℚ))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := ℚ) (L := L) v) :
    (finiteKummerSPlaceH2Localization ℚ L S (2 : ℕ+) hmu).ker ≤
      (finiteKummerCoefficientH2Map ℚ L (2 : ℕ+) hmu).hom.toAddMonoidHom.ker := by
  intro x hx
  change finiteKummerSPlaceH2Localization ℚ L S (2 : ℕ+) hmu x = 0 at hx
  change (finiteKummerCoefficientH2Map ℚ L (2 : ℕ+) hmu).hom x = 0
  apply rationalFieldUnitsH2_detection_of_imaginary_detection L hcyc hP
  intro v
  let C := groupCohomology.functor ℤ Gal(L/ℚ) 2
  let y := (C.map (finiteKummerSSupportedIdeleRepHom ℚ L S (2 : ℕ+) hmu)).hom x
  have hf := congrArg (fun f => (C.map f).hom x)
    (rationalKummerSupported_tensor_factor L S hmu v)
  simp only [Functor.map_comp] at hf
  change (ideleFiniteH2 ℚ L v).hom
      ((C.map (supportedIdeleInclusionRepHom ℚ L S)).hom y) =
    (fieldUnitsTensorH2 ℚ L (v.adicCompletion ℚ)).hom
      ((finiteKummerCoefficientH2Map ℚ L (2 : ℕ+) hmu).hom x) at hf
  rw [← hf]
  by_cases hv : v ∈ S
  · have hz := congrFun hx ⟨v,hv⟩
    change supportedSPlaceH2Localization ℚ L S y ⟨v,hv⟩ = 0 at hz
    rw [supportedIdeleH2_localization_eq ℚ L S y ⟨v,hv⟩] at hz
    exact hz
  · exact supportedIdeleH2_finite_eq_zero_of_unramified ℚ L S v hv (hfin v hv) y

private theorem range_finite_card_le_of_kernel
    {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : A →+ C) (hker : f.ker ≤ g.ker) [Finite f.range] :
    Finite g.range ∧ Nat.card g.range ≤ Nat.card f.range := by
  have hk : f.ker ≤ g.rangeRestrict.ker := by
    simpa only [AddMonoidHom.ker_rangeRestrict] using hker
  let q : A ⧸ f.ker →+ g.range := QuotientAddGroup.lift f.ker g.rangeRestrict hk
  have hq : Function.Surjective q :=
    QuotientAddGroup.lift_surjective_of_surjective f.ker g.rangeRestrict
      g.rangeRestrict_surjective hk
  let e := (QuotientAddGroup.quotientKerEquivRange f).symm
  have hsurj : Function.Surjective (fun x : f.range => q (e x)) := hq.comp e.surjective
  exact ⟨Finite.of_surjective _ hsurj,Nat.card_le_card_of_surjective _ hsurj⟩

/-- Every actual finite rational Galois 2-extension unramified outside S
has a field-unit Kummer image of cardinality at most 2^|S|. -/
theorem rationalFiniteKummerH2_range_finite_natCard_le_of_imaginary_detection
    (hcyc : ImaginaryFieldUnitsFiniteDetection)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hmu : (primitiveRoots 2 ℚ).Nonempty) (hP : IsPGroup 2 Gal(L/ℚ))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := ℚ) (L := L) v) :
    Finite (finiteKummerCoefficientH2Map ℚ L (2 : ℕ+) hmu).hom.toAddMonoidHom.range ∧
      Nat.card (finiteKummerCoefficientH2Map ℚ L (2 : ℕ+) hmu).hom.toAddMonoidHom.range ≤
        2 ^ S.card := by
  have hlocal := finiteKummerSPlaceH2Localization_range_finite_natCard_le
    ℚ L S (2 : ℕ+) hmu hP
  letI := hlocal.1
  have hfield := range_finite_card_le_of_kernel
    (finiteKummerSPlaceH2Localization ℚ L S (2 : ℕ+) hmu)
    (finiteKummerCoefficientH2Map ℚ L (2 : ℕ+) hmu).hom.toAddMonoidHom
    (rationalFiniteKummerSPlaceH2Localization_ker_le_of_imaginary_detection L hcyc S hmu hP hfin)
  exact ⟨hfield.1,hfield.2.trans hlocal.2⟩

end UnitDistance.ArithmeticProP
