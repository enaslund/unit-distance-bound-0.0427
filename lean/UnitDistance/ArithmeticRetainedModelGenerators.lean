module

public import UnitDistance.ArithmeticRetainedCharacters
public import UnitDistance.CatalogRetainedCoordinates

@[expose] public section
set_option backward.privateInPublic true


/-! Actual seven genus lifts and actual twelve central coordinates for the
retained field, satisfying the independently specified bilinear model's
involution and commutation equations. -/
noncomputable section
namespace UnitDistance.ArithmeticRetained
open ArithmeticChosenGenus Multiquadratic

/-- Restriction to the actual genus field is surjective. -/
theorem genusVector_surjective : Function.Surjective genusVector := by
  intro v
  obtain ⟨σ,hσ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := ℚ) (K₁ := GenusField) (E := RetainedField) (signAutomorphism v)
  refine ⟨σ,?_⟩
  change (genusGaloisEquiv.symm (σ.restrictNormal GenusField)).toAdd=v
  rw [show σ.restrictNormal GenusField=signAutomorphism v from hσ]
  exact congrArg Multiplicative.toAdd (genusGaloisEquiv.symm_apply_apply (Multiplicative.ofAdd v))

/-- Any actual lift of each fixed genus basis element. -/
def basisLift (i : Fin 7) : Gal(RetainedField/ℚ) :=
  (genusVector_surjective (Pi.single i 1)).choose

theorem genusVector_basisLift (i : Fin 7) : genusVector (basisLift i)=Pi.single i 1 :=
  (genusVector_surjective (Pi.single i 1)).choose_spec

theorem basisLift_square (i : Fin 7) : basisLift i^2=1 :=
  basis_lift_square _ i (genusVector_basisLift i)

/-- Actual automorphisms are determined by genus elements and the twelve selected roots. -/
theorem retained_aut_ext_roots {σ τ : Gal(RetainedField/ℚ)}
    (hbase : ∀ a : GenusField, σ (algebraMap GenusField RetainedField a)=
      τ (algebraMap GenusField RetainedField a))
    (hroots : ∀ j, σ (retainedRoot j)=τ (retainedRoot j)) : σ=τ := by
  apply retained_aut_ext _ _ hbase
  rintro x ⟨j,hj,hx⟩
  have hs : x^2=(retainedRoot j)^2 := hx.trans (retainedRoot_sq j).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
  · simpa only [hs] using hroots j
  · simpa only [hs,map_neg] using congrArg Neg.neg (hroots j)

/-- Actual central automorphisms in the model's independently specified coordinates. -/
def modelCentral : Multiplicative RetainedQuadratic.W →* Gal(RetainedField/ℚ) where
  toFun v := centralSignHom (Multiplicative.ofAdd (CatalogRetainedCoordinates.toSigns v.toAdd))
  map_one' := by
    change centralSignHom (Multiplicative.ofAdd (CatalogRetainedCoordinates.toSigns 0))=1
    rw [map_zero]
    exact centralSignHom.map_one
  map_mul' v w := by
    change centralSignHom (Multiplicative.ofAdd (CatalogRetainedCoordinates.toSigns (v.toAdd+w.toAdd)))=_
    rw [map_add]
    exact centralSignHom.map_mul _ _

theorem modelCentral_action (v : Multiplicative RetainedQuadratic.W) (j : Fin 12) :
    modelCentral v (retainedRoot j)=
      binarySign (CatalogRetainedCoordinates.toSigns v.toAdd j)*retainedRoot j :=
  centralSignHom_action _ j

theorem modelCentral_fixes_genus (v : Multiplicative RetainedQuadratic.W) (a : GenusField) :
    modelCentral v (algebraMap GenusField RetainedField a)=algebraMap GenusField RetainedField a :=
  centralSignHom_fixes_genus _ a

theorem modelCentral_central (v : Multiplicative RetainedQuadratic.W) (σ : Gal(RetainedField/ℚ)) :
    Commute (modelCentral v) σ := centralSignHom_central _ σ

theorem modelCentral_injective : Function.Injective modelCentral := by
  intro v w h
  apply Multiplicative.toAdd.injective
  apply CatalogRetainedCoordinates.fromSigns_leftInverse.injective
  exact congrArg Multiplicative.toAdd (centralSignHom_injective h)

/-- Actual commutators of the lifted genus basis have precisely the model's central values. -/
theorem basisLift_commutator (i j : Fin 7) :
    (basisLift i)⁻¹*(basisLift j)⁻¹*basisLift i*basisLift j =
      modelCentral (Multiplicative.ofAdd
        (RetainedQuadratic.cocycle (Pi.single i 1) (Pi.single j 1)+
         RetainedQuadratic.cocycle (Pi.single j 1) (Pi.single i 1))) := by
  apply retained_aut_ext_roots
  · intro a
    rw [modelCentral_fixes_genus]
    exact fixes_genus_of_vector_zero _ (commutator_genusVector _ _) a
  · intro k
    rw [commutator_action_on_radical _ _ k _ (retainedRoot_sq k),
      modelCentral_action,genusVector_basisLift,genusVector_basisLift,
      retainedForm_basis_zero,retainedForm_basis_zero,add_zero,add_zero]
    exact congrArg (fun t => binarySign (E := RetainedField) t*retainedRoot k)
      (CatalogRetainedCoordinates.cocycle_polar_certificate i j k).symm

theorem basisLift_swap (i j : Fin 7) :
    basisLift i*basisLift j =
      modelCentral (Multiplicative.ofAdd
        (RetainedQuadratic.cocycle (Pi.single i 1) (Pi.single j 1)+
         RetainedQuadratic.cocycle (Pi.single j 1) (Pi.single i 1)))*basisLift j*basisLift i := by
  calc
    basisLift i*basisLift j = (basisLift j*basisLift i)*
        ((basisLift i)⁻¹*(basisLift j)⁻¹*basisLift i*basisLift j) := by group
    _ = _ := by
      rw [basisLift_commutator,(modelCentral_central _ (basisLift j*basisLift i)).symm.eq]
      group

end UnitDistance.ArithmeticRetained
