module

public import UnitDistance.TensorBaseChangeH2

@[expose] public section
set_option backward.privateInPublic true


noncomputable section
open CategoryTheory
namespace UnitDistance.ArithmeticProP
variable (K L : Type) [Field K] [Field L] [Algebra K L]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction through the identity base extension is the identity map. -/
theorem fieldUnitsRestrictionH2_self :
    fieldUnitsRestrictionH2 K K L = 𝟙 _ := by
  unfold fieldUnitsRestrictionH2
  calc
    _ = groupCohomology.map (MonoidHom.id Gal(L/K))
        (𝟙 (Rep.ofAlgebraAutOnUnits K L)) 2 := by
      apply groupCohomology.map_congr
      · ext σ x
        rfl
      · apply LinearMap.ext
        intro x
        rfl
    _ = _ := by simp only [groupCohomology.map_id]

/-- Actual tensor-local vanishing is preserved by changing the coefficient
algebra through a K-algebra homomorphism. -/
theorem fieldUnitsTensorH2_eq_zero_of_coefficients
    (A B : Type) [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B) (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : (fieldUnitsTensorH2 K L A).hom x = 0) :
    (fieldUnitsTensorH2 K L B).hom x = 0 := by
  have h := fieldUnitsTensorRestriction_eq_zero_of_eq_zero K K L A B f x hx
  rwa [fieldUnitsRestrictionH2_self] at h

/-- Equivalent coefficient algebras give exactly the same vanishing test. -/
theorem fieldUnitsTensorH2_eq_zero_iff_coefficients
    (A B : Type) [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    (fieldUnitsTensorH2 K L A).hom x = 0 ↔
      (fieldUnitsTensorH2 K L B).hom x = 0 :=
  ⟨fieldUnitsTensorH2_eq_zero_of_coefficients K L A B e.toAlgHom x,
   fieldUnitsTensorH2_eq_zero_of_coefficients K L B A e.symm.toAlgHom x⟩

end UnitDistance.ArithmeticProP
