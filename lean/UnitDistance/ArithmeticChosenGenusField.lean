module

public import UnitDistance.GeneratedQuadraticTower
public import UnitDistance.GeneratedQuadraticGalois
public import UnitDistance.QuadraticRationalSignLift
public import Mathlib.Data.Rat.Sqrt

@[expose] public section
set_option backward.privateInPublic true


/-!
# A generated actual genus field with a compact field interface

The field is chosen from the proved actual quadratic-tower construction on
seven independent rational squareclasses. Its degree and generation by actual
roots are conclusions, with no assigned field or Galois-group invariants.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticChosenGenus
open Multiquadratic

abbrev radicands : Fin 7 → ℚ := ![-1,2,3,5,7,11,13]

theorem radicands_ne_zero (i : Fin 7) : radicands i ≠ 0 := by
  have h : ∀ i : Fin 7, radicands i ≠ 0 := by decide +kernel
  exact h i

theorem rational_products_nonsquare (s : Finset (Fin 7)) (hs : s.Nonempty) :
    ¬IsSquare (∏ i ∈ s, radicands i) := by
  have h : ∀ s : Finset (Fin 7), s.Nonempty → ¬IsSquare (∏ i ∈ s, radicands i) := by
    decide +kernel
  exact h s hs

theorem radicands_invariant (i : Fin 7) (σ : Gal(ℚ/ℚ)) :
    ∃ u : ℚ, radicands i*u^2 = σ (radicands i) := by
  refine ⟨1,?_⟩
  simpa using (σ.commutes (radicands i)).symm

def genusTower : GeneratedGaloisTower ℚ radicands Finset.univ :=
  Classical.choice (exists_generatedGaloisTower ℚ radicands radicands_ne_zero
    rational_products_nonsquare radicands_invariant Finset.univ)

abbrev GenusField := genusTower.Carrier

instance genusField_field : Field GenusField := genusTower.field
instance genusField_charZero : CharZero GenusField := genusTower.charZero
instance genusField_algebraRat : Algebra ℚ GenusField := DivisionRing.toRatAlgebra

theorem genusTower_algebra_eq : genusTower.algebra = genusField_algebraRat :=
  Subsingleton.elim _ _

instance genusField_finite : Module.Finite ℚ GenusField := by
  rw [← genusTower_algebra_eq]
  exact genusTower.finite

instance genusField_galois : IsGalois ℚ GenusField := by
  rw [← genusTower_algebra_eq]
  exact genusTower.galois

instance genusField_numberField : NumberField GenusField where
  to_finiteDimensional := genusField_finite

theorem genusField_degree : Module.finrank ℚ GenusField = 128 := by
  rw [← genusTower_algebra_eq]
  simpa using genusTower.degree

theorem genusField_galoisGroup_card : Nat.card (Gal(GenusField/ℚ)) = 128 := by
  rw [IsGalois.card_aut_eq_finrank,genusField_degree]

theorem genusField_has_root (i : Fin 7) :
    ∃ x : GenusField, x^2=(radicands i : GenusField) := by
  have h := genusTower.toActualGaloisTower.toActualTower.isSquare_radical i
    (Finset.mem_univ i) (radicands_ne_zero i)
  obtain ⟨x,hx⟩ := h
  exact ⟨x,by simpa [pow_two] using hx.symm⟩

def roots (i : Fin 7) : GenusField := (genusField_has_root i).choose

theorem roots_sq (i : Fin 7) : (roots i)^2=(radicands i : GenusField) :=
  (genusField_has_root i).choose_spec

theorem roots_ne_zero (i : Fin 7) : roots i ≠ 0 := by
  have h : (radicands i : GenusField) ≠ 0 := by exact_mod_cast radicands_ne_zero i
  intro hz
  have he := roots_sq i
  rw [hz,zero_pow (by decide : 2 ≠ 0)] at he
  exact h he.symm

theorem genusField_generated :
    Algebra.adjoin ℚ (radicalSet (L := GenusField) radicands Finset.univ) = ⊤ := by
  rw [← genusTower_algebra_eq]
  exact genusTower.generated

end UnitDistance.ArithmeticChosenGenus
