module

public import UnitDistance.KummerInvariantRadicand
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section
set_option backward.privateInPublic true


/-! The actual rational imaginary quadratic field and its canonical embedding
into every field with a displayed square root of minus one. -/
noncomputable section
namespace UnitDistance.ArithmeticProP.ImaginaryQuadratic
open QuadraticAlgebra UnitDistance.KummerInvariant NumberField

instance neg_one_nonsquare : Fact (Nonsquare (-1 : ℚ)) := ⟨by
  intro x hx
  nlinarith [sq_nonneg x]⟩

abbrev Carrier := Extension (-1 : ℚ)

def root : Carrier := omega

@[simp] theorem root_sq : root^2 = -1 := by
  ext <;> simp [root,pow_two]

theorem finrank : Module.finrank ℚ Carrier = 2 := relative_finrank _

instance galois : IsGalois ℚ Carrier :=
  isGalois_of_invariant (k := ℚ) (-1 : ℚ) (fun σ => ⟨1,by simp⟩)

instance cyclic : IsCyclic Gal(Carrier/ℚ) := by
  apply isCyclic_of_prime_card (p := 2)
  rw [IsGalois.card_aut_eq_finrank,finrank]

instance abelian : IsAbelianGalois ℚ Carrier := IsAbelianGalois.of_isCyclic ℚ Carrier

instance totallyComplex : IsTotallyComplex Carrier where
  isComplex w := InfinitePlace.isComplex_iff.mpr (by
    intro h
    have hs := congrArg h.embedding root_sq
    simp only [map_pow,map_neg,map_one] at hs
    nlinarith [sq_nonneg (h.embedding root)])

/-- The actual algebra homomorphism evaluating the formal imaginary root. -/
def embedding {L : Type*} [Field L] [Algebra ℚ L]
    (i : L) (hi : i^2 = -1) : Carrier →ₐ[ℚ] L :=
  QuadraticAlgebra.lift ⟨i,by simpa [pow_two] using hi⟩

@[simp] theorem embedding_root {L : Type*} [Field L] [Algebra ℚ L]
    (i : L) (hi : i^2 = -1) : embedding i hi root = i := by
  change (omega : Carrier).re • (1 : L) + (omega : Carrier).im • i = i
  simp

end UnitDistance.ArithmeticProP.ImaginaryQuadratic
