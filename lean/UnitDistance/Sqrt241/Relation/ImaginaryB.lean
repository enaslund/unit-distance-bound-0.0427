/-
B-analogues of `UnitDistance/ImaginaryQuadraticBase.lean`,
`UnitDistance/FiniteFieldImage.lean` and `UnitDistance/ImaginaryGaloisEnlargement.lean`:
the base ℚ is replaced by `B = ℚ(√241)` and `AlgebraicClosure ℚ` by
`AlgebraicClosure B`.
-/
module

public import UnitDistance.KummerInvariantRadicand
public import UnitDistance.Sqrt241.Base.Field
public import UnitDistance.Sqrt241.Base.SUnits
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.GaloisPCompositum
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.GroupTheory.PGroup
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The field `B(i)` and the enlargement `E ↦ E(i)` over `B`

`ImaginaryB.Carrier = B(√−1)` is a totally complex quadratic Galois extension
of `B` with cyclic Galois group of order two. Every finite Galois 2-extension
`L/B` embeds into the literal compositum `imaginaryGaloisEnlargement L` of the
images of `L` and `B(i)` in `AlgebraicClosure B`, again a finite Galois
2-extension of `B`, containing a square root of `−1`.
-/

noncomputable section

namespace UnitDistance.Sqrt241.Relation

namespace ImaginaryB

open QuadraticAlgebra UnitDistance.KummerInvariant NumberField Base

instance neg_one_nonsquare : Fact (Nonsquare (-1 : B)) :=
  ⟨fun s hs => not_isSquare_neg_one ⟨s, hs.symm.trans (sq s)⟩⟩

/-- The field `B(√−1)`. -/
abbrev Carrier := Extension (-1 : B)

/-- The adjoined square root of `−1`. -/
def root : Carrier := omega

@[simp] theorem root_sq : root ^ 2 = -1 := by
  ext <;> simp [root, pow_two]

theorem finrank : Module.finrank B Carrier = 2 := relative_finrank _

instance galois : IsGalois B Carrier :=
  isGalois_of_invariant (k := B) (-1 : B) (fun _ => ⟨1, by simp⟩)

theorem natCard_gal : Nat.card Gal(Carrier/B) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, finrank]

instance cyclic : IsCyclic Gal(Carrier/B) := by
  apply isCyclic_of_prime_card (p := 2)
  rw [IsGalois.card_aut_eq_finrank, finrank]

instance abelian : IsAbelianGalois B Carrier := IsAbelianGalois.of_isCyclic B Carrier

instance totallyComplex : IsTotallyComplex Carrier where
  isComplex w := InfinitePlace.isComplex_iff.mpr (by
    intro h
    have hs := congrArg h.embedding root_sq
    simp only [map_pow, map_neg, map_one] at hs
    nlinarith [sq_nonneg (h.embedding root)])

/-- The `B`-algebra homomorphism evaluating the adjoined root at a given square
root of `−1`. -/
def embedding {L : Type*} [Field L] [Algebra B L]
    (i : L) (hi : i ^ 2 = -1) : Carrier →ₐ[B] L :=
  QuadraticAlgebra.lift ⟨i, by simpa [pow_two] using hi⟩

end ImaginaryB

open NumberField Base

variable (K : Type) [Field K] [NumberField K] [Algebra B K] [FiniteDimensional B K]
  [IsGalois B K]

/-- A chosen embedding into the fixed algebraic closure of `B`. -/
def closureEmbedding : K →ₐ[B] AlgebraicClosure B := IsAlgClosed.lift

/-- The image of `K` in `AlgebraicClosure B`, a finite Galois intermediate field. -/
def finiteGaloisImage : FiniteGaloisIntermediateField B (AlgebraicClosure B) := by
  let f := closureEmbedding K
  exact { toIntermediateField := f.fieldRange
          finiteDimensional := f.equivFieldRange.toLinearEquiv.finiteDimensional
          isGalois := IsGalois.of_algEquiv f.equivFieldRange }

instance finiteGaloisImage_numberField : NumberField (finiteGaloisImage K) :=
  NumberField.of_module_finite B (finiteGaloisImage K)

/-- `K` is equivalent to its image. -/
def finiteGaloisImageEquiv : K ≃ₐ[B] finiteGaloisImage K :=
  (closureEmbedding K).equivFieldRange

theorem finiteGaloisImage_isPGroup {p : ℕ} (h : IsPGroup p (K ≃ₐ[B] K)) :
    IsPGroup p (finiteGaloisImage K ≃ₐ[B] finiteGaloisImage K) :=
  h.of_equiv (AlgEquiv.autCongr (finiteGaloisImageEquiv K))

variable (L : Type) [Field L] [NumberField L] [Algebra B L] [FiniteDimensional B L]
  [IsGalois B L]

/-- The compositum of the images of `L` and `B(i)` in `AlgebraicClosure B`. -/
def imaginaryGaloisEnlargement : FiniteGaloisIntermediateField B (AlgebraicClosure B) :=
  finiteGaloisImage L ⊔ finiteGaloisImage ImaginaryB.Carrier

instance imaginaryGaloisEnlargement_numberField :
    NumberField (imaginaryGaloisEnlargement L) :=
  NumberField.of_module_finite B _

/-- `L` embeds into its compositum with `B(i)`. -/
def imaginaryGaloisEnlargementEmbedding : L →ₐ[B] imaginaryGaloisEnlargement L :=
  (IntermediateField.inclusion (show (finiteGaloisImage L).toIntermediateField ≤
      (imaginaryGaloisEnlargement L).toIntermediateField from le_sup_left)).comp
    (finiteGaloisImageEquiv L).toAlgHom

/-- `B(i)` embeds into the same compositum. -/
def imaginaryGaloisEnlargementImaginaryEmbedding :
    ImaginaryB.Carrier →ₐ[B] imaginaryGaloisEnlargement L :=
  (IntermediateField.inclusion
      (show (finiteGaloisImage ImaginaryB.Carrier).toIntermediateField ≤
        (imaginaryGaloisEnlargement L).toIntermediateField from le_sup_right)).comp
    (finiteGaloisImageEquiv ImaginaryB.Carrier).toAlgHom

theorem imaginaryGaloisEnlargement_has_root :
    ∃ i : imaginaryGaloisEnlargement L, i ^ 2 = -1 := by
  refine ⟨imaginaryGaloisEnlargementImaginaryEmbedding L ImaginaryB.root, ?_⟩
  rw [← map_pow, ImaginaryB.root_sq, map_neg, map_one]

/-- The compositum remains a Galois 2-extension. -/
theorem imaginaryGaloisEnlargement_isPGroup (hP : IsPGroup 2 Gal(L/B)) :
    IsPGroup 2 Gal((imaginaryGaloisEnlargement L)/B) := by
  apply ClassFieldTower.Sawin.isPGroup_galois_sup
  · exact finiteGaloisImage_isPGroup L hP
  · apply finiteGaloisImage_isPGroup ImaginaryB.Carrier
    apply IsPGroup.of_card (n := 1)
    rw [IsGalois.card_aut_eq_finrank, ImaginaryB.finrank]
    norm_num

end UnitDistance.Sqrt241.Relation
