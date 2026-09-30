module

public import UnitDistance.KummerInvariantRadicand
public import UnitDistance.GaloisConjugationFixedField

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual quadratic presentation over a conjugation fixed field

A displayed square root of minus one and a proved relative degree two
produce an actual algebra equivalence with the quadratic algebra. The
conjugation-fixed-field case supplies nonsquareness using its actual real
embedding.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ConjugationQuadratic
open QuadraticAlgebra KummerInvariant NumberField NumberField.ComplexEmbedding

variable {F K : Type*} [Field F] [CharZero F] [Field K] [Algebra F K]

/-- The actual evaluation map sending the formal imaginary root to the displayed root. -/
def imaginaryHom (i : K) (hi : i^2 = -1) : Extension (-1 : F) →ₐ[F] K :=
  QuadraticAlgebra.lift ⟨i,by simpa [pow_two] using hi⟩

@[simp] theorem imaginaryHom_root (i : K) (hi : i^2 = -1) :
    imaginaryHom (F := F) i hi omega = i := by
  change (omega : Extension (-1 : F)).re • (1 : K) +
    (omega : Extension (-1 : F)).im • i = i
  simp

/-- The actual imaginary quadratic presentation follows from the actual degree. -/
def imaginaryEquiv [Fact (Nonsquare (-1 : F))]
    (i : K) (hi : i^2 = -1) (hdegree : Module.finrank F K = 2) :
    Extension (-1 : F) ≃ₐ[F] K := by
  let f := imaginaryHom (F := F) i hi
  haveI : Module.Finite F K := FiniteDimensional.of_finrank_pos (by omega)
  have hdim : Module.finrank F (LinearMap.range f.toLinearMap) = Module.finrank F K := by
    calc
      Module.finrank F (LinearMap.range f.toLinearMap) =
          Module.finrank F (Extension (-1 : F)) :=
        (LinearEquiv.ofInjective f.toLinearMap f.injective).finrank_eq.symm
      _ = 2 := QuadraticAlgebra.finrank_eq_two _ _
      _ = Module.finrank F K := hdegree.symm
  exact AlgEquiv.ofBijective f ⟨f.injective,
    LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hdim)⟩

@[simp] theorem imaginaryEquiv_root [Fact (Nonsquare (-1 : F))]
    (i : K) (hi : i^2 = -1) (hdegree : Module.finrank F K = 2) :
    imaginaryEquiv (F := F) i hi hdegree omega = i := imaginaryHom_root i hi

end UnitDistance.ConjugationQuadratic

namespace UnitDistance.ConjugationQuadratic
open QuadraticAlgebra KummerInvariant NumberField NumberField.ComplexEmbedding
variable {K : Type*} [Field K] [NumberField K]
  (φ : K →+* ℂ) (c : Gal(K/ℚ)) (hc : IsConj φ c)

include φ hc

/-- An actual real embedding proves that minus one is genuinely nonsquare. -/
theorem fixedField_neg_one_nonsquare : Nonsquare (-1 : GaloisConjugation.fixedField K c) := by
  let ψ := GaloisConjugation.realEmbedding φ c hc
  intro x hx
  have h := congrArg ψ hx
  simp only [map_pow,map_neg,map_one] at h
  nlinarith [sq_nonneg (ψ x)]

/-- The explicit actual imaginary quadratic presentation of K over its
actual conjugation fixed field. -/
def fixedFieldImaginaryEquiv (hc1 : c ≠ 1) (i : K) (hi : i^2 = -1) :
    Extension (-1 : GaloisConjugation.fixedField K c) ≃ₐ[GaloisConjugation.fixedField K c] K := by
  letI : Fact (Nonsquare (-1 : GaloisConjugation.fixedField K c)) :=
    ⟨fixedField_neg_one_nonsquare φ c hc⟩
  exact imaginaryEquiv i hi (GaloisConjugation.relativeDegree_eq_two φ c hc hc1)

@[simp] theorem fixedFieldImaginaryEquiv_root (hc1 : c ≠ 1) (i : K) (hi : i^2 = -1) :
    fixedFieldImaginaryEquiv φ c hc hc1 i hi omega = i := by
  letI : Fact (Nonsquare (-1 : GaloisConjugation.fixedField K c)) :=
    ⟨fixedField_neg_one_nonsquare φ c hc⟩
  change imaginaryEquiv i hi (GaloisConjugation.relativeDegree_eq_two φ c hc hc1) omega = i
  exact imaginaryEquiv_root _ _ _

end UnitDistance.ConjugationQuadratic
