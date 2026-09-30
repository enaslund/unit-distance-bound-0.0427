module

public import UnitDistance.ArithmeticChosenGenusField
public import UnitDistance.CoprimeDiscriminantCompositum
public import UnitDistance.GeneratedQuadraticEmbedding
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.QuadraticFieldDiscriminant
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.QuadraticClosure
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The exact discriminant of the seven-radical genus field

The genus field is reconstructed as the compositum of the eighth cyclotomic
field and the five quadratic fields with signed fundamental radicands
`-3, 5, -7, -11, 13`.  Their discriminants are pairwise coprime.  Repeated
application of the coprime-compositum formula therefore computes the exact
discriminant.  A degree-preserving embedding then identifies this compositum
with the independently generated genus field used by the arithmetic proof.
-/

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace UnitDistance.GenusDiscriminant

open NumberField
open ClassFieldTower.Sawin
open CoprimeDiscriminantCompositum
open AlgebraicNumberTheory

private theorem nonsquare_negThree : ¬ IsSquare (-3 : ℚ) := by norm_num
private theorem nonsquare_five : ¬ IsSquare (5 : ℚ) := by norm_num
private theorem nonsquare_negSeven : ¬ IsSquare (-7 : ℚ) := by norm_num
private theorem nonsquare_negEleven : ¬ IsSquare (-11 : ℚ) := by norm_num
private theorem nonsquare_thirteen : ¬ IsSquare (13 : ℚ) := by norm_num

/-- The dyadic genus component `Q(zeta_8)`. -/
abbrev Dyadic := CyclotomicField 8 ℚ

private instance eightRatNeZero : NeZero (8 : ℚ) := ⟨by norm_num⟩
noncomputable instance dyadicCyclotomic :
    IsCyclotomicExtension {8} ℚ Dyadic :=
  CyclotomicField.isCyclotomicExtension 8 ℚ

/-- The five odd quadratic components, using their signed fundamental
discriminants as radicands. -/
abbrev QNegThree := quadraticClosure (-3 : ℚ) nonsquare_negThree
abbrev QFive := quadraticClosure (5 : ℚ) nonsquare_five
abbrev QNegSeven := quadraticClosure (-7 : ℚ) nonsquare_negSeven
abbrev QNegEleven := quadraticClosure (-11 : ℚ) nonsquare_negEleven
abbrev QThirteen := quadraticClosure (13 : ℚ) nonsquare_thirteen

noncomputable instance qNegThreeNumberField : NumberField QNegThree :=
  NumberField.of_module_finite ℚ QNegThree
noncomputable instance qFiveNumberField : NumberField QFive :=
  NumberField.of_module_finite ℚ QFive
noncomputable instance qNegSevenNumberField : NumberField QNegSeven :=
  NumberField.of_module_finite ℚ QNegSeven
noncomputable instance qNegElevenNumberField : NumberField QNegEleven :=
  NumberField.of_module_finite ℚ QNegEleven
noncomputable instance qThirteenNumberField : NumberField QThirteen :=
  NumberField.of_module_finite ℚ QThirteen

instance qNegThreeQuadratic : Algebra.IsQuadraticExtension ℚ QNegThree :=
  quadraticClosure_isQuadraticExtension (-3 : ℚ) nonsquare_negThree
instance qFiveQuadratic : Algebra.IsQuadraticExtension ℚ QFive :=
  quadraticClosure_isQuadraticExtension (5 : ℚ) nonsquare_five
instance qNegSevenQuadratic : Algebra.IsQuadraticExtension ℚ QNegSeven :=
  quadraticClosure_isQuadraticExtension (-7 : ℚ) nonsquare_negSeven
instance qNegElevenQuadratic : Algebra.IsQuadraticExtension ℚ QNegEleven :=
  quadraticClosure_isQuadraticExtension (-11 : ℚ) nonsquare_negEleven
instance qThirteenQuadratic : Algebra.IsQuadraticExtension ℚ QThirteen :=
  quadraticClosure_isQuadraticExtension (13 : ℚ) nonsquare_thirteen

noncomputable instance dyadicAbelian : IsAbelianGalois ℚ Dyadic :=
  IsCyclotomicExtension.isAbelianGalois {8} ℚ Dyadic

noncomputable instance qNegThreeAbelian : IsAbelianGalois ℚ QNegThree :=
  IsAbelianGalois.mk
noncomputable instance qFiveAbelian : IsAbelianGalois ℚ QFive :=
  IsAbelianGalois.mk
noncomputable instance qNegSevenAbelian : IsAbelianGalois ℚ QNegSeven :=
  IsAbelianGalois.mk
noncomputable instance qNegElevenAbelian : IsAbelianGalois ℚ QNegEleven :=
  IsAbelianGalois.mk
noncomputable instance qThirteenAbelian : IsAbelianGalois ℚ QThirteen :=
  IsAbelianGalois.mk

theorem dyadic_degree : Module.finrank ℚ Dyadic = 4 := by
  rw [IsCyclotomicExtension.Rat.finrank 8 Dyadic]
  decide +kernel

theorem qNegThree_degree : Module.finrank ℚ QNegThree = 2 :=
  quadraticClosure_finrank (-3 : ℚ) nonsquare_negThree
theorem qFive_degree : Module.finrank ℚ QFive = 2 :=
  quadraticClosure_finrank (5 : ℚ) nonsquare_five
theorem qNegSeven_degree : Module.finrank ℚ QNegSeven = 2 :=
  quadraticClosure_finrank (-7 : ℚ) nonsquare_negSeven
theorem qNegEleven_degree : Module.finrank ℚ QNegEleven = 2 :=
  quadraticClosure_finrank (-11 : ℚ) nonsquare_negEleven
theorem qThirteen_degree : Module.finrank ℚ QThirteen = 2 :=
  quadraticClosure_finrank (13 : ℚ) nonsquare_thirteen

theorem dyadic_natAbs_discr : (discr Dyadic).natAbs = 2 ^ 8 := by
  rw [IsCyclotomicExtension.Rat.natAbs_discr 8 Dyadic]
  rw [show Nat.totient 8 = 4 by decide +kernel]
  rw [show Nat.primeFactors 8 = {2} by decide +kernel]
  norm_num

theorem qNegThree_discr : discr QNegThree = -3 := by
  exact numberField_discr_of_mod_four_eq_one QNegThree (-3) (by decide +kernel)
    (quadraticClosureGenerator (-3 : ℚ) nonsquare_negThree)
    (quadraticClosureGenerator_sq (-3 : ℚ) nonsquare_negThree)
    (quadraticClosureGenerator_adjoin (-3 : ℚ) nonsquare_negThree) (by norm_num)

theorem qFive_discr : discr QFive = 5 := by
  exact numberField_discr_of_mod_four_eq_one QFive 5 (by decide +kernel)
    (quadraticClosureGenerator (5 : ℚ) nonsquare_five)
    (quadraticClosureGenerator_sq (5 : ℚ) nonsquare_five)
    (quadraticClosureGenerator_adjoin (5 : ℚ) nonsquare_five) (by norm_num)

theorem qNegSeven_discr : discr QNegSeven = -7 := by
  exact numberField_discr_of_mod_four_eq_one QNegSeven (-7) (by decide +kernel)
    (quadraticClosureGenerator (-7 : ℚ) nonsquare_negSeven)
    (quadraticClosureGenerator_sq (-7 : ℚ) nonsquare_negSeven)
    (quadraticClosureGenerator_adjoin (-7 : ℚ) nonsquare_negSeven) (by norm_num)

theorem qNegEleven_discr : discr QNegEleven = -11 := by
  exact numberField_discr_of_mod_four_eq_one QNegEleven (-11) (by decide +kernel)
    (quadraticClosureGenerator (-11 : ℚ) nonsquare_negEleven)
    (quadraticClosureGenerator_sq (-11 : ℚ) nonsquare_negEleven)
    (quadraticClosureGenerator_adjoin (-11 : ℚ) nonsquare_negEleven) (by norm_num)

theorem qThirteen_discr : discr QThirteen = 13 := by
  exact numberField_discr_of_mod_four_eq_one QThirteen 13 (by decide +kernel)
    (quadraticClosureGenerator (13 : ℚ) nonsquare_thirteen)
    (quadraticClosureGenerator_sq (13 : ℚ) nonsquare_thirteen)
    (quadraticClosureGenerator_adjoin (13 : ℚ) nonsquare_thirteen) (by norm_num)

theorem qNegThree_natAbs_discr : (discr QNegThree).natAbs = 3 := by
  rw [qNegThree_discr]
  norm_num
theorem qFive_natAbs_discr : (discr QFive).natAbs = 5 := by
  rw [qFive_discr]
  norm_num
theorem qNegSeven_natAbs_discr : (discr QNegSeven).natAbs = 7 := by
  rw [qNegSeven_discr]
  norm_num
theorem qNegEleven_natAbs_discr : (discr QNegEleven).natAbs = 11 := by
  rw [qNegEleven_discr]
  norm_num
theorem qThirteen_natAbs_discr : (discr QThirteen).natAbs = 13 := by
  rw [qThirteen_discr]
  norm_num

/-- Successive concrete composita of the six pairwise-coprime components. -/
abbrev C1 := Carrier Dyadic QNegThree
noncomputable instance C1NumberField : NumberField C1 :=
  carrierNumberField Dyadic QNegThree
noncomputable instance C1Abelian : IsAbelianGalois ℚ C1 :=
  finiteAbelianCompositumField_isAbelianGalois ℚ Dyadic QNegThree

abbrev C2 := Carrier C1 QFive
noncomputable instance C2NumberField : NumberField C2 :=
  carrierNumberField C1 QFive
noncomputable instance C2Abelian : IsAbelianGalois ℚ C2 :=
  finiteAbelianCompositumField_isAbelianGalois ℚ C1 QFive

abbrev C3 := Carrier C2 QNegSeven
noncomputable instance C3NumberField : NumberField C3 :=
  carrierNumberField C2 QNegSeven
noncomputable instance C3Abelian : IsAbelianGalois ℚ C3 :=
  finiteAbelianCompositumField_isAbelianGalois ℚ C2 QNegSeven

abbrev C4 := Carrier C3 QNegEleven
noncomputable instance C4NumberField : NumberField C4 :=
  carrierNumberField C3 QNegEleven
noncomputable instance C4Abelian : IsAbelianGalois ℚ C4 :=
  finiteAbelianCompositumField_isAbelianGalois ℚ C3 QNegEleven

abbrev C5 := Carrier C4 QThirteen
noncomputable instance C5NumberField : NumberField C5 :=
  carrierNumberField C4 QThirteen
noncomputable instance C5Abelian : IsAbelianGalois ℚ C5 :=
  finiteAbelianCompositumField_isAbelianGalois ℚ C4 QThirteen

theorem C1_degree : Module.finrank ℚ C1 = 8 := by
  rw [finrank_eq_mul Dyadic QNegThree]
  · rw [dyadic_degree, qNegThree_degree]
  · rw [dyadic_natAbs_discr, qNegThree_natAbs_discr]
    norm_num

theorem C1_natAbs_discr : (discr C1).natAbs = 2 ^ 16 * 3 ^ 4 := by
  rw [natAbs_discr_eq Dyadic QNegThree]
  · rw [dyadic_degree, qNegThree_degree, dyadic_natAbs_discr,
      qNegThree_natAbs_discr]
    ring
  · rw [dyadic_natAbs_discr, qNegThree_natAbs_discr]
    norm_num

theorem C2_degree : Module.finrank ℚ C2 = 16 := by
  rw [finrank_eq_mul C1 QFive]
  · rw [C1_degree, qFive_degree]
  · rw [C1_natAbs_discr, qFive_natAbs_discr]
    norm_num

theorem C2_natAbs_discr : (discr C2).natAbs = 2 ^ 32 * 3 ^ 8 * 5 ^ 8 := by
  rw [natAbs_discr_eq C1 QFive]
  · rw [C1_degree, qFive_degree, C1_natAbs_discr, qFive_natAbs_discr]
    ring
  · rw [C1_natAbs_discr, qFive_natAbs_discr]
    norm_num

theorem C3_degree : Module.finrank ℚ C3 = 32 := by
  rw [finrank_eq_mul C2 QNegSeven]
  · rw [C2_degree, qNegSeven_degree]
  · rw [C2_natAbs_discr, qNegSeven_natAbs_discr]
    norm_num

theorem C3_natAbs_discr :
    (discr C3).natAbs = 2 ^ 64 * 3 ^ 16 * 5 ^ 16 * 7 ^ 16 := by
  rw [natAbs_discr_eq C2 QNegSeven]
  · rw [C2_degree, qNegSeven_degree, C2_natAbs_discr, qNegSeven_natAbs_discr]
    ring
  · rw [C2_natAbs_discr, qNegSeven_natAbs_discr]
    norm_num

theorem C4_degree : Module.finrank ℚ C4 = 64 := by
  rw [finrank_eq_mul C3 QNegEleven]
  · rw [C3_degree, qNegEleven_degree]
  · rw [C3_natAbs_discr, qNegEleven_natAbs_discr]
    norm_num

theorem C4_natAbs_discr :
    (discr C4).natAbs = 2 ^ 128 * 3 ^ 32 * 5 ^ 32 * 7 ^ 32 * 11 ^ 32 := by
  rw [natAbs_discr_eq C3 QNegEleven]
  · rw [C3_degree, qNegEleven_degree, C3_natAbs_discr,
      qNegEleven_natAbs_discr]
    ring
  · rw [C3_natAbs_discr, qNegEleven_natAbs_discr]
    norm_num

theorem C5_degree : Module.finrank ℚ C5 = 128 := by
  rw [finrank_eq_mul C4 QThirteen]
  · rw [C4_degree, qThirteen_degree]
  · rw [C4_natAbs_discr, qThirteen_natAbs_discr]
    norm_num

theorem C5_natAbs_discr :
    (discr C5).natAbs = 2 ^ 256 * 15015 ^ 64 := by
  rw [natAbs_discr_eq C4 QThirteen]
  · rw [C4_degree, qThirteen_degree, C4_natAbs_discr,
      qThirteen_natAbs_discr]
    ring
  · rw [C4_natAbs_discr, qThirteen_natAbs_discr]
    norm_num

/-! ## Identification with the chosen seven-radical field -/

/-- A fixed primitive eighth root in the dyadic component. -/
def zetaEight : Dyadic := IsCyclotomicExtension.zeta 8 ℚ Dyadic

theorem zetaEight_primitive : IsPrimitiveRoot zetaEight 8 :=
  IsCyclotomicExtension.zeta_spec 8 ℚ Dyadic

theorem zetaEight_pow_four : zetaEight ^ 4 = -1 := by
  have htwo : IsPrimitiveRoot (zetaEight ^ 4) 2 :=
    zetaEight_primitive.pow (by norm_num) (by norm_num)
  exact htwo.eq_neg_one_of_two_right

/-- The two radicals carried by the eighth cyclotomic component. -/
def dyadicI : Dyadic := zetaEight ^ 2
def dyadicSqrtTwo : Dyadic := zetaEight - zetaEight ^ 3

theorem dyadicI_sq : dyadicI ^ 2 = -1 := by
  rw [dyadicI, ← pow_mul, show 2 * 2 = 4 by norm_num, zetaEight_pow_four]

theorem dyadicSqrtTwo_sq : dyadicSqrtTwo ^ 2 = 2 := by
  have h6 : zetaEight ^ 6 = -(zetaEight ^ 2) := by
    calc
      zetaEight ^ 6 = zetaEight ^ 2 * zetaEight ^ 4 := by ring
      _ = -(zetaEight ^ 2) := by rw [zetaEight_pow_four]; ring
  rw [dyadicSqrtTwo]
  calc
    (zetaEight - zetaEight ^ 3) ^ 2 =
        zetaEight ^ 2 - 2 * zetaEight ^ 4 + zetaEight ^ 6 := by ring
    _ = 2 := by rw [zetaEight_pow_four, h6]; ring

/-- The six component embeddings into the final compositum. -/
def dyadicToC5 : Dyadic →ₐ[ℚ] C5 :=
  (leftEmbedding C4 QThirteen).comp
    ((leftEmbedding C3 QNegEleven).comp
      ((leftEmbedding C2 QNegSeven).comp
        ((leftEmbedding C1 QFive).comp (leftEmbedding Dyadic QNegThree))))

def qNegThreeToC5 : QNegThree →ₐ[ℚ] C5 :=
  (leftEmbedding C4 QThirteen).comp
    ((leftEmbedding C3 QNegEleven).comp
      ((leftEmbedding C2 QNegSeven).comp
        ((leftEmbedding C1 QFive).comp (rightEmbedding Dyadic QNegThree))))

def qFiveToC5 : QFive →ₐ[ℚ] C5 :=
  (leftEmbedding C4 QThirteen).comp
    ((leftEmbedding C3 QNegEleven).comp
      ((leftEmbedding C2 QNegSeven).comp (rightEmbedding C1 QFive)))

def qNegSevenToC5 : QNegSeven →ₐ[ℚ] C5 :=
  (leftEmbedding C4 QThirteen).comp
    ((leftEmbedding C3 QNegEleven).comp (rightEmbedding C2 QNegSeven))

def qNegElevenToC5 : QNegEleven →ₐ[ℚ] C5 :=
  (leftEmbedding C4 QThirteen).comp (rightEmbedding C3 QNegEleven)

def qThirteenToC5 : QThirteen →ₐ[ℚ] C5 :=
  rightEmbedding C4 QThirteen

def rootMinusOne : C5 := dyadicToC5 dyadicI
def rootTwo : C5 := dyadicToC5 dyadicSqrtTwo
def rootThree : C5 :=
  dyadicToC5 dyadicI *
    qNegThreeToC5 (quadraticClosureGenerator (-3 : ℚ) nonsquare_negThree)
def rootFive : C5 :=
  qFiveToC5 (quadraticClosureGenerator (5 : ℚ) nonsquare_five)
def rootSeven : C5 :=
  dyadicToC5 dyadicI *
    qNegSevenToC5 (quadraticClosureGenerator (-7 : ℚ) nonsquare_negSeven)
def rootEleven : C5 :=
  dyadicToC5 dyadicI *
    qNegElevenToC5 (quadraticClosureGenerator (-11 : ℚ) nonsquare_negEleven)
def rootThirteen : C5 :=
  qThirteenToC5 (quadraticClosureGenerator (13 : ℚ) nonsquare_thirteen)

theorem rootMinusOne_sq : rootMinusOne ^ 2 = (-1 : C5) := by
  rw [rootMinusOne, ← map_pow, dyadicI_sq, map_neg, map_one]

theorem rootTwo_sq : rootTwo ^ 2 = (2 : C5) := by
  rw [rootTwo, ← map_pow, dyadicSqrtTwo_sq, map_ofNat]

theorem rootThree_sq : rootThree ^ 2 = (3 : C5) := by
  rw [rootThree, mul_pow, ← map_pow, ← map_pow, dyadicI_sq,
    quadraticClosureGenerator_sq]
  simpa using (qNegThreeToC5.commutes (3 : ℚ))

theorem rootFive_sq : rootFive ^ 2 = (5 : C5) := by
  rw [rootFive, ← map_pow, quadraticClosureGenerator_sq]
  simpa using (qFiveToC5.commutes (5 : ℚ))

theorem rootSeven_sq : rootSeven ^ 2 = (7 : C5) := by
  rw [rootSeven, mul_pow, ← map_pow, ← map_pow, dyadicI_sq,
    quadraticClosureGenerator_sq]
  simpa using (qNegSevenToC5.commutes (7 : ℚ))

theorem rootEleven_sq : rootEleven ^ 2 = (11 : C5) := by
  rw [rootEleven, mul_pow, ← map_pow, ← map_pow, dyadicI_sq,
    quadraticClosureGenerator_sq]
  simpa using (qNegElevenToC5.commutes (11 : ℚ))

theorem rootThirteen_sq : rootThirteen ^ 2 = (13 : C5) := by
  rw [rootThirteen, ← map_pow, quadraticClosureGenerator_sq]
  simpa using (qThirteenToC5.commutes (13 : ℚ))

theorem C5_has_genus_roots (i : Fin 7) :
    ∃ y : C5, y ^ 2 =
      algebraMap ℚ C5 (ArithmeticChosenGenus.radicands i) := by
  fin_cases i
  · exact ⟨rootMinusOne, by simpa [ArithmeticChosenGenus.radicands] using rootMinusOne_sq⟩
  · exact ⟨rootTwo, by simpa [ArithmeticChosenGenus.radicands] using rootTwo_sq⟩
  · exact ⟨rootThree, by simpa [ArithmeticChosenGenus.radicands] using rootThree_sq⟩
  · exact ⟨rootFive, by simpa [ArithmeticChosenGenus.radicands] using rootFive_sq⟩
  · exact ⟨rootSeven, by simpa [ArithmeticChosenGenus.radicands] using rootSeven_sq⟩
  · exact ⟨rootEleven, by simpa [ArithmeticChosenGenus.radicands] using rootEleven_sq⟩
  · exact ⟨rootThirteen, by simpa [ArithmeticChosenGenus.radicands] using rootThirteen_sq⟩

/-- The generated genus field embeds into the coprime-discriminant model. -/
private theorem nonempty_chosenGenusToC5 :
    Nonempty (ArithmeticChosenGenus.GenusField →ₐ[ℚ] C5) := by
  rw [← ArithmeticChosenGenus.genusTower_algebra_eq]
  exact ArithmeticChosenGenus.genusTower.nonempty_embedding C5
    (fun i _ ↦ C5_has_genus_roots i)

def chosenGenusToC5 : ArithmeticChosenGenus.GenusField →ₐ[ℚ] C5 :=
  Classical.choice nonempty_chosenGenusToC5

theorem chosenGenusToC5_surjective : Function.Surjective chosenGenusToC5 := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := chosenGenusToC5.toLinearMap) (by
      rw [ArithmeticChosenGenus.genusField_degree, C5_degree])).mp
    chosenGenusToC5.injective

/-- The independently chosen genus field is the concrete compositum above. -/
def chosenGenusEquivC5 : ArithmeticChosenGenus.GenusField ≃ₐ[ℚ] C5 :=
  AlgEquiv.ofBijective chosenGenusToC5
    ⟨chosenGenusToC5.injective, chosenGenusToC5_surjective⟩

/-- Exact absolute discriminant of the genus field used in the retained-field
construction.  This discharges the former genus-discriminant premise. -/
theorem chosenGenus_natAbs_discr :
    (discr ArithmeticChosenGenus.GenusField).natAbs =
      2 ^ 256 * 15015 ^ 64 := by
  rw [discr_eq_discr_of_algEquiv ArithmeticChosenGenus.GenusField chosenGenusEquivC5]
  exact C5_natAbs_discr

end UnitDistance.GenusDiscriminant
