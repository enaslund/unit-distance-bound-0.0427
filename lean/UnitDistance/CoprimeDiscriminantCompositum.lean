module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

@[expose] public section
set_option backward.privateInPublic true


/-!
# Discriminants of concrete coprime composita

This file packages Mathlib's different-ideal compositum theorem for the
concrete compositum of two finite abelian number fields.  Coprimality of the
two absolute discriminants supplies both linear disjointness and coprimality
of the mapped differents, so the resulting degree and discriminant formulas
have no local assumptions.
-/

noncomputable section

namespace UnitDistance.CoprimeDiscriminantCompositum

open NumberField
open AlgebraicNumberTheory

variable (K L : Type) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [IsAbelianGalois ℚ K] [IsAbelianGalois ℚ L]

/-- The fixed separable-closure model of the compositum. -/
abbrev Carrier := finiteAbelianCompositumField ℚ K L

/-- The canonical embedding of the left factor. -/
abbrev leftEmbedding : K →ₐ[ℚ] Carrier K L :=
  finiteAbelianCompositumEmbeddingLeft ℚ K L

/-- The canonical embedding of the right factor. -/
abbrev rightEmbedding : L →ₐ[ℚ] Carrier K L :=
  finiteAbelianCompositumEmbeddingRight ℚ K L

noncomputable instance carrierNumberField : NumberField (Carrier K L) :=
  NumberField.of_module_finite ℚ (Carrier K L)

noncomputable instance leftRangeFinite :
    Module.Finite ℚ (leftEmbedding K L).fieldRange :=
  (leftEmbedding K L).equivFieldRange.toLinearEquiv.finiteDimensional

noncomputable instance rightRangeFinite :
    Module.Finite ℚ (rightEmbedding K L).fieldRange :=
  (rightEmbedding K L).equivFieldRange.toLinearEquiv.finiteDimensional

noncomputable instance leftRangeNumberField :
    NumberField (leftEmbedding K L).fieldRange :=
  NumberField.of_module_finite ℚ (leftEmbedding K L).fieldRange

noncomputable instance rightRangeNumberField :
    NumberField (rightEmbedding K L).fieldRange :=
  NumberField.of_module_finite ℚ (rightEmbedding K L).fieldRange

noncomputable instance leftRangeGalois :
    IsGalois ℚ (leftEmbedding K L).fieldRange :=
  IsGalois.of_algEquiv (leftEmbedding K L).equivFieldRange

noncomputable instance rightRangeGalois :
    IsGalois ℚ (rightEmbedding K L).fieldRange :=
  IsGalois.of_algEquiv (rightEmbedding K L).equivFieldRange

private theorem image_discriminants
    (hcop : Nat.Coprime (discr K).natAbs (discr L).natAbs) :
    IsCoprime
      (discr (leftEmbedding K L).fieldRange)
      (discr (rightEmbedding K L).fieldRange) := by
  rw [← discr_eq_discr_of_algEquiv K (leftEmbedding K L).equivFieldRange,
    ← discr_eq_discr_of_algEquiv L (rightEmbedding K L).equivFieldRange,
    Int.isCoprime_iff_nat_coprime]
  exact hcop

/-- Coprime absolute discriminants force the two canonical images to be
linearly disjoint in their concrete compositum. -/
theorem image_linearDisjoint
    (hcop : Nat.Coprime (discr K).natAbs (discr L).natAbs) :
    (leftEmbedding K L).fieldRange.LinearDisjoint
      (rightEmbedding K L).fieldRange := by
  apply linearDisjoint_of_isGalois_isCoprime_discr (Carrier K L)
  exact image_discriminants K L hcop

/-- The degree of a coprime compositum is the product of the two degrees. -/
theorem finrank_eq_mul
    (hcop : Nat.Coprime (discr K).natAbs (discr L).natAbs) :
    Module.finrank ℚ (Carrier K L) =
      Module.finrank ℚ K * Module.finrank ℚ L := by
  let A := (leftEmbedding K L).fieldRange
  let B := (rightEmbedding K L).fieldRange
  have htop : A ⊔ B = ⊤ :=
    finiteAbelianCompositum_embeddingRanges_sup_eq_top ℚ K L
  have hsup := (image_linearDisjoint K L hcop).finrank_sup
  rw [htop] at hsup
  calc
    Module.finrank ℚ (Carrier K L) =
        Module.finrank ℚ (⊤ : IntermediateField ℚ (Carrier K L)) :=
      (IntermediateField.topEquiv.toLinearEquiv.finrank_eq).symm
    _ = Module.finrank ℚ (leftEmbedding K L).fieldRange *
        Module.finrank ℚ (rightEmbedding K L).fieldRange := hsup
    _ = Module.finrank ℚ K * Module.finrank ℚ L := by
      rw [← (leftEmbedding K L).equivFieldRange.toLinearEquiv.finrank_eq,
        ← (rightEmbedding K L).equivFieldRange.toLinearEquiv.finrank_eq]

/-- Exact discriminant formula for a compositum whose two absolute
discriminants are coprime. -/
theorem natAbs_discr_eq
    (hcop : Nat.Coprime (discr K).natAbs (discr L).natAbs) :
    (discr (Carrier K L)).natAbs =
      (discr K).natAbs ^ Module.finrank ℚ L *
        (discr L).natAbs ^ Module.finrank ℚ K := by
  let A := (leftEmbedding K L).fieldRange
  let B := (rightEmbedding K L).fieldRange
  have hAB : IsCoprime (discr A) (discr B) := image_discriminants K L hcop
  have hdisj : A.LinearDisjoint B := image_linearDisjoint K L hcop
  have htop : A ⊔ B = ⊤ :=
    finiteAbelianCompositum_embeddingRanges_sup_eq_top ℚ K L
  rw [natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow
    (Carrier K L) A B hdisj htop
      (isCoprime_differentIdeal_of_isCoprime_discr (Carrier K L) hAB)]
  dsimp only [A, B]
  rw [← discr_eq_discr_of_algEquiv K (leftEmbedding K L).equivFieldRange,
    ← discr_eq_discr_of_algEquiv L (rightEmbedding K L).equivFieldRange]
  simp only [
    (leftEmbedding K L).equivFieldRange.toLinearEquiv.finrank_eq,
    (rightEmbedding K L).equivFieldRange.toLinearEquiv.finrank_eq]

end UnitDistance.CoprimeDiscriminantCompositum
