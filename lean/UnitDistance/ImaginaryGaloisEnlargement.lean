module

public import UnitDistance.ImaginaryQuadraticBase
public import UnitDistance.FiniteFieldImage
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.GaloisPCompositum

@[expose] public section
set_option backward.privateInPublic true


/-! Actual enlargement of a finite rational Galois 2-extension by i. -/
noncomputable section
open NumberField
namespace UnitDistance.ArithmeticProP

variable (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]

def imaginaryGaloisEnlargement : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
  finiteGaloisImage L ⊔ finiteGaloisImage ImaginaryQuadratic.Carrier

instance imaginaryGaloisEnlargement_numberField : NumberField (imaginaryGaloisEnlargement L) :=
  NumberField.of_module_finite ℚ _

/-- The original number field embeds into its literal compositum with Q(i). -/
def imaginaryGaloisEnlargementEmbedding : L →ₐ[ℚ] imaginaryGaloisEnlargement L :=
  (IntermediateField.inclusion (show (finiteGaloisImage L).toIntermediateField ≤
      (imaginaryGaloisEnlargement L).toIntermediateField from le_sup_left)).comp
    (finiteGaloisImageEquiv L).toAlgHom

/-- The imaginary quadratic field embeds into the same compositum. -/
def imaginaryGaloisEnlargementImaginaryEmbedding :
    ImaginaryQuadratic.Carrier →ₐ[ℚ] imaginaryGaloisEnlargement L :=
  (IntermediateField.inclusion
      (show (finiteGaloisImage ImaginaryQuadratic.Carrier).toIntermediateField ≤
        (imaginaryGaloisEnlargement L).toIntermediateField from le_sup_right)).comp
    (finiteGaloisImageEquiv ImaginaryQuadratic.Carrier).toAlgHom

theorem imaginaryGaloisEnlargement_has_root :
    ∃ i : imaginaryGaloisEnlargement L, i^2 = -1 := by
  refine ⟨imaginaryGaloisEnlargementImaginaryEmbedding L ImaginaryQuadratic.root,?_⟩
  rw [← map_pow,ImaginaryQuadratic.root_sq,map_neg,map_one]

/-- The actual compositum remains a Galois 2-extension. -/
theorem imaginaryGaloisEnlargement_isPGroup (hP : IsPGroup 2 Gal(L/ℚ)) :
    IsPGroup 2 Gal((imaginaryGaloisEnlargement L)/ℚ) := by
  apply ClassFieldTower.Sawin.isPGroup_galois_sup
  · exact finiteGaloisImage_isPGroup L hP
  · apply finiteGaloisImage_isPGroup ImaginaryQuadratic.Carrier
    apply IsPGroup.of_card (n := 1)
    rw [IsGalois.card_aut_eq_finrank,ImaginaryQuadratic.finrank]
    norm_num

end UnitDistance.ArithmeticProP
