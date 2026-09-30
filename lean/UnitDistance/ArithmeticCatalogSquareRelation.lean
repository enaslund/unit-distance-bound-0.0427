module

public import UnitDistance.ArithmeticCatalogRadicands
public import UnitDistance.CatalogWordSquareclasses

@[expose] public section
set_option backward.privateInPublic true


/-!
# The explicit square relation among catalog words

The relation word 26 is a genuine square in the actual genus field.
This gives the missing field identity behind the containment of the seven
completed radicands in the full twelve-radical construction.
-/

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticCatalog
open ArithmeticChosenGenus Multiquadratic NormExtensionCatalog CatalogWordSquareclasses

theorem wordRadicand_eq_wordValue (m : ℕ) :
    wordRadicand m = wordValue catalogAlpha m := by
  simp only [wordRadicand,radicand,Finset.prod_filter,wordValue,catalogAlpha]

/-- The actual repeated square root in rows 1, 3, and 4 has square -55. -/
theorem maskRoot_41_sq : (maskRoot 41)^2 = (-55 : GenusField) := by
  simpa [rootsA,masksA,CatalogSquareclassData.masksA,catalog] using rootsA_sq 1

/-- The actual product of the three catalog radicands is exactly -728. -/
theorem wordRadicand_26_value : wordRadicand 26 = (-728 : GenusField) := by
  rw [wordRadicand_eq_wordValue,wordValue_26]
  simpa [catalogAlpha,alpha,rootsA,masksA,CatalogSquareclassData.masksA,catalog] using
    triple_norm_identity (maskRoot 41) maskRoot_41_sq

/-- The relation word has an explicit square root in the actual genus field. -/
theorem wordRadicand_26_square : wordRadicand 26 = (2*maskRoot 83)^2 := by
  have hv : maskValue 83 = (-182 : ℚ) := by decide +kernel
  rw [wordRadicand_26_value,mul_pow,maskRoot_sq,hv]
  norm_num

theorem wordRadicand_26_isSquare : IsSquare (wordRadicand 26) :=
  ⟨2*maskRoot 83,by simpa [pow_two] using wordRadicand_26_square⟩

end UnitDistance.ArithmeticCatalog
