module

public import UnitDistance.GaloisQuotientTower
public import UnitDistance.GaloisFiniteQuotientField
public import UnitDistance.GaloisEmbeddingConjugation
public import UnitDistance.ArithmeticRetainedRoots

@[expose] public section
set_option backward.privateInPublic true


/-! Actual growing number fields containing the retained field and the
independent finite conjugacy detector, extracted from an infinite quotient. -/
noncomputable section
namespace UnitDistance.GaloisQuotient
open NumberField ArithmeticRetained GaloisConjugation
attribute [local instance] IntermediateField.algebra'
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [T2Space Q] [CompactSpace Q] [TotallyDisconnectedSpace Q] [Infinite Q]
variable (ρ : Gal(Ω/ℚ) →ₜ* Q) (hρ : Function.Surjective ρ)
variable (e : RetainedField →ₐ[ℚ] Ω)
variable {C : Type} [Group C] [Fintype C] [TopologicalSpace C] [DiscreteTopology C]
variable (χ : Gal(Ω/ℚ) →ₜ* C)
variable (hM : ρ.toMonoidHom.ker ≤ e.fieldRange.fixingSubgroup)
variable (hχ : ρ.toMonoidHom.ker ≤ χ.toMonoidHom.ker)

local instance retainedRange_algebra : Algebra ℚ e.fieldRange := e.fieldRange.algebra'

private instance retainedRange_finite : Module.Finite ℚ e.fieldRange :=
  e.equivFieldRange.toLinearEquiv.finiteDimensional
private instance retainedRange_galois : IsGalois ℚ e.fieldRange :=
  IsGalois.of_algEquiv e.equivFieldRange

/-- The actual retained field and the actual finite detector are adjoined
to each level of the growing Galois family. -/
def retainedFamily : Family ℚ Ω Q ρ.toMonoidHom := by
  let T := Classical.choice (exists_family ℚ Ω Q ρ.toMonoidHom hρ ρ.continuous_toFun)
  let R := e.fieldRange ⊔ finiteQuotientField χ
  have hR : ρ.toMonoidHom.ker ≤ R.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup,finiteQuotientField_fixing]
    exact le_inf hM hχ
  exact T.adjoinRetained ℚ Ω Q R hR

abbrev retainedLevel (j : ℕ) := (retainedFamily ρ hρ e χ hM hχ).level j

instance retainedLevel_algebra (j : ℕ) : Algebra ℚ (retainedLevel ρ hρ e χ hM hχ j) :=
  (retainedLevel ρ hρ e χ hM hχ j).algebra'

instance retainedLevel_finite (j : ℕ) : Module.Finite ℚ (retainedLevel ρ hρ e χ hM hχ j) :=
  (retainedFamily ρ hρ e χ hM hχ).finite j
instance retainedLevel_galois (j : ℕ) : IsGalois ℚ (retainedLevel ρ hρ e χ hM hχ j) :=
  (retainedFamily ρ hρ e χ hM hχ).galois j

instance retainedLevel_numberField (j : ℕ) : NumberField (retainedLevel ρ hρ e χ hM hχ j) :=
  NumberField.of_module_finite ℚ _

/-- Every actual layer contains the actual embedded retained field. -/
theorem retainedRange_le_level (j : ℕ) :
    e.fieldRange ≤ retainedLevel ρ hρ e χ hM hχ j := le_trans le_sup_left le_sup_right

/-- Every actual layer contains the actual fixed field of the finite quotient. -/
theorem detectorField_le_level (j : ℕ) :
    finiteQuotientField χ ≤ retainedLevel ρ hρ e χ hM hχ j := le_trans le_sup_right le_sup_right

def retainedEmbedding (j : ℕ) : RetainedField →ₐ[ℚ] retainedLevel ρ hρ e χ hM hχ j :=
  (IntermediateField.inclusion (retainedRange_le_level ρ hρ e χ hM hχ j)).comp
    e.equivFieldRange.toAlgHom

instance retainedLevel_algebraRetained (j : ℕ) :
    Algebra RetainedField (retainedLevel ρ hρ e χ hM hχ j) :=
  (retainedEmbedding ρ hρ e χ hM hχ j).toRingHom.toAlgebra

/-- These are actual degree-diverging number fields. -/
theorem retainedLevel_degree_tendsto : Filter.Tendsto
    (fun j => Module.finrank ℚ (retainedLevel ρ hρ e χ hM hχ j)) Filter.atTop Filter.atTop :=
  (retainedFamily ρ hρ e χ hM hχ).degree_tendsto

/-- The fixed ambient conjugation restricts to each actual finite layer. -/
def retainedLevelConjugation (c : Gal(Ω/ℚ)) (j : ℕ) :
    Gal(retainedLevel ρ hρ e χ hM hχ j/ℚ) :=
  GaloisEmbedding.restriction (retainedLevel ρ hρ e χ hM hχ j).val c

/-- Containing the detector yields the genuine conjugacy-index bound in
every finite Galois layer; it is not a supplied signature condition. -/
theorem retainedLevel_conjugacy_index (hχsurj : Function.Surjective χ)
    (c : Gal(Ω/ℚ)) (hindex : 4096 ≤ (Subgroup.centralizer ({χ c} : Set C)).index) (j : ℕ) :
    4096 ≤ (Subgroup.centralizer
      ({retainedLevelConjugation ρ hρ e χ hM hχ c j} :
        Set Gal(retainedLevel ρ hρ e χ hM hχ j/ℚ))).index := by
  let L := retainedLevel ρ hρ e χ hM hχ j
  let hL := detectorField_le_level ρ hρ e χ hM hχ j
  let π := finiteQuotientOnLayer χ L hL
  have hp := centralizer_index_le_of_surjective π
    (finiteQuotientOnLayer_surjective χ L hχsurj hL)
    (retainedLevelConjugation ρ hρ e χ hM hχ c j)
  have he : π (retainedLevelConjugation ρ hρ e χ hM hχ c j)=χ c :=
    finiteQuotientOnLayer_restriction χ L hL c
  rw [he] at hp
  exact hindex.trans hp

/-- Restriction of the ambient complex embedding to the literal finite layer. -/
def retainedLevelEmbedding (Φ : Ω →+* ℂ) (j : ℕ) :
    retainedLevel ρ hρ e χ hM hχ j →+* ℂ :=
  Φ.comp (retainedLevel ρ hρ e χ hM hχ j).val.toRingHom

theorem retainedLevel_isConj (Φ : Ω →+* ℂ) (c : Gal(Ω/ℚ))
    (hc : NumberField.ComplexEmbedding.IsConj Φ c) (j : ℕ) :
    NumberField.ComplexEmbedding.IsConj (retainedLevelEmbedding ρ hρ e χ hM hχ Φ j)
      (retainedLevelConjugation ρ hρ e χ hM hχ c j) :=
  GaloisEmbedding.restriction_isConj (retainedLevel ρ hρ e χ hM hχ j).val Φ c hc

theorem retainedLevel_conjugation_ne_one (Φ : Ω →+* ℂ) (c : Gal(Ω/ℚ))
    (hc : NumberField.ComplexEmbedding.IsConj Φ c) (j : ℕ) :
    retainedLevelConjugation ρ hρ e χ hM hχ c j ≠ 1 := by
  apply (NumberField.ComplexEmbedding.isConj_ne_one_iff
    (retainedLevel_isConj ρ hρ e χ hM hχ Φ c hc j)).mpr
  intro hr
  have hs := congrArg hr.embedding (imaginaryUnitIn_sq (retainedLevel ρ hρ e χ hM hχ j))
  simp only [map_pow,map_neg,map_one] at hs
  nlinarith [sq_nonneg (hr.embedding (imaginaryUnitIn (retainedLevel ρ hρ e χ hM hχ j)))]

end UnitDistance.GaloisQuotient
