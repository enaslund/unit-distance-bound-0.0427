module

public import UnitDistance.Sqrt241.Retained.Kernel
public import UnitDistance.GaloisQuotientTower
public import UnitDistance.GaloisEmbeddingConjugation

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The growing levels `K_j`

Generalization of the ℚ package's `GaloisRetainedFamily`/`SigmaCutFamily`: the
profinite quotient `Ĝ ⧸ kernelHat` is infinite (`Input.infinite_quotient`), so
`GaloisQuotient.exists_family` gives finite Galois fields `L_j ≤ Ω` of unbounded
degree whose fixing groups contain `kernelHat`; the levels are
`K_j := L_j ⊔ detectorField` (`GaloisQuotient.Family.adjoinRetained`).

For every level: `K_j` is finite Galois over `ℚ`, `M ≤ K_j`,
`kernelHat ≤ Gal(Ω/K_j) ≤ detKer ≤ core`, the degree tends to infinity, the
restriction `c_j` of `c₁` is the complex conjugation of `phi|K_j`
(`levelConj_isConj`), and its centralizer index is at least `65536`
(`levelConj_index`), so `c_j ≠ 1`.

**Admissible fields.** `Input.Admissible K` (finite Galois `K ≤ Ω` with `M ≤ K` and
`kernelHat ≤ Gal(Ω/K)`) is the class of fields whose local indices are computed in
`Levels/LocalData.lean`; `M` and every level are admissible.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation Cut GroupData ProCGroups GaloisQuotient

namespace Input

variable (I : Input)

/-! ### The profinite quotient `Ĝ ⧸ kernelHat` -/

/-- The profinite quotient of `Ĝ` by the cut kernel. -/
abbrev HatQuotient : Type := Ghat ⧸ I.kernelHat

instance kernelHat_isClosed : IsClosed (I.kernelHat : Set Ghat) := I.isClosed_kernelHat

instance hatQuotient_totallyDisconnected : TotallyDisconnectedSpace I.HatQuotient :=
  ProCGroups.totallyDisconnectedSpace_quotient_closedNormal I.kernelHat I.isClosed_kernelHat

instance hatQuotient_infinite : Infinite I.HatQuotient := I.infinite_quotient

/-- `Ĝ → Ĝ ⧸ kernelHat`. -/
def hatProjection : Ghat →* I.HatQuotient := QuotientGroup.mk' I.kernelHat

theorem hatProjection_surjective : Function.Surjective I.hatProjection :=
  QuotientGroup.mk'_surjective _

theorem hatProjection_continuous : Continuous I.hatProjection := QuotientGroup.continuous_mk

theorem hatProjection_ker : I.hatProjection.ker = I.kernelHat := QuotientGroup.ker_mk' _

/-! ### The family -/

theorem kernel_le_detectorField_fixing :
    I.hatProjection.ker ≤ I.detectorField.fixingSubgroup := by
  rw [hatProjection_ker, detectorField_fixingSubgroup]
  exact I.kernelHat_le_detKer

/-- **The growing family** `K_j = L_j ⊔ detectorField`. -/
def family : Family ℚ Omega I.HatQuotient I.hatProjection :=
  (Classical.choice (exists_family ℚ Omega I.HatQuotient I.hatProjection
    I.hatProjection_surjective I.hatProjection_continuous)).adjoinRetained ℚ Omega
    I.HatQuotient I.detectorField I.kernel_le_detectorField_fixing

/-- **The levels** `K_j ≤ Ω`. -/
def level (j : ℕ) : IntermediateField ℚ Omega := I.family.level j

instance level_finiteDimensional (j : ℕ) : FiniteDimensional ℚ (I.level j) := I.family.finite j

instance level_isGalois (j : ℕ) : IsGalois ℚ (I.level j) := I.family.galois j

instance level_numberField (j : ℕ) : NumberField (I.level j) :=
  NumberField.of_module_finite ℚ _

theorem level_degree_tendsto :
    Filter.Tendsto (fun j => Module.finrank ℚ (I.level j)) Filter.atTop Filter.atTop :=
  I.family.degree_tendsto

theorem detectorField_le_level (j : ℕ) : I.detectorField ≤ I.level j :=
  Family.retained_le ℚ Omega I.HatQuotient _ I.detectorField I.kernel_le_detectorField_fixing j

theorem M_le_level (j : ℕ) : I.M ≤ I.level j :=
  I.M_le_detectorField.trans (I.detectorField_le_level j)

theorem kernelHat_le_level_fixing (j : ℕ) : I.kernelHat ≤ (I.level j).fixingSubgroup := by
  rw [← I.hatProjection_ker]
  exact I.family.kernel_fixes j

theorem level_fixing_le_detKer (j : ℕ) : (I.level j).fixingSubgroup ≤ I.detKer := by
  rw [← I.detectorField_fixingSubgroup]
  exact IntermediateField.fixingSubgroup_le (I.detectorField_le_level j)

theorem level_increasing (j : ℕ) : I.level j ≤ I.level (j + 1) := I.family.increasing j

/-! ### Complex conjugation on the levels -/

/-- The complex embedding `phi|K_j`. -/
def levelPhi (j : ℕ) : I.level j →+* ℂ := I.phi.comp (I.level j).val.toRingHom

/-- The restriction `c_j` of `c₁` to `K_j`. -/
def levelConj (j : ℕ) : Gal(I.level j/ℚ) := res (I.level j) ((I.E.conj 0 : GB) : Ghat)

theorem levelConj_isConj (j : ℕ) :
    NumberField.ComplexEmbedding.IsConj (I.levelPhi j) (I.levelConj j) :=
  GaloisEmbedding.restriction_isConj (I.level j).val I.phi _ I.conj_isConj

/-- **Centralizer index** at least `2^16` in every level. -/
theorem levelConj_index (j : ℕ) :
    65536 ≤ (Subgroup.centralizer ({I.levelConj j} : Set Gal(I.level j/ℚ))).index :=
  I.centralizer_index (I.level j) (I.level_fixing_le_detKer j)

theorem levelConj_ne_one (j : ℕ) : I.levelConj j ≠ 1 := by
  intro h
  have hi := I.levelConj_index j
  rw [h] at hi
  have htop : Subgroup.centralizer ({(1 : Gal(I.level j/ℚ))} : Set Gal(I.level j/ℚ)) = ⊤ := by
    ext g
    simp
  rw [htop, Subgroup.index_top] at hi
  omega

/-! ### Admissible fields -/

/-- Finite Galois subfields of `Ω` containing `M` and fixed by `kernelHat`. -/
structure Admissible (K : IntermediateField ℚ Omega) : Prop where
  finiteDimensional : FiniteDimensional ℚ K
  isGalois : IsGalois ℚ K
  M_le : I.M ≤ K
  kernelHat_le : I.kernelHat ≤ K.fixingSubgroup

theorem admissible_M : I.Admissible I.M :=
  ⟨inferInstance, inferInstance, le_rfl, by rw [M_fixingSubgroup]; exact I.kernelHat_le_core⟩

theorem admissible_level (j : ℕ) : I.Admissible (I.level j) :=
  ⟨inferInstance, inferInstance, I.M_le_level j, I.kernelHat_le_level_fixing j⟩

theorem Admissible.fixing_le_core {I : Input} {K : IntermediateField ℚ Omega}
    (hK : I.Admissible K) : K.fixingSubgroup ≤ I.core := by
  rw [← I.M_fixingSubgroup]
  exact IntermediateField.fixingSubgroup_le hK.M_le

end Input

end UnitDistance.Sqrt241.Retained
