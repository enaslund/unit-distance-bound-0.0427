module

public import UnitDistance.Sqrt241.Retained.Basic
public import UnitDistance.Sqrt241.Genus.ExactTypes

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The retained field `M = Ω^core`

`M := fixedField core ≤ Ω`. Since `core` is open and normal in `Ĝ`, `M` is a
finite Galois extension of `ℚ` (`InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois`)
with `Gal(M/ℚ) ≃ Ĝ/core`. Elements of `core` fix `√241` (they lie in `G_B`) and
have trivial genus label (`(ρ_B g).base = genusLabel g`), so the genus field
`E_Ω` lies in `M`; this gives `genusToM : CanonicalGenus.Carrier →ₐ[ℚ] M` and
`√−1, √3 ∈ M` (`√3 = √−1 √α₄ √α₅`, `α₄α₅ = −3`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation Cut GroupData CanonicalGenus

namespace Input

variable (I : Input)

/-- `core` as a closed subgroup. -/
def coreClosed : ClosedSubgroup Ghat := ⟨I.core, I.isClosed_core⟩

instance coreClosed_normal : I.coreClosed.Normal := I.core_normal

/-- **The retained field** `M := Ω^core`. -/
def M : IntermediateField ℚ Omega := IntermediateField.fixedField I.core

theorem M_fixingSubgroup : I.M.fixingSubgroup = I.core :=
  InfiniteGalois.fixingSubgroup_fixedField I.coreClosed

theorem M_finite_galois : FiniteDimensional ℚ I.M ∧ IsGalois ℚ I.M := by
  apply (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois I.M).mp
  rw [M_fixingSubgroup]
  exact ⟨I.isOpen_core, I.core_normal⟩

instance M_finiteDimensional : FiniteDimensional ℚ I.M := I.M_finite_galois.1

instance M_isGalois : IsGalois ℚ I.M := I.M_finite_galois.2

instance M_numberField : NumberField I.M := NumberField.of_module_finite ℚ _

theorem mem_M_iff (x : Omega) : x ∈ I.M ↔ ∀ σ ∈ I.core, σ x = x := by
  constructor
  · intro hx σ hσ
    exact hx ⟨σ, hσ⟩
  · intro h σ
    exact h σ.1 σ.2

/-- Elements of `retainedKer` fix the genus field. -/
theorem retainedKer_le_EOmega_fixing : I.retainedKer ≤ EOmega.fixingSubgroup := by
  intro σ hσ
  obtain ⟨hB, h1⟩ := (I.mem_retainedKer_iff σ).mp hσ
  have hl : genusLabel ⟨σ, hB⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    rw [← I.retainedMap_base, h1]
    rfl
  exact (mem_ker_genusLabelHom_iff ⟨σ, hB⟩).mp hl

theorem core_le_EOmega_fixing : I.core ≤ EOmega.fixingSubgroup :=
  I.core_le_retainedKer.trans I.retainedKer_le_EOmega_fixing

/-- **The genus field lies in `M`.** -/
theorem EOmega_le_M : EOmega ≤ I.M :=
  (IntermediateField.le_iff_le I.core EOmega).mpr I.core_le_EOmega_fixing

theorem mem_EOmega_of_mem_field {x : Closure} (hx : x ∈ CanonicalGenus.field) :
    (⟨x, canonicalGenus_le_Omega hx⟩ : Omega) ∈ EOmega := by
  rw [← lift_EOmega] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = ⟨x, canonicalGenus_le_Omega (lift_EOmega ▸ ⟨y, hy, hyx⟩)⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

theorem mem_M_of_mem_field {x : Closure} (hx : x ∈ CanonicalGenus.field) :
    (⟨x, canonicalGenus_le_Omega hx⟩ : Omega) ∈ I.M :=
  I.EOmega_le_M (mem_EOmega_of_mem_field hx)

/-- **The canonical genus field in `M`.** -/
def genusToM : CanonicalGenus.Carrier →ₐ[ℚ] I.M where
  toFun x := ⟨⟨(x : Closure), canonicalGenus_le_Omega x.2⟩, I.mem_M_of_mem_field x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem coe_genusToM (x : CanonicalGenus.Carrier) :
    (((I.genusToM x : I.M) : Omega) : Closure) = (x : Closure) := rfl

/-- The algebra structure `E → M`, for the analytic bridge
`fixedBaseCeiling_lt_of_genus_bound`. -/
abbrev genusAlgebra : Algebra CanonicalGenus.Carrier I.M := I.genusToM.toRingHom.toAlgebra

/-- `√−1 ∈ M`. -/
def sqrtNegOne : I.M := I.genusToM (Genus.gE 0)

theorem sqrtNegOne_sq : I.sqrtNegOne ^ 2 = -1 := by
  rw [sqrtNegOne, ← map_pow, Genus.gE_zero_sq, map_neg, map_one]

theorem radQ_zero_four_five : Genus.radQ 0 * Genus.radQ 4 * Genus.radQ 5 = 3 := by
  decide +kernel

/-- `√3 = √−1 √α₄ √α₅ ∈ M`. -/
def sqrtThree : I.M := I.genusToM (Genus.gE 0 * Genus.gE 4 * Genus.gE 5)

theorem sqrtThree_sq : I.sqrtThree ^ 2 = 3 := by
  rw [sqrtThree, ← map_pow, Genus.sq_gE_mul3, radQ_zero_four_five, map_ofNat, map_ofNat]

end Input

end UnitDistance.Sqrt241.Retained
