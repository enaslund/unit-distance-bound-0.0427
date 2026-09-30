module

public import UnitDistance.Sqrt241.DyadicLink.Radical
public import UnitDistance.GroupAugmentationClassTwo
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.FreeProC.Basic

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The Kummer cocycle of `√β₁` on `G_B` (dyadic link, step 2)

Let `t = √β₁ ∈ Ω` (`tOm`, from `sqrtBeta_mem_Omega`) and `s = √α₅`. For `g ∈ G_B` with
genus label `v`, `g` fixes `a, b ∈ B` and sends `√α₃ ↦ (-1)^{v₃} √α₃`, so
`g(t)² = a + (-1)^{v₃} b √α₃`, which is `t²` (`v₃ = 0`) or `β̄₁ = (s/t)²` (`v₃ = 1`).
With the reference roots `ref 0 = t`, `ref 1 = s/t` (`ref`), `g t = ± ref v₃`; the sign
`kummerChar g ∈ F₂` satisfies

    kummerChar (g h) = kummerChar g + kummerChar h + v₅ w₃        (`kummerChar_mul`)

(`v, w` the labels of `g, h`). Hence `g ↦ (v, kummerChar g)` is a continuous
homomorphism `kummerMap : G_B →ₜ* KummerQ` into the class-two group
`F₂⁸ ×_{β₃₅} F₂` with `β₃₅(v, w) = v₅ w₃` (`kummerForm`). In particular `g²` acts on
`t` by `(-1)^{v₃ v₅}` and a commutator `[g, h]` by `(-1)^{v₃ w₅ + v₅ w₃}`.
-/

open scoped NumberField
open NumberField

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.DyadicLink

open Tower Base CanonicalGenus Multiquadratic ClassTwo ProCGroups ProCGroups.ProC

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ### The radical in `Ω` -/

/-- `t = √β₁` as an element of `Ω`. -/
def tOm : Omega := ⟨sqrtBeta, sqrtBeta_mem_Omega⟩

@[simp] theorem coe_tOm : (tOm : Closure) = sqrtBeta := rfl

theorem tOm_ne_zero : tOm ≠ 0 := fun h => sqrtBeta_ne_zero (congrArg Subtype.val h)

/-- `a = -25 + 2√241 ∈ Ω`. -/
def aOm : Omega :=
  ⟨-25 + 2 * baseRoot,
    add_mem (neg_mem (ofNat_mem Omega 25)) (mul_mem (ofNat_mem Omega 2) baseRoot_mem_Omega)⟩

/-- `b = -139 - 9√241 ∈ Ω`. -/
def bOm : Omega :=
  ⟨-139 - 9 * baseRoot,
    sub_mem (neg_mem (ofNat_mem Omega 139)) (mul_mem (ofNat_mem Omega 9) baseRoot_mem_Omega)⟩

theorem coe_aOm : (aOm : Closure) = -25 + 2 * baseRoot := rfl

theorem coe_bOm : (bOm : Closure) = -139 - 9 * baseRoot := rfl

theorem aOm_mem_BinOmega : aOm ∈ BinOmega :=
  (mem_BinOmega_iff aOm).mpr
    (add_mem (neg_mem (ofNat_mem B 25)) (mul_mem (ofNat_mem B 2) baseRoot_mem_B))

theorem bOm_mem_BinOmega : bOm ∈ BinOmega :=
  (mem_BinOmega_iff bOm).mpr
    (sub_mem (neg_mem (ofNat_mem B 139)) (mul_mem (ofNat_mem B 9) baseRoot_mem_B))

theorem tOm_sq : tOm ^ 2 = aOm + bOm * genusRootOmega 3 := by
  apply Subtype.ext
  rw [IntermediateField.coe_pow, IntermediateField.coe_add, IntermediateField.coe_mul, coe_tOm,
    sqrtBeta_sq, coe_aOm, coe_bOm, coe_genusRootOmega]
  rfl

theorem sq_s_div_tOm :
    (genusRootOmega 5 * tOm⁻¹) ^ 2 = aOm + (-1 : Omega) * bOm * genusRootOmega 3 := by
  apply Subtype.ext
  rw [IntermediateField.coe_pow, IntermediateField.coe_mul, IntermediateField.coe_inv, coe_tOm,
    coe_genusRootOmega, IntermediateField.coe_add, IntermediateField.coe_mul,
    IntermediateField.coe_mul, IntermediateField.coe_neg, IntermediateField.coe_one, coe_aOm,
    coe_bOm, coe_genusRootOmega, ← div_eq_mul_inv, sq_genusRoot_div_sqrtBeta, betaBar]
  ring

/-! ### Reference roots -/

/-- The reference roots `ref 0 = √β₁`, `ref 1 = √α₅ / √β₁` (a root of `β̄₁`). -/
def ref (x : ZMod 2) : Omega := if x = 0 then tOm else genusRootOmega 5 * tOm⁻¹

theorem ref_zero : ref 0 = tOm := ite_eq_left rfl

theorem ref_one : ref 1 = genusRootOmega 5 * tOm⁻¹ := ite_eq_right (by decide)

theorem ref_ne_zero (x : ZMod 2) : ref x ≠ 0 := by
  rcases zmod2_cases x with rfl | rfl
  · rw [ref_zero]
    exact tOm_ne_zero
  · rw [ref_one]
    exact mul_ne_zero (genusRootOmega_ne_zero 5) (inv_ne_zero tOm_ne_zero)

theorem ref_sq (x : ZMod 2) :
    ref x ^ 2 = aOm + binarySign x * bOm * genusRootOmega 3 := by
  rcases zmod2_cases x with rfl | rfl
  · rw [ref_zero, tOm_sq, binarySign_zero, one_mul]
  · rw [ref_one, sq_s_div_tOm]
    simp [binarySign, binarySignInteger]

theorem s_mul_ref_inv (x : ZMod 2) : genusRootOmega 5 * (ref x)⁻¹ = ref (x + 1) := by
  rcases zmod2_cases x with rfl | rfl
  · rw [ref_zero, zero_add, ref_one]
  · rw [ref_one, show (1 : ZMod 2) + 1 = 0 by decide, ref_zero, mul_inv, inv_inv,
      ← mul_assoc, mul_inv_cancel₀ (genusRootOmega_ne_zero 5), one_mul]

/-! ### The action of `G_B` -/

theorem apply_rootOmega (g : GB) : (g : Ghat) rootOmega = rootOmega :=
  (mem_GB_iff (g : Ghat)).mp g.2

theorem apply_aOm (g : GB) : (g : Ghat) aOm = aOm := fixes_BinOmega g aOm aOm_mem_BinOmega

theorem apply_bOm (g : GB) : (g : Ghat) bOm = bOm := fixes_BinOmega g bOm bOm_mem_BinOmega

theorem apply_genusRootOmega' (g : GB) (k : Fin 8) :
    (g : Ghat) (genusRootOmega k) = binarySign ((genusLabel g).toAdd k) * genusRootOmega k := by
  rw [genusLabel_apply, genusChar_action]

theorem apply_tOm_sq (g : GB) :
    ((g : Ghat) tOm) ^ 2 = ref ((genusLabel g).toAdd 3) ^ 2 := by
  rw [← map_pow, tOm_sq, map_add, map_mul, apply_aOm, apply_bOm, apply_genusRootOmega', ref_sq]
  ring

open Classical in
/-- **The Kummer sign** of `g ∈ G_B`: `g √β₁ = (-1)^{kummerChar g} · ref v₃`. -/
def kummerChar (g : GB) : ZMod 2 :=
  if (g : Ghat) tOm = ref ((genusLabel g).toAdd 3) then 0 else 1

theorem kummerChar_action (g : GB) :
    (g : Ghat) tOm = binarySign (kummerChar g) * ref ((genusLabel g).toAdd 3) := by
  classical
  unfold kummerChar
  split_ifs with h
  · rw [binarySign_zero, one_mul, h]
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp (apply_tOm_sq g) with h' | h'
    · exact absurd h' h
    · rw [h']
      simp [binarySign, binarySignInteger]

theorem kummerChar_eq_of_action (g : GB) (x : ZMod 2)
    (h : (g : Ghat) tOm = binarySign x * ref ((genusLabel g).toAdd 3)) : kummerChar g = x := by
  apply binarySign_injective (E := Omega)
  apply mul_right_cancel₀ (ref_ne_zero ((genusLabel g).toAdd 3))
  rw [← kummerChar_action, h]

theorem binarySign_inv (x : ZMod 2) : (binarySign x : Omega)⁻¹ = binarySign x := by
  rcases zmod2_cases x with rfl | rfl
  · simp
  · simp [binarySign, binarySignInteger]

theorem apply_ref (g : GB) (x : ZMod 2) :
    (g : Ghat) (ref x) = binarySign (kummerChar g + (genusLabel g).toAdd 5 * x) *
      ref ((genusLabel g).toAdd 3 + x) := by
  rcases zmod2_cases x with rfl | rfl
  · rw [ref_zero, kummerChar_action, mul_zero, add_zero, add_zero]
  · rw [ref_one, map_mul, map_inv₀, apply_genusRootOmega', kummerChar_action, mul_one,
      ← s_mul_ref_inv, binarySign_add, mul_inv, binarySign_inv]
    ring

/-- **The Kummer cocycle**: `c(gh) = c(g) + c(h) + v₅ w₃`. -/
theorem kummerChar_mul (g h : GB) :
    kummerChar (g * h) = kummerChar g + kummerChar h +
      (genusLabel g).toAdd 5 * (genusLabel h).toAdd 3 := by
  apply kummerChar_eq_of_action
  have hl : (genusLabel (g * h)).toAdd = (genusLabel g).toAdd + (genusLabel h).toAdd := by
    rw [map_mul, toAdd_mul]
  rw [Subgroup.coe_mul, AlgEquiv.mul_apply, kummerChar_action h, map_mul, map_binarySign,
    apply_ref, hl, Pi.add_apply, binarySign_add, binarySign_add, binarySign_add]
  ring

theorem kummerChar_one : kummerChar 1 = 0 := by
  apply kummerChar_eq_of_action
  rw [map_one, binarySign_zero, one_mul]
  change tOm = ref ((0 : Fin 8 → ZMod 2) 3)
  rw [Pi.zero_apply, ref_zero]

/-! ### The Kummer map -/

/-- `β₃₅(v, w) = v₅ w₃`: the cocycle of the `D₄`-extension `B(√α₃, √α₅, √β₁)/B`. -/
def kummerForm : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun v w => v 5 * w 3)
    (fun v v' w => by simp [add_mul]) (fun c v w => by simp [mul_assoc])
    (fun v w w' => by simp [mul_add]) (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[simp] theorem kummerForm_apply (v w : Fin 8 → ZMod 2) : kummerForm v w = v 5 * w 3 := rfl

/-- The class-two group `F₂⁸ ×_{β₃₅} F₂`. -/
abbrev KummerQ : Type := GroupModel kummerForm

instance : Group KummerQ := inferInstanceAs (Group (GroupModel kummerForm))
instance kummerTopology : TopologicalSpace KummerQ := ⊥
instance kummerDiscrete : DiscreteTopology KummerQ := ⟨rfl⟩
instance kummerTopologicalGroup : IsTopologicalGroup KummerQ := inferInstance
instance kummerT2 : T2Space KummerQ := inferInstance
instance kummerCompact : CompactSpace KummerQ := inferInstance
instance kummerTotallyDisconnected : TotallyDisconnectedSpace KummerQ := inferInstance

theorem kummerQ_isTwoGroup : IsPGroup 2 KummerQ := GroupModel.isTwoGroup kummerForm

theorem kummerQ_hasPGroupOpenNormalBasis : HasPGroupOpenNormalBasis 2 KummerQ := by
  apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  exact ⟨inferInstance, kummerQ_isTwoGroup.of_surjective (QuotientGroup.mk' (U : Subgroup KummerQ))
    (QuotientGroup.mk'_surjective (U : Subgroup KummerQ))⟩

/-- The Kummer map as a group homomorphism. -/
def kummerHom : GB →* KummerQ where
  toFun g := ⟨(genusLabel g).toAdd, kummerChar g⟩
  map_one' := by
    apply GroupModel.ext
    · change (genusLabel 1).toAdd = 0
      rw [map_one]
      rfl
    · exact kummerChar_one
  map_mul' g h := by
    apply GroupModel.ext
    · change (genusLabel (g * h)).toAdd = (genusLabel g).toAdd + (genusLabel h).toAdd
      rw [map_mul, toAdd_mul]
    · change kummerChar (g * h) = kummerChar g + kummerChar h +
        kummerForm (genusLabel g).toAdd (genusLabel h).toAdd
      rw [kummerChar_mul, kummerForm_apply]

theorem isIntegral_tOm : IsIntegral ℚ tOm := Algebra.IsIntegral.isIntegral tOm

theorem kummerHom_continuous : Continuous kummerHom := by
  let U : Subgroup GB := genusLabel.toMonoidHom.ker ⊓
    (IntermediateField.adjoin ℚ {tOm}).fixingSubgroup.subgroupOf GB
  have hfin : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {tOm}) :=
    IntermediateField.adjoin.finiteDimensional isIntegral_tOm
  have hU : IsOpen (U : Set GB) := by
    apply IsOpen.inter
    · exact (isOpen_discrete ({1} : Set (Multiplicative (Fin 8 → ZMod 2)))).preimage
        genusLabel.continuous
    · exact (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val
  apply continuous_of_le_ker kummerHom U hU
  rintro g ⟨hg1, hg2⟩
  have hl : genusLabel g = 1 := MonoidHom.mem_ker.mp hg1
  have ht : (g : Ghat) tOm = tOm :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg2 tOm
      (IntermediateField.mem_adjoin_simple_self ℚ tOm)
  have hc : kummerChar g = 0 := by
    apply kummerChar_eq_of_action
    rw [ht, hl, binarySign_zero, one_mul]
    change tOm = ref ((0 : Fin 8 → ZMod 2) 3)
    rw [Pi.zero_apply, ref_zero]
  rw [MonoidHom.mem_ker]
  apply GroupModel.ext
  · change (genusLabel g).toAdd = 0
    rw [hl]
    rfl
  · exact hc

/-- **The Kummer map** `Ψ : G_B →ₜ* F₂⁸ ×_{β₃₅} F₂`, `g ↦ (genus label, Kummer sign)`. -/
def kummerMap : GB →ₜ* KummerQ := ⟨kummerHom, kummerHom_continuous⟩

@[simp] theorem kummerMap_base (g : GB) : (kummerMap g).base = (genusLabel g).toAdd := rfl

@[simp] theorem kummerMap_central (g : GB) : (kummerMap g).central = kummerChar g := rfl

/-- An element of `G_B` with trivial Kummer image fixes `√β₁`. -/
theorem fixes_tOm_of_kummerMap_eq_one {g : GB} (hg : kummerMap g = 1) : (g : Ghat) tOm = tOm := by
  have hl : (genusLabel g).toAdd = 0 := congrArg GroupModel.base hg
  have hc : kummerChar g = 0 := congrArg GroupModel.central hg
  rw [kummerChar_action, hc, hl, binarySign_zero, one_mul, Pi.zero_apply, ref_zero]

/-- Squares act on `√β₁` through `v₃ v₅`. -/
theorem kummerChar_sq (g : GB) :
    kummerChar (g ^ 2) = (genusLabel g).toAdd 3 * (genusLabel g).toAdd 5 := by
  rw [pow_two, kummerChar_mul]
  have h : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [h, zero_add, mul_comm]

/-- Commutators `[g, h] = g⁻¹ h⁻¹ g h` act on `√β₁` through `v₅ w₃ + v₃ w₅`. -/
theorem kummerChar_commutator (g h : GB) :
    kummerChar (g⁻¹ * h⁻¹ * g * h) =
      (genusLabel g).toAdd 5 * (genusLabel h).toAdd 3 +
        (genusLabel g).toAdd 3 * (genusLabel h).toAdd 5 := by
  have hc := congrArg GroupModel.central (GroupModel.commutator_coordinates kummerForm
    (kummerMap g) (kummerMap h))
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at hc
  rw [kummerMap_central] at hc
  rw [hc]
  change (genusLabel g).toAdd 5 * (genusLabel h).toAdd 3 -
      (genusLabel h).toAdd 5 * (genusLabel g).toAdd 3 = _
  rw [sub_eq_add_neg, ZModModule.neg_eq_self, mul_comm ((genusLabel h).toAdd 5)]

end UnitDistance.Sqrt241.DyadicLink
