module

public import UnitDistance.Sqrt241.Retained.Field
public import UnitDistance.Sqrt241.GroupData.MagnusCut
public import UnitDistance.Sqrt241.GroupData.LocalModels
public import UnitDistance.GaloisFiniteQuotientField

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The detector for the centralizer bound

The truncated Magnus cut `ψ : F(8) → Cut` kills the cut kernel, and the class of
`ψ(c₁)` in the finite image of `ψ` has at least `2^15` elements
(`MagnusB.magnus_retains_and_detects`). It descends to `ψ_B : G_B → Cut`
(`magnusB`). The **detector kernel** is the `σ̂`-core of `ker ρ_B ⊓ ker ψ_B`
(`detKer`, open and normal in `Ĝ`, contained in `core`), and the **detector field**
is its fixed field.

**Centralizer bound** (`centralizer_index`): for every finite Galois `K ≤ Ω` whose
fixing group lies in `detKer`, the restriction `c` of `c₁` to `K` has at least
`2^16 = 65536` conjugates in `Gal(K/ℚ)`. The conjugates
`(σ̂^b h) c₁ (σ̂^b h)⁻¹` (`b ∈ {0,1}`, `h ∈ G_B` running over representatives of the
`2^15` classes of `ψ(c₁)`) are pairwise distinct in `Gal(K/ℚ)`: `b` is detected by
the genus label (`c₁ ↦ 10111010`, `c₂ = σ̂c₁σ̂⁻¹ ↦ 11000101`), `h` by `ψ_B`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation Cut GroupData ProCGroups ProCGroups.Presentations

/-- An injectively parametrized family of conjugates bounds the centralizer index
(copy of `TruncatedMagnus.card_le_centralizer_index_of_conjugates_injective`). -/
theorem card_le_centralizer_index_of_conjugates_injective
    {G P : Type*} [Group G] [Finite G] [Finite P] (c : G) (g : P → G)
    (hinj : Function.Injective (fun p => g p * c * (g p)⁻¹)) :
    Nat.card P ≤ (Subgroup.centralizer ({c} : Set G)).index := by
  let f : P → G ⧸ Subgroup.centralizer ({c} : Set G) := fun p => QuotientGroup.mk (g p)
  apply Nat.card_le_card_of_injective f
  intro p q hpq
  apply hinj
  have hmem : (g p)⁻¹ * g q ∈ Subgroup.centralizer ({c} : Set G) := QuotientGroup.eq.mp hpq
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hmem
  have h := congrArg (fun x : G => g p * x * (g q)⁻¹) hc
  simpa [mul_assoc] using h.symm

theorem conjVector_ne : conjVector 0 ≠ conjVector 1 := by decide +kernel

namespace Input

variable (I : Input)

/-! ### The Magnus cut and its descent to `G_B` -/

/-- The cubic tails of the 21 quadratic cut words. -/
abbrev tails : Fin 21 → Magnus.V₃ 8 Magnus.F :=
  Magnus.CutData.relatorTails (FiniteFreeProTwo.isFree 8) I.A.lifts.quadraticWords

/-- The finite truncated Magnus cut group. -/
abbrev MagnusCut : Type := MagnusB.data.Cut I.tails

/-- The truncated Magnus cut `ψ : F(8) → Cut`. -/
def magnus : Source →ₜ* I.MagnusCut := MagnusB.data.freeCut (FiniteFreeProTwo.isFree 8) I.tails

theorem magnus_facts :
    I.A.kernel ≤ retainedFree.toMonoidHom.ker ∧ I.A.kernel ≤ I.magnus.toMonoidHom.ker ∧
      2 ^ 15 ≤ (Subgroup.centralizer
        ({(⟨I.magnus (I.A.conj 0), ⟨I.A.conj 0, rfl⟩⟩ : I.magnus.toMonoidHom.range)} :
          Set I.magnus.toMonoidHom.range)).index :=
  MagnusB.magnus_retains_and_detects (FiniteFreeProTwo.isFree 8) retainedFree
    (fun i => by rw [retainedFree_generator]) I.A.lifts I.hL

/-- `ψ` on the cut quotient. -/
def magnusQ : I.A.ActualQuotient →ₜ* I.MagnusCut :=
  ProCGroups.QuotientGroup.liftₜ I.A.kernel I.magnus I.magnus_facts.2.1

/-- **`ψ_B : G_B → Cut`.** -/
def magnusB : GB →ₜ* I.MagnusCut := I.magnusQ.comp I.projB

theorem magnusB_freeMap (g : Source) : I.magnusB (freeMap g) = I.magnus g := by
  change I.magnusQ (I.projB (freeMap g)) = _
  rw [projB_freeMap]
  rfl

theorem magnusB_conj_zero : I.magnusB (I.E.conj 0) = I.magnus (I.A.conj 0) := by
  change I.magnusB (I.E.conj 0) = I.magnus (LocalElements.lift (I.E.conj 0))
  rw [← magnusB_freeMap, LocalElements.freeMap_lift]

/-- The kernel of `ψ_B` in `Ĝ`. -/
def magnusKer : Subgroup Ghat := I.magnusB.toMonoidHom.ker.map GB.subtype

theorem mem_magnusKer_iff (g : Ghat) :
    g ∈ I.magnusKer ↔ ∃ h : g ∈ GB, I.magnusB ⟨g, h⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem magnusKer_conj_mem {h x : Ghat} (hh : h ∈ GB) (hx : x ∈ I.magnusKer) :
    h * x * h⁻¹ ∈ I.magnusKer := by
  obtain ⟨hxB, hx1⟩ := (I.mem_magnusKer_iff x).mp hx
  have hm : h * x * h⁻¹ ∈ GB := GB.mul_mem (GB.mul_mem hh hxB) (GB.inv_mem hh)
  refine (I.mem_magnusKer_iff _).mpr ⟨hm, ?_⟩
  have he : (⟨h * x * h⁻¹, hm⟩ : GB) = ⟨h, hh⟩ * ⟨x, hxB⟩ * (⟨h, hh⟩ : GB)⁻¹ := rfl
  rw [he, map_mul, map_mul, map_inv, hx1, mul_one, mul_inv_cancel]

theorem isOpen_magnusKer : IsOpen (I.magnusKer : Set Ghat) := by
  have hK : IsOpen ((I.magnusB.toMonoidHom.ker : Subgroup GB) : Set GB) :=
    (isOpen_discrete ({1} : Set I.MagnusCut)).preimage I.magnusB.continuous
  have h := GB_isOpen.isOpenMap_subtype_val _ hK
  rw [magnusKer, Subgroup.coe_map, Subgroup.coe_subtype]
  exact h

/-! ### The detector kernel and field -/

/-- **The detector kernel**: the `σ̂`-core of `ker ρ_B ⊓ ker ψ_B`. -/
def detKer : Subgroup Ghat := sigmaCore (I.retainedKer ⊓ I.magnusKer)

instance detKer_normal : I.detKer.Normal :=
  sigmaCore_normal _ (fun _ hh _ hx =>
    ⟨I.retainedKer_conj_mem hh hx.1, I.magnusKer_conj_mem hh hx.2⟩)

theorem isOpen_detKer : IsOpen (I.detKer : Set Ghat) :=
  isOpen_sigmaCore _ (I.isOpen_retainedKer.inter I.isOpen_magnusKer)

theorem isClosed_detKer : IsClosed (I.detKer : Set Ghat) :=
  Subgroup.isClosed_of_isOpen _ I.isOpen_detKer

theorem detKer_le_core : I.detKer ≤ I.core := sigmaCore_mono inf_le_left

theorem detKer_le_retainedKer : I.detKer ≤ I.retainedKer :=
  (sigmaCore_le _).trans inf_le_left

theorem detKer_le_magnusKer : I.detKer ≤ I.magnusKer :=
  (sigmaCore_le _).trans inf_le_right

/-- The detector field `Ω^detKer` (finite Galois over `ℚ`, contains `M`). -/
def detectorField : IntermediateField ℚ Omega := IntermediateField.fixedField I.detKer

theorem detectorField_fixingSubgroup : I.detectorField.fixingSubgroup = I.detKer :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨I.detKer, I.isClosed_detKer⟩

theorem detectorField_finite_galois :
    FiniteDimensional ℚ I.detectorField ∧ IsGalois ℚ I.detectorField := by
  apply (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois I.detectorField).mp
  rw [detectorField_fixingSubgroup]
  exact ⟨I.isOpen_detKer, I.detKer_normal⟩

instance detectorField_finiteDimensional : FiniteDimensional ℚ I.detectorField :=
  I.detectorField_finite_galois.1

instance detectorField_isGalois : IsGalois ℚ I.detectorField := I.detectorField_finite_galois.2

theorem M_le_detectorField : I.M ≤ I.detectorField :=
  IntermediateField.fixedField_le I.detKer_le_core

/-! ### Labels of conjugates of `c₁` -/

theorem genusLabel_conj (h g : GB) : genusLabel (h * g * h⁻¹) = genusLabel g := by
  rw [map_mul, map_mul, map_inv, mul_comm (genusLabel h), mul_assoc, mul_inv_cancel, mul_one]

/-- Two elements of `G_B` congruent modulo `detKer` have the same label and the same
Magnus image. -/
theorem label_magnus_eq_of_mem_detKer {u v : GB} (h : (u : Ghat)⁻¹ * v ∈ I.detKer) :
    genusLabel u = genusLabel v ∧ I.magnusB u = I.magnusB v := by
  have h1 := I.detKer_le_retainedKer h
  have h2 := I.detKer_le_magnusKer h
  obtain ⟨hB, hr⟩ := (I.mem_retainedKer_iff _).mp h1
  obtain ⟨hB', hm⟩ := (I.mem_magnusKer_iff _).mp h2
  have e1 : (⟨(u : Ghat)⁻¹ * v, hB⟩ : GB) = u⁻¹ * v := rfl
  have e2 : (⟨(u : Ghat)⁻¹ * v, hB'⟩ : GB) = u⁻¹ * v := rfl
  rw [e1] at hr
  rw [e2] at hm
  refine ⟨?_, ?_⟩
  · have hl : genusLabel (u⁻¹ * v) = 1 := by
      apply Multiplicative.toAdd.injective
      rw [← I.retainedMap_base, hr]
      rfl
    rw [map_mul, map_inv] at hl
    exact inv_mul_eq_one.mp hl
  · rw [map_mul, map_inv] at hm
    exact inv_mul_eq_one.mp hm

theorem conj_one_label : genusLabel (I.E.conj 1) = Multiplicative.ofAdd (conjVector 1) :=
  I.labels.conj 1

theorem conj_zero_label : genusLabel (I.E.conj 0) = Multiplicative.ofAdd (conjVector 0) :=
  I.labels.conj 0

/-- `σ̂ (h c₁ h⁻¹) σ̂⁻¹ = h' c₂ h'⁻¹` with `h' = σ̂ h σ̂⁻¹ ∈ G_B`. -/
theorem sigma_conj_conj_mem (h : GB) :
    sigmaHat * ((h : Ghat) * (I.E.conj 0 : Ghat) * (h : Ghat)⁻¹) * sigmaHat⁻¹ =
      (sigmaHat * h * sigmaHat⁻¹) * (I.E.conj 1 : Ghat) * (sigmaHat * h * sigmaHat⁻¹)⁻¹ := by
  rw [I.conj_compat]
  group

/-! ### The centralizer bound -/

section Index

variable (K : IntermediateField ℚ Omega) [FiniteDimensional ℚ K] [IsGalois ℚ K]

/-- Restriction `Ĝ → Gal(K/ℚ)`. -/
abbrev res : Ghat →ₜ* Gal(K/ℚ) := GaloisEmbedding.restriction K.val

theorem res_eq_iff (u v : Ghat) : res K u = res K v ↔ u⁻¹ * v ∈ K.fixingSubgroup := by
  rw [← GaloisQuotient.restriction_kernel K, MonoidHom.mem_ker, map_mul, map_inv]
  change res K u = res K v ↔ (res K u)⁻¹ * res K v = 1
  rw [inv_mul_eq_one]

/-- The image of the Magnus cut. -/
abbrev MagnusRange : Subgroup I.MagnusCut := I.magnus.toMonoidHom.range

/-- `ψ(c₁)` in the Magnus range. -/
def magnusConj : I.MagnusRange := ⟨I.magnus (I.A.conj 0), ⟨I.A.conj 0, rfl⟩⟩

/-- A preimage in `G_B` of an element of the Magnus range. -/
def liftRange (x : I.MagnusRange) : GB := freeMap (Classical.choose x.2)

theorem magnusB_liftRange (x : I.MagnusRange) : I.magnusB (I.liftRange x) = x := by
  rw [liftRange, magnusB_freeMap]
  exact Classical.choose_spec x.2

/-- The parametrized conjugators `σ̂^b h`. -/
def conjugator (p : Bool × (I.MagnusRange ⧸ Subgroup.centralizer ({I.magnusConj} :
    Set I.MagnusRange))) : Ghat :=
  (if p.1 then sigmaHat else 1) * (I.liftRange p.2.out : Ghat)

theorem conj_in_GB_eq {y y' : GB}
    (h : ((y : Ghat) * (I.E.conj 0 : Ghat) * (y : Ghat)⁻¹)⁻¹ *
      ((y' : Ghat) * (I.E.conj 0 : Ghat) * (y' : Ghat)⁻¹) ∈ I.detKer) :
    I.magnusB y * I.magnusB (I.E.conj 0) * (I.magnusB y)⁻¹ =
      I.magnusB y' * I.magnusB (I.E.conj 0) * (I.magnusB y')⁻¹ := by
  have h' := (I.label_magnus_eq_of_mem_detKer (u := y * I.E.conj 0 * y⁻¹)
    (v := y' * I.E.conj 0 * y'⁻¹) (by simpa using h)).2
  simpa [map_mul, map_inv] using h'

theorem out_eq_of_magnus {t t' : I.MagnusRange ⧸ Subgroup.centralizer ({I.magnusConj} :
      Set I.MagnusRange)}
    (h : ((t.out : I.MagnusRange) : I.MagnusCut) * I.magnus (I.A.conj 0) *
        ((t.out : I.MagnusRange) : I.MagnusCut)⁻¹ =
      ((t'.out : I.MagnusRange) : I.MagnusCut) * I.magnus (I.A.conj 0) *
        ((t'.out : I.MagnusRange) : I.MagnusCut)⁻¹) : t = t' := by
  rw [← QuotientGroup.out_eq' t, ← QuotientGroup.out_eq' t']
  apply QuotientGroup.eq.mpr
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, magnusConj]
  calc ((t.out : I.MagnusRange) : I.MagnusCut)⁻¹ * (t'.out : I.MagnusRange) *
        I.magnus (I.A.conj 0)
      = ((t.out : I.MagnusRange) : I.MagnusCut)⁻¹ *
          (((t'.out : I.MagnusRange) : I.MagnusCut) * I.magnus (I.A.conj 0) *
            ((t'.out : I.MagnusRange) : I.MagnusCut)⁻¹) *
          ((t'.out : I.MagnusRange) : I.MagnusCut) := by group
    _ = ((t.out : I.MagnusRange) : I.MagnusCut)⁻¹ *
          (((t.out : I.MagnusRange) : I.MagnusCut) * I.magnus (I.A.conj 0) *
            ((t.out : I.MagnusRange) : I.MagnusCut)⁻¹) *
          ((t'.out : I.MagnusRange) : I.MagnusCut) := by rw [h]
    _ = I.magnus (I.A.conj 0) * (((t.out : I.MagnusRange) : I.MagnusCut)⁻¹ *
          ((t'.out : I.MagnusRange) : I.MagnusCut)) := by group

/-- The key injectivity for `b = b' = 0`. -/
theorem param_eq_of_GB {t t' : I.MagnusRange ⧸ Subgroup.centralizer ({I.magnusConj} :
      Set I.MagnusRange)}
    (h : ((I.liftRange t.out : Ghat) * (I.E.conj 0 : Ghat) * (I.liftRange t.out : Ghat)⁻¹)⁻¹ *
      ((I.liftRange t'.out : Ghat) * (I.E.conj 0 : Ghat) * (I.liftRange t'.out : Ghat)⁻¹) ∈
        I.detKer) : t = t' := by
  have h1 := I.conj_in_GB_eq h
  rw [magnusB_liftRange, magnusB_liftRange, magnusB_conj_zero] at h1
  exact I.out_eq_of_magnus h1

theorem hK_detKer_conj {K : IntermediateField ℚ Omega} (hK : K.fixingSubgroup ≤ I.detKer)
    {u v : Ghat} (h : u⁻¹ * v ∈ K.fixingSubgroup) : u⁻¹ * v ∈ I.detKer := hK h

theorem conjugator_injective (hK : K.fixingSubgroup ≤ I.detKer) :
    Function.Injective (fun p => res K (I.conjugator p) * res K (I.E.conj 0 : Ghat) *
      (res K (I.conjugator p))⁻¹) := by
  rintro ⟨b, t⟩ ⟨b', t'⟩ hpq
  dsimp only at hpq
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, res_eq_iff] at hpq
  have hD := hK hpq
  set y := I.liftRange t.out
  set y' := I.liftRange t'.out
  -- the conjugates as elements of `G_B`
  have hlab : ∀ (c : Bool) (z : GB), (if c then sigmaHat else 1) * (z : Ghat) *
      (I.E.conj 0 : Ghat) * ((if c then sigmaHat else 1) * (z : Ghat))⁻¹ ∈ GB := by
    intro c z
    apply GB_normal.conj_mem _ (I.E.conj 0).2
  -- labels decide `b`
  have hb : b = b' := by
    by_contra hne
    let u : GB := ⟨_, hlab b y⟩
    let v : GB := ⟨_, hlab b' y'⟩
    have huv : (u : Ghat)⁻¹ * v ∈ I.detKer := by
      simpa [u, v, conjugator, mul_assoc] using hD
    have hl := (I.label_magnus_eq_of_mem_detKer huv).1
    -- label of the conjugate
    have hval : ∀ (c : Bool) (z : GB), genusLabel (⟨_, hlab c z⟩ : GB) =
        if c then Multiplicative.ofAdd (conjVector 1) else Multiplicative.ofAdd (conjVector 0) := by
      intro c z
      cases c
      · have he : (⟨_, hlab false z⟩ : GB) = z * I.E.conj 0 * z⁻¹ := by
          apply Subtype.ext
          simp
        rw [he, genusLabel_conj, conj_zero_label]
        rfl
      · have hz : sigmaHat * (z : Ghat) * sigmaHat⁻¹ ∈ GB := GB_normal.conj_mem _ z.2 _
        have he : (⟨_, hlab true z⟩ : GB) =
            ⟨_, hz⟩ * I.E.conj 1 * (⟨_, hz⟩ : GB)⁻¹ := by
          apply Subtype.ext
          simp only [ite_true, Subgroup.coe_mul, Subgroup.coe_inv]
          rw [I.conj_compat]
          group
        rw [he, genusLabel_conj, conj_one_label]
        rfl
    rw [hval, hval] at hl
    cases b <;> cases b'
    · exact hne rfl
    · exact conjVector_ne (Multiplicative.ofAdd.injective hl)
    · exact conjVector_ne (Multiplicative.ofAdd.injective hl).symm
    · exact hne rfl
  subst hb
  congr 1
  cases b
  · apply I.param_eq_of_GB
    simpa [conjugator, y, y'] using hD
  · apply I.param_eq_of_GB
    have hD' : sigmaHat⁻¹ * ((sigmaHat * (y : Ghat) * (I.E.conj 0 : Ghat) *
        (sigmaHat * (y : Ghat))⁻¹)⁻¹ * (sigmaHat * (y' : Ghat) * (I.E.conj 0 : Ghat) *
        (sigmaHat * (y' : Ghat))⁻¹)) * sigmaHat⁻¹⁻¹ ∈ I.detKer := by
      apply (I.detKer_normal).conj_mem
      simpa [conjugator, y, y', mul_assoc] using hD
    have he : sigmaHat⁻¹ * ((sigmaHat * (y : Ghat) * (I.E.conj 0 : Ghat) *
        (sigmaHat * (y : Ghat))⁻¹)⁻¹ * (sigmaHat * (y' : Ghat) * (I.E.conj 0 : Ghat) *
        (sigmaHat * (y' : Ghat))⁻¹)) * sigmaHat⁻¹⁻¹ =
        ((y : Ghat) * (I.E.conj 0 : Ghat) * (y : Ghat)⁻¹)⁻¹ *
          ((y' : Ghat) * (I.E.conj 0 : Ghat) * (y' : Ghat)⁻¹) := by group
    rw [he] at hD'
    exact hD'

/-- **The centralizer bound.** For every finite Galois `K ≤ Ω` with `Gal(Ω/K) ≤ detKer`,
the restriction of `c₁` to `K` has centralizer index at least `2^16`. -/
theorem centralizer_index (hK : K.fixingSubgroup ≤ I.detKer) :
    65536 ≤ (Subgroup.centralizer ({res K (I.E.conj 0 : Ghat)} : Set Gal(K/ℚ))).index := by
  have hcard : Nat.card (Bool × (I.MagnusRange ⧸ Subgroup.centralizer ({I.magnusConj} :
      Set I.MagnusRange))) = 2 * (Subgroup.centralizer ({I.magnusConj} :
        Set I.MagnusRange)).index := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, Subgroup.index]
  have h15 : 2 ^ 15 ≤ (Subgroup.centralizer ({I.magnusConj} : Set I.MagnusRange)).index :=
    I.magnus_facts.2.2
  have hle := card_le_centralizer_index_of_conjugates_injective (res K (I.E.conj 0 : Ghat))
    (fun p => res K (I.conjugator p)) (I.conjugator_injective K hK)
  rw [hcard] at hle
  omega

end Index

end Input

end UnitDistance.Sqrt241.Retained
