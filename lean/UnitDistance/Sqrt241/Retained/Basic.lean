module

public import UnitDistance.Sqrt241.Presentation.LocalLifts
public import UnitDistance.Sqrt241.Cut.Infinite

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The retained map `ρ_B : G_B → Q_B` and the cut kernel in `Ĝ`

Input (`Retained.Input`): local elements `E` of `G_B` with their group
relations and genus labels (`Presentation.LocalElements.Relations`, `.Labels`).
By the presentation (`LocalElements.sourceLifts`, `relators_generate`, `presentation`)
the seven relators generate the relation kernel of `freeMap : F(8) → G_B`, and the
relators are cut words (`Cut.SourceLifts.relators_closure_le_kernel`), so the relation
kernel lies in the cut kernel.
Hence:

* `projB : G_B →ₜ* F(8)/cut` with `projB (freeMap g) = projection g`
  (the arithmetic projection onto the cut quotient, surjective);
* `retainedMap = ρ_B : G_B →ₜ* Q_B` (`= retained ∘ projB`), with
  `(ρ_B g).base = genusLabel g`;
* in `Ĝ`: `kernelHat` (image of the cut kernel, `= ker projB`), `retainedKer`
  (`= ker ρ_B`), `kernelHat ≤ retainedKer ≤ G_B`;
* `core = retainedKer ⊓ σ̂ retainedKer σ̂⁻¹`, written with `comap` of the
  conjugation by `σ̂⁻¹`; it is open and normal in `Ĝ`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation Cut GroupData ProCGroups ProCGroups.Presentations

/-- The inputs of the retained construction (all supplied by the local elements of `Local/`):

* the local elements `E` of `G_B` with their relations and genus labels;
* `σ̂`-compatibility: `c₂ = σ̂ c₁ σ̂⁻¹`, and at the pairs of primes above `3`, `5`, `2`,
  `29` the second-prime elements are conjugate to the first-prime ones by some
  `s ∈ σ̂ G_B` (for the normalized maps `Local.localMapB`, `s = σ̂` or `σ̂⁻¹`);
  the third cap is `F₇²` with `F₇ ∉ G_B` (i.e. `σ̂ F₇⁻¹ ∈ G_B`), or a copy of the first cap
  (version 2's symmetric cut `Retained.inputSym`, without any cap at `7`);
* a complex embedding `phi` of `Ω` whose complex conjugation is `c₁`
  (`Local.phi₁`, `Local.conj₁_isConj`). -/
structure Input where
  E : LocalElements
  relations : E.Relations
  labels : E.Labels
  conj_compat : ((E.conj 1 : GB) : Ghat) = sigmaHat * (E.conj 0 : Ghat) * sigmaHat⁻¹
  tame_compat_q : ∃ s : Ghat, s * sigmaHat⁻¹ ∈ GB ∧
    ((E.tameInertia 1 : GB) : Ghat) = s * (E.tameInertia 0 : Ghat) * s⁻¹ ∧
    ((E.tameFrobenius 1 : GB) : Ghat) = s * (E.tameFrobenius 0 : Ghat) * s⁻¹
  tame_compat_r : ∃ s : Ghat, s * sigmaHat⁻¹ ∈ GB ∧
    ((E.tameInertia 3 : GB) : Ghat) = s * (E.tameInertia 2 : Ghat) * s⁻¹ ∧
    ((E.tameFrobenius 3 : GB) : Ghat) = s * (E.tameFrobenius 2 : Ghat) * s⁻¹
  dyadic_compat : ∃ s : Ghat, s * sigmaHat⁻¹ ∈ GB ∧
    ∀ g, ((E.dyadic 1 g : GB) : Ghat) = s * (E.dyadic 0 g : Ghat) * s⁻¹
  cap_compat : ∃ s : Ghat, s * sigmaHat⁻¹ ∈ GB ∧
    ((E.cap 1 : GB) : Ghat) = s * (E.cap 0 : Ghat) * s⁻¹
  frob7_compat : (∃ F : Ghat, ((E.cap 2 : GB) : Ghat) = F ^ 2 ∧ sigmaHat * F⁻¹ ∈ GB) ∨
    E.cap 2 = E.cap 0
  phi : Omega →+* ℂ
  conj_isConj : NumberField.ComplexEmbedding.IsConj phi ((E.conj 0 : GB) : Ghat)

/-! ### The `σ̂`-core of a subgroup of `Ĝ` -/

theorem mem_GB_or_inv_mul_mem (g : Ghat) : g ∈ GB ∨ sigmaHat⁻¹ * g ∈ GB := by
  by_cases hg : g ∈ GB
  · exact Or.inl hg
  · right
    have h1 := (not_mem_GB_iff g).mp hg
    have h2 : sigmaHat⁻¹ rootOmega = -rootOmega := by
      have h3 := sigmaHat_rootOmega
      have h4 : sigmaHat⁻¹ (sigmaHat rootOmega) = rootOmega := by
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      rw [h3, map_neg] at h4
      rw [← neg_neg (sigmaHat⁻¹ rootOmega), h4]
    rw [mem_GB_iff, AlgEquiv.mul_apply, h1, map_neg, h2, neg_neg]

theorem sigmaHat_inv_not_mem : sigmaHat⁻¹ ∉ GB := fun h => sigmaHat_not_mem (by
  simpa using GB.inv_mem h)

/-- The `σ̂`-core `K ⊓ σ̂ K σ̂⁻¹` of a subgroup `K ≤ Ĝ`. -/
def sigmaCore (K : Subgroup Ghat) : Subgroup Ghat :=
  K ⊓ K.comap (MulAut.conj sigmaHat⁻¹).toMonoidHom

theorem mem_sigmaCore_iff (K : Subgroup Ghat) (x : Ghat) :
    x ∈ sigmaCore K ↔ x ∈ K ∧ sigmaHat⁻¹ * x * sigmaHat ∈ K := by
  change x ∈ K ∧ (MulAut.conj sigmaHat⁻¹) x ∈ K ↔ _
  rw [MulAut.conj_apply, inv_inv]

theorem sigmaCore_le (K : Subgroup Ghat) : sigmaCore K ≤ K := inf_le_left

theorem sigmaCore_mono {K L : Subgroup Ghat} (h : K ≤ L) : sigmaCore K ≤ sigmaCore L :=
  inf_le_inf h (Subgroup.comap_mono h)

/-- A `G_B`-normal subgroup has a `Ĝ`-normal `σ̂`-core. -/
theorem sigmaCore_normal (K : Subgroup Ghat)
    (hK : ∀ h ∈ GB, ∀ x ∈ K, h * x * h⁻¹ ∈ K) : (sigmaCore K).Normal := by
  have hB : ∀ h ∈ GB, ∀ x ∈ sigmaCore K, h * x * h⁻¹ ∈ sigmaCore K := by
    intro h hh x hx
    rw [mem_sigmaCore_iff] at hx ⊢
    refine ⟨hK h hh x hx.1, ?_⟩
    have hh' : sigmaHat⁻¹ * h * sigmaHat ∈ GB := by
      simpa using GB_normal.conj_mem h hh sigmaHat⁻¹
    have he : sigmaHat⁻¹ * (h * x * h⁻¹) * sigmaHat =
        (sigmaHat⁻¹ * h * sigmaHat) * (sigmaHat⁻¹ * x * sigmaHat) *
          (sigmaHat⁻¹ * h * sigmaHat)⁻¹ := by group
    rw [he]
    exact hK _ hh' _ hx.2
  have hσ : ∀ x ∈ sigmaCore K, sigmaHat * x * sigmaHat⁻¹ ∈ sigmaCore K := by
    intro x hx
    rw [mem_sigmaCore_iff] at hx ⊢
    refine ⟨?_, by simpa [mul_assoc] using hx.1⟩
    have he : sigmaHat * x * sigmaHat⁻¹ =
        sigmaHat ^ 2 * (sigmaHat⁻¹ * x * sigmaHat) * (sigmaHat ^ 2)⁻¹ := by group
    rw [he]
    exact hK _ sigmaHat_sq_mem _ hx.2
  constructor
  intro x hx g
  rcases mem_GB_or_inv_mul_mem g with hg | hg
  · exact hB g hg x hx
  · have he : g * x * g⁻¹ =
        sigmaHat * ((sigmaHat⁻¹ * g) * x * (sigmaHat⁻¹ * g)⁻¹) * sigmaHat⁻¹ := by
      group
    rw [he]
    exact hσ _ (hB _ hg x hx)

theorem isOpen_sigmaCore (K : Subgroup Ghat) (hK : IsOpen (K : Set Ghat)) :
    IsOpen (sigmaCore K : Set Ghat) := by
  have h2 : IsOpen ((K.comap (MulAut.conj sigmaHat⁻¹).toMonoidHom : Subgroup Ghat) :
      Set Ghat) := by
    have hc : Continuous fun x : Ghat => sigmaHat⁻¹ * x * sigmaHat⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hK.preimage hc
  exact hK.inter h2

namespace Input

variable (I : Input)

/-- The lifts of the local elements to the free source `F(8)`. -/
abbrev A : SourceLifts := I.E.sourceLifts

theorem hL : I.A.Labels := LocalElements.sourceLifts_labels I.labels

/-- The presentation hypothesis of the cut (the genuine relation `genuineRelation` is the
same local element at both dyadic places). -/
theorem hgen : I.A.Presentation genuineRelation := LocalElements.presentation I.relations I.labels

theorem relators_generate :
    closedNormalClosure (Set.range (I.A.relators genuineRelation)) =
      (relationKernel : Subgroup Source) :=
  LocalElements.relators_generate I.relations I.labels

/-- The relation kernel of `freeMap` lies in the cut kernel. -/
theorem relationKernel_le_kernel : (relationKernel : Subgroup Source) ≤ I.A.kernel := by
  rw [← I.relators_generate]
  exact I.A.relators_closure_le_kernel genuineRelation detector_genuineRelation

theorem infinite_actualQuotient : Infinite I.A.ActualQuotient :=
  I.A.infinite_of_presentation I.hL genuineRelation detector_genuineRelation I.hgen

/-! ### The arithmetic projection `G_B → F(8)/cut` -/

/-- `F(8)/R → F(8)/cut`. -/
def liftR : (Source ⧸ (relationKernel : Subgroup Source)) →ₜ* I.A.ActualQuotient :=
  ProCGroups.QuotientGroup.liftₜ (relationKernel : Subgroup Source) I.A.projection
    (fun _ hg => I.A.projection_eq_one_of_mem (I.relationKernel_le_kernel hg))

theorem liftR_mk (g : Source) :
    I.liftR (QuotientGroup.mk' (relationKernel : Subgroup Source) g) = I.A.projection g := rfl

/-- `G_B → F(8)/cut`, through `F(8)/R ≃ G_B`. -/
def projB : GB →ₜ* I.A.ActualQuotient :=
  I.liftR.comp ⟨freeQuotientEquiv.symm.toMulEquiv.toMonoidHom, freeQuotientEquiv.symm.continuous⟩

theorem projB_apply (g : GB) : I.projB g = I.liftR (freeQuotientEquiv.symm g) := rfl

theorem projB_freeMap (g : Source) : I.projB (freeMap g) = I.A.projection g := by
  have h : freeQuotientEquiv.symm (freeMap g) =
      QuotientGroup.mk' (relationKernel : Subgroup Source) g := by
    rw [ContinuousMulEquiv.symm_apply_eq]
    rfl
  rw [projB_apply, h, liftR_mk]

theorem projB_surjective : Function.Surjective I.projB := by
  intro x
  obtain ⟨g, rfl⟩ := I.A.projection_surjective x
  exact ⟨freeMap g, I.projB_freeMap g⟩

theorem projB_comp_freeMap : I.projB.comp freeMap = I.A.projection :=
  ContinuousMonoidHom.ext (I.projB_freeMap)

/-! ### The retained map `ρ_B` -/

/-- **The retained map** `ρ_B : G_B →ₜ* Q_B`. -/
def retainedMap : GB →ₜ* Retained.Q := (I.A.retained I.hL).comp I.projB

theorem retainedMap_freeMap (g : Source) : I.retainedMap (freeMap g) = retainedFree g := by
  change I.A.retained I.hL (I.projB (freeMap g)) = _
  rw [projB_freeMap, SourceLifts.retained_projection]

theorem retainedMap_base (g : GB) : (I.retainedMap g).base = (genusLabel g).toAdd := by
  obtain ⟨s, rfl⟩ := freeMap_surjective g
  rw [retainedMap_freeMap, retainedFree_base]

theorem retainedMap_eq_one_of_projB {g : GB} (hg : I.projB g = 1) : I.retainedMap g = 1 := by
  change I.A.retained I.hL (I.projB g) = 1
  rw [hg, map_one]

/-! ### Subgroups of `Ĝ` -/

/-- **The cut kernel in `Ĝ`**: the image of the cut kernel of `F(8)` in `G_B ≤ Ĝ`. -/
def kernelHat : Subgroup Ghat := I.projB.toMonoidHom.ker.map GB.subtype

/-- The kernel of `ρ_B`, as a subgroup of `Ĝ`. -/
def retainedKer : Subgroup Ghat := I.retainedMap.toMonoidHom.ker.map GB.subtype

theorem mem_kernelHat_iff (g : Ghat) :
    g ∈ I.kernelHat ↔ ∃ h : g ∈ GB, I.projB ⟨g, h⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem mem_retainedKer_iff (g : Ghat) :
    g ∈ I.retainedKer ↔ ∃ h : g ∈ GB, I.retainedMap ⟨g, h⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem kernelHat_le_GB : I.kernelHat ≤ GB := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem retainedKer_le_GB : I.retainedKer ≤ GB := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem kernelHat_le_retainedKer : I.kernelHat ≤ I.retainedKer := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, I.retainedMap_eq_one_of_projB hx, rfl⟩

theorem freeMap_mem_kernelHat {g : Source} (hg : g ∈ I.A.kernel) :
    ((freeMap g : GB) : Ghat) ∈ I.kernelHat := by
  refine ⟨freeMap g, ?_, rfl⟩
  change I.projB (freeMap g) = 1
  rw [projB_freeMap]
  exact I.A.projection_eq_one_of_mem hg

/-- `G_B`-conjugation preserves `retainedKer`. -/
theorem retainedKer_conj_mem {h x : Ghat} (hh : h ∈ GB) (hx : x ∈ I.retainedKer) :
    h * x * h⁻¹ ∈ I.retainedKer := by
  obtain ⟨hxB, hx1⟩ := (I.mem_retainedKer_iff x).mp hx
  have hm : h * x * h⁻¹ ∈ GB := GB.mul_mem (GB.mul_mem hh hxB) (GB.inv_mem hh)
  refine (I.mem_retainedKer_iff _).mpr ⟨hm, ?_⟩
  have he : (⟨h * x * h⁻¹, hm⟩ : GB) = ⟨h, hh⟩ * ⟨x, hxB⟩ * (⟨h, hh⟩ : GB)⁻¹ := rfl
  rw [he, map_mul, map_mul, map_inv, hx1, mul_one, mul_inv_cancel]

/-- `G_B`-conjugation preserves `kernelHat`. -/
theorem kernelHat_conj_mem {h x : Ghat} (hh : h ∈ GB) (hx : x ∈ I.kernelHat) :
    h * x * h⁻¹ ∈ I.kernelHat := by
  obtain ⟨hxB, hx1⟩ := (I.mem_kernelHat_iff x).mp hx
  have hm : h * x * h⁻¹ ∈ GB := GB.mul_mem (GB.mul_mem hh hxB) (GB.inv_mem hh)
  refine (I.mem_kernelHat_iff _).mpr ⟨hm, ?_⟩
  have he : (⟨h * x * h⁻¹, hm⟩ : GB) = ⟨h, hh⟩ * ⟨x, hxB⟩ * (⟨h, hh⟩ : GB)⁻¹ := rfl
  rw [he, map_mul, map_mul, map_inv, hx1, mul_one, mul_inv_cancel]

theorem isOpen_retainedKer : IsOpen (I.retainedKer : Set Ghat) := by
  have hK : IsOpen ((I.retainedMap.toMonoidHom.ker : Subgroup GB) : Set GB) :=
    (isOpen_discrete ({1} : Set Retained.Q)).preimage I.retainedMap.continuous
  have h := GB_isOpen.isOpenMap_subtype_val _ hK
  rw [retainedKer, Subgroup.coe_map, Subgroup.coe_subtype]
  exact h

theorem isClosed_kernelHat : IsClosed (I.kernelHat : Set Ghat) := by
  have hK : IsClosed ((I.projB.toMonoidHom.ker : Subgroup GB) : Set GB) :=
    ProCGroups.ContinuousMonoidHom.isClosed_ker I.projB
  have hc : IsCompact ((I.projB.toMonoidHom.ker : Subgroup GB) : Set GB) := hK.isCompact
  have h := hc.image (continuous_subtype_val : Continuous (fun x : GB => (x : Ghat)))
  rw [kernelHat, Subgroup.coe_map, Subgroup.coe_subtype]
  exact h.isClosed

/-! ### The core -/

/-- **The core** `retainedKer ⊓ σ̂ retainedKer σ̂⁻¹` (as `x ∈ core ↔ x, σ̂⁻¹ x σ̂ ∈ retainedKer`). -/
def core : Subgroup Ghat := sigmaCore I.retainedKer

theorem mem_core_iff (x : Ghat) :
    x ∈ I.core ↔ x ∈ I.retainedKer ∧ sigmaHat⁻¹ * x * sigmaHat ∈ I.retainedKer :=
  mem_sigmaCore_iff _ x

theorem core_le_retainedKer : I.core ≤ I.retainedKer := sigmaCore_le _

theorem core_le_GB : I.core ≤ GB := I.core_le_retainedKer.trans I.retainedKer_le_GB

instance core_normal : I.core.Normal :=
  sigmaCore_normal _ (fun _ hh _ hx => I.retainedKer_conj_mem hh hx)

theorem isOpen_core : IsOpen (I.core : Set Ghat) := isOpen_sigmaCore _ I.isOpen_retainedKer

theorem isClosed_core : IsClosed (I.core : Set Ghat) :=
  Subgroup.isClosed_of_isOpen _ I.isOpen_core

end Input

end UnitDistance.Sqrt241.Retained
