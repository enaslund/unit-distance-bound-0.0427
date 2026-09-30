module

public import UnitDistance.Sqrt241.Local.TameData
public import UnitDistance.Sqrt241.Local.Maps
public import UnitDistance.ProfiniteGeneratedTameCompactness
public import UnitDistance.ProPOpenNormalStage
public import UnitDistance.HomKernelTransfer
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.GaloisPCompositum

@[expose] public section
set_option backward.privateInPublic true

/-!
# Tame pairs in `G_B` at `𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂`

For each tame prime `k` (`3` or `5`) there are `t` in the chosen absolute inertia group
and `s` in the chosen absolute decomposition group, with the genus labels of the
chosen place, whose images in `G_B` satisfy the literal tame relation
`s t s⁻¹ = t^p` and generate the local inertia and decomposition images in every
finite quotient of `G_B` (`tame_generating_relation`).

For every open normal `U ≤ G_B`, an open normal `W ≤ Ĝ` inside `U` has a finite Galois
fixed field `F ⊆ Ω`; the finite-level pair of `TameData.lean` for the compositum
`F·E` (a finite Galois `2`-extension of `ℚ` containing the genus roots) satisfies
the relation and generation modulo `U`. Compactness of the local pair space (with
the closed label condition) gives one pair for all `U`. No assumption `E ≤ Ω` is
needed.

The normalized elements are `tameInertia q`, `tameFrobenius q` for `q : Fin 4`
(`𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂`), images under `localMapB` of the chosen absolute pair.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Local

open NumberField CanonicalGenus Base UnitDistance.PrimeCompletion Multiquadratic Tower
open ProCGroups ProCGroups.ProC ClassFieldTower.Martinet.Shafarevich

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ## Compactness with a closed side condition -/

section Compactness

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable {I D : Type*} [Group I] [TopologicalSpace I] [CompactSpace I]
  [Group D] [TopologicalSpace D] [CompactSpace D]

/-- `ProfiniteTame.exists_generated_tame_pair` with the labels replaced by an arbitrary
closed condition on the local pair. -/
theorem exists_generated_tame_pair_of_closed (i : I →ₜ* G) (d : D →ₜ* G)
    (C₀ : Set (I × D)) (hC₀ : IsClosed C₀) (q : ℕ)
    (h : ∀ U : OpenNormalSubgroup G, ∃ t : I, ∃ s : D, (t, s) ∈ C₀ ∧
      d s * i t * (d s)⁻¹ * (i t ^ q)⁻¹ ∈ U ∧
      ProfiniteTame.quotientGenerates i d U (i t) (d s)) :
    ∃ t : I, ∃ s : D, (t, s) ∈ C₀ ∧ d s * i t * (d s)⁻¹ = i t ^ q ∧
      ∀ U : OpenNormalSubgroup G, ProfiniteTame.quotientGenerates i d U (i t) (d s) := by
  let f : I × D → G := fun p => d p.2 * i p.1 * (d p.2)⁻¹ * (i p.1 ^ q)⁻¹
  have hf : Continuous f := by fun_prop
  let C : OpenNormalSubgroup G → Set (I × D) := fun U =>
    {p | p ∈ C₀ ∧ f p ∈ U ∧ ProfiniteTame.quotientGenerates i d U (i p.1) (d p.2)}
  have hclosed (U : OpenNormalSubgroup G) : IsClosed (C U) :=
    hC₀.inter ((U.toOpenSubgroup.isClosed.preimage hf).inter
      (ProfiniteTame.isClosed_quotientGenerates i d U))
  have hnonempty (U : OpenNormalSubgroup G) : (C U).Nonempty := by
    obtain ⟨t, s, hts, hrel, hgen⟩ := h U
    exact ⟨(t, s), hts, hrel, hgen⟩
  have hdir : Directed (· ⊇ ·) C := by
    intro U V
    refine ⟨U ⊓ V, ?_, ?_⟩
    · intro p hp
      exact ⟨hp.1, hp.2.1.1, ProfiniteTame.quotientGenerates_mono i d inf_le_left hp.2.2⟩
    · intro p hp
      exact ⟨hp.1, hp.2.1.2, ProfiniteTame.quotientGenerates_mono i d inf_le_right hp.2.2⟩
  let : Nonempty (OpenNormalSubgroup G) :=
    ⟨{toOpenSubgroup := ⊤, isNormal' := show (⊤ : Subgroup G).Normal from inferInstance}⟩
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C
    hdir hnonempty (fun U => (hclosed U).isCompact) hclosed
  have hpU (U : OpenNormalSubgroup G) :
      p ∈ C₀ ∧ f p ∈ U ∧ ProfiniteTame.quotientGenerates i d U (i p.1) (d p.2) :=
    Set.mem_iInter.mp hp U
  have hrel : f p = 1 := ProfiniteTame.eq_one_of_mem_all_openNormal (fun U => (hpU U).2.1)
  exact ⟨p.1, p.2, (hpU Classical.ofNonempty).1, mul_inv_eq_one.mp hrel, fun U => (hpU U).2.2⟩

end Compactness

/-! ## Labels are closed conditions -/

/-- Restriction to the canonical genus field. -/
def genusRestriction : Gal(Closure/ℚ) →ₜ* Gal(CanonicalGenus.Carrier/ℚ) :=
  GaloisEmbedding.restriction CanonicalGenus.field.val

theorem hasLabel_iff_restriction (σ : Gal(Closure/ℚ)) (v : Fin 8 → ZMod 2) :
    HasLabel σ v ↔ ∀ k, genusRestriction σ (Genus.gE k) = binarySign (v k) * Genus.gE k := by
  have hc (k : Fin 8) : ((genusRestriction σ (Genus.gE k) : CanonicalGenus.Carrier) : Closure) =
      σ (genusRoot k) :=
    GaloisEmbedding.restriction_commutes CanonicalGenus.field.val σ (Genus.gE k)
  constructor
  · intro h k
    apply Subtype.ext
    rw [hc, h k]
    simp [binarySign]
  · intro h k
    rw [← hc, h k]
    simp [binarySign]

theorem isClosed_hasLabel (v : Fin 8 → ZMod 2) :
    IsClosed {σ : Gal(Closure/ℚ) | HasLabel σ v} := by
  have he : {σ : Gal(Closure/ℚ) | HasLabel σ v} = genusRestriction ⁻¹'
      {a | ∀ k, a (Genus.gE k) = binarySign (v k) * Genus.gE k} := by
    ext σ
    exact hasLabel_iff_restriction σ v
  rw [he]
  exact (isClosed_discrete _).preimage genusRestriction.continuous

/-! ## Finite Galois layers of `Ω` below an open normal subgroup of `G_B` -/

theorem isOpen_map_GB (U : OpenNormalSubgroup GB) :
    IsOpen ((Subgroup.map GB.subtype (U : Subgroup GB) : Subgroup Ghat) : Set Ghat) := by
  have h : ((Subgroup.map GB.subtype (U : Subgroup GB) : Subgroup Ghat) : Set Ghat) =
      Subtype.val '' (U : Set GB) := by
    ext x
    simp only [Subgroup.coe_map, Subgroup.coe_subtype]
    rfl
  rw [h]
  exact GB_isOpen.isOpenMap_subtype_val _ U.isOpen

theorem exists_openNormal_le (U : OpenNormalSubgroup GB) :
    ∃ W : OpenNormalSubgroup Ghat, ∀ g ∈ W, ∃ h : g ∈ GB, (⟨g, h⟩ : GB) ∈ U := by
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_map_GB U) (Subgroup.one_mem _)
  refine ⟨W, fun g hg => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hW hg
  exact ⟨u.2, hu⟩

theorem isPGroup_carrier : IsPGroup 2 Gal(CanonicalGenus.Carrier/ℚ) := by
  apply IsPGroup.of_card (n := 9)
  rw [IsGalois.card_aut_eq_finrank, Genus.finrank_carrier]
  norm_num

/-- The finite Galois field of `Ω` fixed by an open normal subgroup, inside the closure. -/
def layerCl (W : OpenNormalSubgroup Ghat) : IntermediateField ℚ Closure :=
  (IntermediateField.fixedField (W : Subgroup Ghat)).map Omega.val

theorem mem_layerCl (W : OpenNormalSubgroup Ghat) (x : Omega)
    (hx : x ∈ IntermediateField.fixedField (W : Subgroup Ghat)) : (x : Closure) ∈ layerCl W :=
  ⟨x, hx, rfl⟩

/-- The compositum of the layer with the genus field. -/
def layerE (W : OpenNormalSubgroup Ghat) : IntermediateField ℚ Closure :=
  layerCl W ⊔ CanonicalGenus.field

section LayerInstances

variable (W : OpenNormalSubgroup Ghat)

def layerEquiv : IntermediateField.fixedField (W : Subgroup Ghat) ≃ₐ[ℚ] layerCl W :=
  IntermediateField.equivMap _ Omega.val

instance layerFix_finite : FiniteDimensional ℚ (IntermediateField.fixedField (W : Subgroup Ghat)) :=
  (ArithmeticProP.openNormalFiniteGaloisField ℚ Omega W).finiteDimensional

instance layerFix_galois : IsGalois ℚ (IntermediateField.fixedField (W : Subgroup Ghat)) :=
  (ArithmeticProP.openNormalFiniteGaloisField ℚ Omega W).isGalois

instance layerCl_finite : FiniteDimensional ℚ (layerCl W) :=
  (layerEquiv W).toLinearEquiv.finiteDimensional

instance layerCl_galois : IsGalois ℚ (layerCl W) := IsGalois.of_algEquiv (layerEquiv W)

instance layerE_finite : FiniteDimensional ℚ (layerE W) :=
  IntermediateField.finiteDimensional_sup _ _

instance layerE_normal : Normal ℚ (layerE W) :=
  IntermediateField.normal_sup ℚ Closure (layerCl W) CanonicalGenus.field

instance layerE_galois : IsGalois ℚ (layerE W) := IsGalois.mk

instance layerE_numberField : NumberField (layerE W) := NumberField.of_module_finite ℚ _

theorem layerFix_isPGroup : IsPGroup 2 Gal(IntermediateField.fixedField (W : Subgroup Ghat)/ℚ) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hquot := HasOpenNormalBasisInClass.quotient_mem
    (FiniteGroupClass.pGroup_formation 2) Ghat_hasPGroupOpenNormalBasis W
  let e := ArithmeticProP.openNormalQuotientEquivFiniteGaloisField ℚ Omega W
  exact hquot.2.of_surjective e.toMonoidHom e.surjective

theorem layerE_isPGroup : IsPGroup 2 Gal(layerE W/ℚ) := by
  have h₁ : IsPGroup 2 Gal(layerCl W/ℚ) :=
    (layerFix_isPGroup W).of_surjective (AlgEquiv.autCongr (layerEquiv W)).toMonoidHom
      (AlgEquiv.autCongr (layerEquiv W)).surjective
  exact ClassFieldTower.Sawin.isPGroup_galois_sup (layerCl W) CanonicalGenus.field h₁
    isPGroup_carrier

theorem genusRoot_mem_layerE (k : Fin 8) :
    genusRoot k ∈ Set.range (layerE W).val :=
  ⟨⟨genusRoot k, le_sup_right (a := layerCl W) (genusRoot_mem k)⟩, rfl⟩

end LayerInstances

/-- An absolute element fixing the compositum layer maps into `W`. -/
theorem toGhat_mem_of_restriction_eq_one (W : OpenNormalSubgroup Ghat) (σ : Gal(Closure/ℚ))
    (h : GaloisEmbedding.restriction (layerE W).val σ = 1) : toGhat σ ∈ W := by
  have hfix : toGhat σ ∈ (IntermediateField.fixedField (W : Subgroup Ghat)).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    apply Subtype.ext
    rw [toGhat_apply]
    have hx' : (x : Closure) ∈ layerE W :=
      le_sup_left (a := layerCl W) (mem_layerCl W x hx)
    have hc := GaloisEmbedding.restriction_commutes (layerE W).val σ ⟨(x : Closure), hx'⟩
    rw [h] at hc
    exact hc.symm
  rw [InfiniteGalois.fixingSubgroup_fixedField
    (⟨(W : Subgroup Ghat), W.isClosed⟩ : ClosedSubgroup Ghat)] at hfix
  exact hfix

/-! ## Transport of quotient generation along a continuous endomorphism -/

theorem quotientGenerates_comp {G : Type*} [Group G] [TopologicalSpace G]
    {I D : Type*} [Group I] [TopologicalSpace I] [Group D] [TopologicalSpace D]
    (α : G →ₜ* G) (i : I →ₜ* G) (d : D →ₜ* G) (τ φ : G)
    (h : ∀ U : OpenNormalSubgroup G, ProfiniteTame.quotientGenerates i d U τ φ)
    (U : OpenNormalSubgroup G) :
    ProfiniteTame.quotientGenerates (α.comp i) (α.comp d) U (α τ) (α φ) := by
  let U₀ := OpenNormalSubgroup.comap α.toMonoidHom α.continuous U
  have hle : (U₀ : Subgroup G) ≤ (U : Subgroup G).comap α.toMonoidHom := fun x hx => hx
  let f : G ⧸ (U₀ : Subgroup G) →* G ⧸ (U : Subgroup G) :=
    QuotientGroup.map (U₀ : Subgroup G) (U : Subgroup G) α.toMonoidHom hle
  have hf (g : G) : f (QuotientGroup.mk' (U₀ : Subgroup G) g) =
      QuotientGroup.mk' (U : Subgroup G) (α g) := rfl
  obtain ⟨h1, h2⟩ := h U₀
  refine ⟨fun x => ?_, fun y => ?_⟩
  · obtain ⟨n, hn⟩ := h1 x
    refine ⟨n, ?_⟩
    change QuotientGroup.mk' (U : Subgroup G) (α (i x)) = (QuotientGroup.mk' (U : Subgroup G) (α τ)) ^ n
    rw [← hf, ← hf, ← map_zpow, hn]
  · have hmap : Subgroup.closure ({QuotientGroup.mk' (U₀ : Subgroup G) τ,
        QuotientGroup.mk' (U₀ : Subgroup G) φ} : Set (G ⧸ (U₀ : Subgroup G))) ≤
        (Subgroup.closure ({QuotientGroup.mk' (U : Subgroup G) (α τ),
          QuotientGroup.mk' (U : Subgroup G) (α φ)} : Set (G ⧸ (U : Subgroup G)))).comap f := by
      apply (Subgroup.closure_le _).mpr
      intro z hz
      rcases hz with rfl | rfl
      · rw [SetLike.mem_coe, Subgroup.mem_comap, hf]
        exact Subgroup.subset_closure (by simp)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, hf]
        exact Subgroup.subset_closure (by simp)
    have hy := hmap (h2 y)
    rw [Subgroup.mem_comap, hf] at hy
    exact hy

/-! ## The profinite tame pairs at the chosen places -/

/-- The chosen absolute inertia group above `tamePrime k`, mapped into `G_B`. -/
def tameInertiaMapB (k : Fin 2) : AbsoluteInertia (tamePrime k) →ₜ* GB :=
  (decompositionMapB (tamePrime k) (tameIsSquare k)).comp
    (finitePlaceAbsoluteInertiaInclusion ℚ (place (tamePrime k)))

theorem tameInertiaMapB_apply (k : Fin 2) (t : AbsoluteInertia (tamePrime k)) :
    tameInertiaMapB k t = decompositionMapB (tamePrime k) (tameIsSquare k) t.val := rfl

/-- The finite-level pair gives the relation and generation modulo each `U`. -/
theorem tame_generating_relation_mod (k : Fin 2) (U : OpenNormalSubgroup GB) :
    ∃ t : AbsoluteInertia (tamePrime k), ∃ s : AbsoluteDecomposition (tamePrime k),
      (t, s) ∈ {x : AbsoluteInertia (tamePrime k) × AbsoluteDecomposition (tamePrime k) |
        HasLabel x.1.val.val (tameTau (tameIndex k (tamePlace k))) ∧
        HasLabel x.2.val (tamePhi (tameIndex k (tamePlace k)))} ∧
      decompositionMapB (tamePrime k) (tameIsSquare k) s * tameInertiaMapB k t *
        (decompositionMapB (tamePrime k) (tameIsSquare k) s)⁻¹ *
        (tameInertiaMapB k t ^ (tamePrime k).val)⁻¹ ∈ U ∧
      ProfiniteTame.quotientGenerates (tameInertiaMapB k)
        (decompositionMapB (tamePrime k) (tameIsSquare k)) U
        (tameInertiaMapB k t) (decompositionMapB (tamePrime k) (tameIsSquare k) s) := by
  obtain ⟨W, hW⟩ := exists_openNormal_le U
  obtain ⟨t, s, ht, hs, hrel, hIgen, hDgen⟩ :=
    exists_absolute_tame_pair_at k (layerE W) (layerE W).val (layerE_isPGroup W)
      (genusRoot_mem_layerE W)
  let p := tamePrime k
  let dB := decompositionMapB p (tameIsSquare k)
  let dR := decompositionRestriction p (layerE W) (layerE W).val
  let q : GB →* GB ⧸ (U : Subgroup GB) := QuotientGroup.mk' (U : Subgroup GB)
  have hmemU (d : AbsoluteDecomposition p) (hd : dR d = 1) : dB d ∈ U := by
    have hW' := hW (toGhat d.val) (toGhat_mem_of_restriction_eq_one W d.val hd)
    obtain ⟨_, hU⟩ := hW'
    exact hU
  have hker : dR.ker ≤ (q.comp dB.toMonoidHom).ker := by
    intro d hd
    change q (dB d) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hmemU d hd)
  refine ⟨t, s, ⟨ht, hs⟩, ?_, ?_, ?_⟩
  · have h := hmemU _ hrel
    simpa only [map_mul, map_inv, map_pow, tameInertiaMapB_apply] using h
  · intro x
    obtain ⟨n, hn⟩ := hIgen x
    refine ⟨n, ?_⟩
    exact HomKernelTransfer.eq_zpow_of_eq_zpow dR (q.comp dB.toMonoidHom) hker
      (x := x.val) (t := t.val) (n := n) hn
  · intro y
    have hy : dR y ∈ Subgroup.closure (dR '' ({t.val, s} : Set (AbsoluteDecomposition p))) := by
      simpa only [Set.image_insert_eq, Set.image_singleton] using hDgen y
    have hg := HomKernelTransfer.mem_closure_image dR (q.comp dB.toMonoidHom) hker hy
    rw [Set.image_insert_eq, Set.image_singleton] at hg
    exact hg

/-- **Profinite labelled tame pair at the chosen place above `3` or `5`.** -/
theorem tame_generating_relation (k : Fin 2) :
    ∃ t : AbsoluteInertia (tamePrime k), ∃ s : AbsoluteDecomposition (tamePrime k),
      HasLabel t.val.val (tameTau (tameIndex k (tamePlace k))) ∧
      HasLabel s.val (tamePhi (tameIndex k (tamePlace k))) ∧
      decompositionMapB (tamePrime k) (tameIsSquare k) s * tameInertiaMapB k t *
        (decompositionMapB (tamePrime k) (tameIsSquare k) s)⁻¹ =
          tameInertiaMapB k t ^ (tamePrime k).val ∧
      ∀ U : OpenNormalSubgroup GB, ProfiniteTame.quotientGenerates (tameInertiaMapB k)
        (decompositionMapB (tamePrime k) (tameIsSquare k)) U
        (tameInertiaMapB k t) (decompositionMapB (tamePrime k) (tameIsSquare k) s) := by
  let := ArithmeticProP.finitePlaceAbsoluteInertia_compactSpace ℚ (place (tamePrime k))
  let := ArithmeticProP.finitePlaceAbsoluteDecomposition_compactSpace ℚ (place (tamePrime k))
  have hC : IsClosed {x : AbsoluteInertia (tamePrime k) × AbsoluteDecomposition (tamePrime k) |
      HasLabel x.1.val.val (tameTau (tameIndex k (tamePlace k))) ∧
      HasLabel x.2.val (tamePhi (tameIndex k (tamePlace k)))} := by
    apply IsClosed.inter
    · exact (isClosed_hasLabel _).preimage
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
    · exact (isClosed_hasLabel _).preimage (continuous_subtype_val.comp continuous_snd)
  obtain ⟨t, s, ⟨ht, hs⟩, hrel, hgen⟩ := exists_generated_tame_pair_of_closed
    (tameInertiaMapB k) (decompositionMapB (tamePrime k) (tameIsSquare k)) _ hC _
    (tame_generating_relation_mod k)
  exact ⟨t, s, ht, hs, hrel, hgen⟩

/-- The chosen absolute inertia generator above `tamePrime k`. -/
def tameInertiaAbs (k : Fin 2) : AbsoluteInertia (tamePrime k) :=
  (tame_generating_relation k).choose

/-- The chosen normalized absolute Frobenius above `tamePrime k`. -/
def tameFrobeniusAbs (k : Fin 2) : AbsoluteDecomposition (tamePrime k) :=
  (tame_generating_relation k).choose_spec.choose

theorem tameInertiaAbs_hasLabel (k : Fin 2) :
    HasLabel (tameInertiaAbs k).val.val (tameTau (tameIndex k (tamePlace k))) :=
  (tame_generating_relation k).choose_spec.choose_spec.1

theorem tameFrobeniusAbs_hasLabel (k : Fin 2) :
    HasLabel (tameFrobeniusAbs k).val (tamePhi (tameIndex k (tamePlace k))) :=
  (tame_generating_relation k).choose_spec.choose_spec.2.1

theorem tameAbs_relation (k : Fin 2) :
    decompositionMapB (tamePrime k) (tameIsSquare k) (tameFrobeniusAbs k) *
        tameInertiaMapB k (tameInertiaAbs k) *
        (decompositionMapB (tamePrime k) (tameIsSquare k) (tameFrobeniusAbs k))⁻¹ =
      tameInertiaMapB k (tameInertiaAbs k) ^ (tamePrime k).val :=
  (tame_generating_relation k).choose_spec.choose_spec.2.2.1

theorem tameAbs_generates (k : Fin 2) (U : OpenNormalSubgroup GB) :
    ProfiniteTame.quotientGenerates (tameInertiaMapB k)
      (decompositionMapB (tamePrime k) (tameIsSquare k)) U
      (tameInertiaMapB k (tameInertiaAbs k))
      (decompositionMapB (tamePrime k) (tameIsSquare k) (tameFrobeniusAbs k)) :=
  (tame_generating_relation k).choose_spec.choose_spec.2.2.2 U

/-! ## Normalized tame elements at `𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂` -/

/-- Rational prime index of the tame place `q` (`0 ↦ 3`, `1 ↦ 5`). -/
def tameK : Fin 4 → Fin 2 := ![0, 0, 1, 1]
/-- Prime of `B` of the tame place `q`. -/
def tameP : Fin 4 → Fin 2 := ![0, 1, 0, 1]

theorem tameIndex_tameK_tameP : ∀ q : Fin 4, tameIndex (tameK q) (tameP q) = q := by decide

/-- The normalized decomposition map at the tame place `q`. -/
def tameDecompositionMap (q : Fin 4) : AbsoluteDecomposition (tamePrime (tameK q)) →ₜ* GB :=
  localMapB (tamePrime (tameK q)) (tameIsSquare (tameK q)) (tamePlace (tameK q)) (tameP q)

/-- The normalized inertia map at the tame place `q`. -/
def tameInertiaMap (q : Fin 4) : AbsoluteInertia (tamePrime (tameK q)) →ₜ* GB :=
  (conjGB (frame (tamePlace (tameK q)) (tameP q))).comp (tameInertiaMapB (tameK q))

theorem tameInertiaMap_apply (q : Fin 4) (t : AbsoluteInertia (tamePrime (tameK q))) :
    tameInertiaMap q t = tameDecompositionMap q t.val := rfl

/-- **The tame inertia generator `τ` at `q ∈ {𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂}`.** -/
def tameInertia (q : Fin 4) : GB := tameInertiaMap q (tameInertiaAbs (tameK q))

/-- **The normalized tame Frobenius `φ` at `q`** (it fixes `√π_q`). -/
def tameFrobenius (q : Fin 4) : GB := tameDecompositionMap q (tameFrobeniusAbs (tameK q))

theorem tame_label_normalize (k P : Fin 2) (f : Fin 4 → Fin 8 → ZMod 2)
    (hf : ∀ k P : Fin 2, sigmaMatrix (f (tameIndex k P)) = f (tameIndex k (1 - P))) :
    (if P = tamePlace k then f (tameIndex k (tamePlace k))
      else sigmaMatrix (f (tameIndex k (tamePlace k)))) = f (tameIndex k P) := by
  by_cases hP : P = tamePlace k
  · simp only [hP, ↓reduceIte]
  · have e : ∀ a b : Fin 8 → ZMod 2, (if P = tamePlace k then a else b) = b :=
      fun a b => by simp [hP]
    rw [e, hf, fin2_one_sub_of_ne hP]

theorem tameInertia_hasLabel (q : Fin 4) : HasLabelHat (tameInertia q) (tameTau q) := by
  have h := localMapB_hasLabel (tamePrime (tameK q)) (tameIsSquare (tameK q))
    (tamePlace (tameK q)) (tameP q) (tameInertiaAbs (tameK q)).val
    (tameInertiaAbs_hasLabel (tameK q))
  rw [tame_label_normalize _ _ tameTau sigmaMatrix_tameTau, tameIndex_tameK_tameP] at h
  exact h

theorem tameFrobenius_hasLabel (q : Fin 4) : HasLabelHat (tameFrobenius q) (tamePhi q) := by
  have h := localMapB_hasLabel (tamePrime (tameK q)) (tameIsSquare (tameK q))
    (tamePlace (tameK q)) (tameP q) (tameFrobeniusAbs (tameK q))
    (tameFrobeniusAbs_hasLabel (tameK q))
  rw [tame_label_normalize _ _ tamePhi sigmaMatrix_tamePhi, tameIndex_tameK_tameP] at h
  exact h

/-- **The literal tame relation** `φ τ φ⁻¹ = τ^N` in `G_B`, `N = 3, 3, 5, 5`. -/
theorem tame_relation (q : Fin 4) :
    tameFrobenius q * tameInertia q * (tameFrobenius q)⁻¹ = tameInertia q ^ tameN q := by
  have h := congrArg (conjGB (frame (tamePlace (tameK q)) (tameP q))) (tameAbs_relation (tameK q))
  simp only [map_mul, map_inv, map_pow] at h
  have hN : tameN q = (tamePrime (tameK q)).val := by
    rw [← tameN_eq, tameIndex_tameK_tameP]
  rw [hN]
  exact h

/-- **Generation in every finite quotient of `G_B`**: the image of the local inertia group
is generated by `τ`, that of the local decomposition group by `τ, φ`. -/
theorem tame_generates (q : Fin 4) (U : OpenNormalSubgroup GB) :
    ProfiniteTame.quotientGenerates (tameInertiaMap q) (tameDecompositionMap q) U
      (tameInertia q) (tameFrobenius q) :=
  quotientGenerates_comp (conjGB (frame (tamePlace (tameK q)) (tameP q)))
    (tameInertiaMapB (tameK q)) (decompositionMapB (tamePrime (tameK q)) (tameIsSquare (tameK q)))
    _ _ (tameAbs_generates (tameK q)) U

end UnitDistance.Sqrt241.Local
