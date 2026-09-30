module

public import UnitDistance.Sqrt241.Tower.OmegaB
public import UnitDistance.Sqrt241.Tower.ConjugationTransport
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Topologies.ContinuousMulEquiv
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.GroupTheory.IndexNormal

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The bridge between the B-world and the ℚ-world

The B-world field `Ω_B = OmegaB` (`Tower/OmegaB.lean`) lives in `Bbar = AlgebraicClosure B`.
The ℚ-world is the fixed closure `Closure = AlgebraicClosure ℚ`, which contains
`B = ℚ(√241)` literally. We fix the `B`-isomorphism `chi : Closure ≃ₐ[B] Bbar`
and set `Ω := chi⁻¹(Ω_B)` (`Omega`), a ℚ-subfield of `Closure` containing `B`.

Main results:

* `Omega_isGalois`: `Ω` is Galois over ℚ. Every ℚ-automorphism `σ` of the
  closure is carried by `chi` to a ring automorphism of `Bbar` which is
  semilinear over `σ|_B`; it maps every admissible layer to an admissible layer
  (`ConjugationTransport`), hence `Ω_B` into itself.
* `Ghat = Gal(Ω/ℚ)`, `GB ≤ Ghat` the fixing group of `B` (open, index 2,
  normal), `sigmaHat ∉ GB`.
* `bridge : Gal(Ω_B/B) ≃ₜ* GB`.
* `le_Omega_of_admissible`: a finite Galois 2-extension of ℚ containing `B`
  and unramified over `B` outside `S` lies in `Ω`.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.Tower

open Base CanonicalGenus IntermediateField ClassFieldTower.Sawin

/-! ### The two closures -/

/-- The algebraic closure of ℚ is an algebraic closure of `B`. -/
instance isAlgClosure_B_Closure : IsAlgClosure B Closure := ⟨inferInstance, inferInstance⟩

/-- The fixed `B`-isomorphism between the two algebraic closures. -/
def chi : Closure ≃ₐ[B] Bbar := IsAlgClosure.equiv B Closure Bbar

theorem chi_coe (b : B) : chi (b : Closure) = algebraMap B Bbar b :=
  chi.commutes b

theorem chi_symm_algebraMap (b : B) : chi.symm (algebraMap B Bbar b) = (b : Closure) :=
  chi.symm.commutes b

/-! ### ℚ-automorphisms of the closure, seen in the B-world -/

/-- The restriction to `B` of a ℚ-automorphism of the closure. -/
def baseRestrict (σ : Closure ≃ₐ[ℚ] Closure) : B ≃+* B :=
  (σ.restrictNormal B).toRingEquiv

theorem coe_baseRestrict (σ : Closure ≃ₐ[ℚ] Closure) (b : B) :
    ((baseRestrict σ b : B) : Closure) = σ b :=
  AlgEquiv.restrictNormal_commutes σ B b

/-- `σ` carried to `Bbar` by `chi`. -/
def conjBbar (σ : Closure ≃ₐ[ℚ] Closure) : Bbar ≃+* Bbar :=
  chi.symm.toRingEquiv.trans (σ.toRingEquiv.trans chi.toRingEquiv)

theorem conjBbar_apply (σ : Closure ≃ₐ[ℚ] Closure) (x : Bbar) :
    conjBbar σ x = chi (σ (chi.symm x)) :=
  rfl

theorem conjBbar_chi (σ : Closure ≃ₐ[ℚ] Closure) (x : Closure) :
    conjBbar σ (chi x) = chi (σ x) := by
  rw [conjBbar_apply, AlgEquiv.symm_apply_apply]

/-- `conjBbar σ` is semilinear over `σ|_B`. -/
theorem conjBbar_isSemilinearOver (σ : Closure ≃ₐ[ℚ] Closure) :
    IsSemilinearOver (baseRestrict σ) (conjBbar σ) := by
  intro a
  rw [conjBbar_apply, chi_symm_algebraMap, ← coe_baseRestrict, chi_coe]

/-! ### Stability of `Ω_B` under semilinear automorphisms -/

/-- `S` (the places above `30`) is stable under every automorphism of `B`. -/
theorem S_stable (τ₀ : B ≃+* B) :
    ∀ v w : HeightOneSpectrum (𝓞 B),
      (∀ x : 𝓞 B, x ∈ v.asIdeal ↔ RingOfIntegers.mapRingEquiv τ₀ x ∈ w.asIdeal) →
        w ∉ S → v ∉ S := by
  intro v w hvw hw hv
  apply hw
  have h := (hvw 30).1 hv
  rwa [map_ofNat] at h

/-- The image of an admissible layer under a semilinear automorphism of `Bbar`
is an admissible layer. -/
def admissibleMapSemilinear {τ₀ : B ≃+* B} {τ : Bbar ≃+* Bbar}
    (hτ : IsSemilinearOver τ₀ τ) (E : ProP.FinitePExtension B 2 S) :
    ProP.FinitePExtension B 2 S :=
  haveI := E.val.finiteDimensional
  haveI := E.val.isGalois
  ⟨{ toIntermediateField := mapSemilinear hτ E.val.toIntermediateField
     finiteDimensional := finiteDimensional_mapSemilinear hτ _
     isGalois := isGalois_mapSemilinear hτ _ },
    isPGroup_mapSemilinear hτ _ E.property.1,
    isUnramifiedAtFinitePlacesOutside_mapSemilinear hτ _ (S_stable τ₀) E.property.2⟩

theorem admissibleMapSemilinear_val {τ₀ : B ≃+* B} {τ : Bbar ≃+* Bbar}
    (hτ : IsSemilinearOver τ₀ τ) (E : ProP.FinitePExtension B 2 S) :
    (admissibleMapSemilinear hτ E).val.toIntermediateField =
      mapSemilinear hτ E.val.toIntermediateField :=
  rfl

theorem mem_OmegaB_iff_exists (x : Bbar) :
    x ∈ OmegaB ↔ ∃ E : ProP.FinitePExtension B 2 S, x ∈ E.val.toIntermediateField := by
  have : Nonempty (ProP.FinitePExtension B 2 S) := ⟨ProP.FinitePExtension.bot B 2 S⟩
  have h := IntermediateField.coe_iSup_of_directed (ProP.FinitePExtension.directed B 2 S)
  change x ∈ ((⨆ E : ProP.FinitePExtension B 2 S, E.val.toIntermediateField :
    IntermediateField B Bbar) : Set Bbar) ↔ _
  rw [h, Set.mem_iUnion]
  rfl

/-- `Ω_B` is mapped into itself by every semilinear automorphism of `Bbar`. -/
theorem mapSemilinear_OmegaB_le {τ₀ : B ≃+* B} {τ : Bbar ≃+* Bbar}
    (hτ : IsSemilinearOver τ₀ τ) : mapSemilinear hτ OmegaB ≤ OmegaB := by
  intro x hx
  rw [mem_mapSemilinear_iff, mem_OmegaB_iff_exists] at hx
  obtain ⟨E, hE⟩ := hx
  have hmem : x ∈ mapSemilinear hτ E.val.toIntermediateField := hE
  rw [← admissibleMapSemilinear_val hτ E] at hmem
  exact ProP.le_maximalProPOutside (admissibleMapSemilinear hτ E) hmem

theorem apply_mem_OmegaB {τ₀ : B ≃+* B} {τ : Bbar ≃+* Bbar}
    (hτ : IsSemilinearOver τ₀ τ) {x : Bbar} (hx : x ∈ OmegaB) : τ x ∈ OmegaB :=
  mapSemilinear_OmegaB_le hτ (apply_mem_mapSemilinear hτ hx)

/-! ### `Ω` in the closure of ℚ -/

/-- `Ω_B` carried to the closure of ℚ, as a `B`-subfield. -/
def OmegaBcl : IntermediateField B Closure :=
  OmegaB.map (chi.symm : Bbar →ₐ[B] Closure)

theorem mem_OmegaBcl_iff (x : Closure) : x ∈ OmegaBcl ↔ chi x ∈ OmegaB := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change chi (chi.symm y) ∈ OmegaB
    rwa [AlgEquiv.apply_symm_apply]
  · intro h
    exact ⟨chi x, h, chi.symm_apply_apply x⟩

/-- The field `Ω := chi⁻¹(Ω_B)`, as a ℚ-subfield of the closure. -/
def Omega : IntermediateField ℚ Closure :=
  OmegaBcl.restrictScalars ℚ

theorem mem_Omega_iff (x : Closure) : x ∈ Omega ↔ chi x ∈ OmegaB :=
  mem_OmegaBcl_iff x

theorem B_le_Omega : B ≤ Omega := by
  intro x hx
  rw [mem_Omega_iff, show x = ((⟨x, hx⟩ : B) : Closure) from rfl, chi_coe]
  exact OmegaB.algebraMap_mem _

theorem baseRoot_mem_Omega : baseRoot ∈ Omega :=
  B_le_Omega baseRoot_mem_B

instance Omega_normal : Normal ℚ Omega := by
  rw [normal_iff_forall_map_le']
  rintro σ _ ⟨x, hx, rfl⟩
  change x ∈ Omega at hx
  change σ x ∈ Omega
  rw [mem_Omega_iff] at hx ⊢
  rw [← conjBbar_chi]
  exact apply_mem_OmegaB (conjBbar_isSemilinearOver σ) hx

/-- `Ω` is Galois over ℚ. -/
instance Omega_isGalois : IsGalois ℚ Omega where

/-! ### The groups `Ĝ = Gal(Ω/ℚ)` and `G_B` -/

/-- The ℚ-world group `Ĝ = Gal(Ω/ℚ)`. -/
abbrev Ghat : Type := Omega ≃ₐ[ℚ] Omega

/-- `B` as a ℚ-subfield of `Ω`. -/
def BinOmega : IntermediateField ℚ Omega :=
  IntermediateField.restrict B_le_Omega

theorem mem_BinOmega_iff (x : Omega) : x ∈ BinOmega ↔ (x : Closure) ∈ B :=
  IntermediateField.mem_restrict B_le_Omega x

/-- `√241` as an element of `Ω`. -/
def rootOmega : Omega := ⟨baseRoot, baseRoot_mem_Omega⟩

@[simp] theorem coe_rootOmega : (rootOmega : Closure) = baseRoot := rfl

theorem rootOmega_mem_BinOmega : rootOmega ∈ BinOmega :=
  (mem_BinOmega_iff _).2 baseRoot_mem_B

theorem rootOmega_sq : rootOmega ^ 2 = 241 := by
  apply Subtype.ext
  change baseRoot ^ 2 = ((241 : Omega) : Closure)
  rw [baseRoot_sq]
  rfl

instance BinOmega_finiteDimensional : FiniteDimensional ℚ BinOmega :=
  (IntermediateField.restrictAlgEquiv B_le_Omega).toLinearEquiv.finiteDimensional

theorem finrank_BinOmega : Module.finrank ℚ BinOmega = 2 :=
  (IntermediateField.restrictAlgEquiv B_le_Omega).toLinearEquiv.finrank_eq.symm.trans
    finrank_eq_two

/-- Every element of `B ⊆ Ω` is `a + b√241` with rational `a, b`. -/
theorem exists_coords_BinOmega (x : Omega) (hx : x ∈ BinOmega) :
    ∃ a b : ℚ, x = algebraMap ℚ Omega a + algebraMap ℚ Omega b * rootOmega := by
  obtain ⟨a, b, hab⟩ := exists_coords (⟨(x : Closure), (mem_BinOmega_iff x).1 hx⟩ : B)
  refine ⟨a, b, Subtype.ext ?_⟩
  have h := congrArg (fun y : B ↦ (y : Closure)) hab
  simpa using h

/-- The subgroup `G_B ≤ Ĝ` fixing `B`. -/
def GB : Subgroup Ghat := BinOmega.fixingSubgroup

theorem mem_GB_iff (g : Ghat) : g ∈ GB ↔ g rootOmega = rootOmega := by
  constructor
  · intro hg
    exact hg ⟨rootOmega, rootOmega_mem_BinOmega⟩
  · rintro hg ⟨x, hx⟩
    obtain ⟨a, b, rfl⟩ := exists_coords_BinOmega x hx
    change g (algebraMap ℚ Omega a + algebraMap ℚ Omega b * rootOmega) = _
    rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hg]

/-- The image of `√241` under an element of `Ĝ` is `±√241`. -/
theorem apply_rootOmega (g : Ghat) : g rootOmega = rootOmega ∨ g rootOmega = -rootOmega := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, rootOmega_sq, map_ofNat]

theorem GB_isOpen : IsOpen (GB : Set Ghat) :=
  IntermediateField.fixingSubgroup_isOpen BinOmega

theorem GB_isClosed : IsClosed (GB : Set Ghat) :=
  IntermediateField.fixingSubgroup_isClosed BinOmega

theorem GB_index : GB.index = 2 := by
  rw [GB, ← IntermediateField.finrank_eq_fixingSubgroup_index, finrank_BinOmega]

instance GB_normal : GB.Normal :=
  Subgroup.normal_of_index_eq_two GB_index

theorem exists_not_mem_GB : ∃ g : Ghat, g ∉ GB := by
  by_contra h
  have htop : GB = ⊤ := eq_top_iff.2 fun g _ ↦ by
    by_contra hg
    exact h ⟨g, hg⟩
  have := GB_index
  rw [htop, Subgroup.index_top] at this
  exact absurd this (by norm_num)

/-- A fixed element of `Ĝ` outside `G_B` (a lift of the nontrivial
automorphism `σ` of `B`). -/
def sigmaHat : Ghat := Classical.choose exists_not_mem_GB

theorem sigmaHat_not_mem : sigmaHat ∉ GB :=
  Classical.choose_spec exists_not_mem_GB

theorem sigmaHat_rootOmega : sigmaHat rootOmega = -rootOmega := by
  rcases apply_rootOmega sigmaHat with h | h
  · exact absurd ((mem_GB_iff _).2 h) sigmaHat_not_mem
  · exact h

theorem sigmaHat_baseRoot : (sigmaHat rootOmega : Closure) = -baseRoot := by
  rw [sigmaHat_rootOmega]
  rfl

theorem not_mem_GB_iff (g : Ghat) : g ∉ GB ↔ g rootOmega = -rootOmega := by
  rw [mem_GB_iff]
  constructor
  · intro h
    exact (apply_rootOmega g).resolve_left h
  · intro h h'
    rw [h'] at h
    have h2 : (2 : Omega) * rootOmega = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact two_ne_zero h3
    · apply sqrt241_ne_zero
      apply Subtype.ext
      exact congrArg (fun y : Omega ↦ (y : Closure)) h3

theorem sigmaHat_sq_mem : sigmaHat ^ 2 ∈ GB := by
  rw [mem_GB_iff, pow_two, AlgEquiv.mul_apply, sigmaHat_rootOmega, map_neg,
    sigmaHat_rootOmega, neg_neg]

theorem conj_sigmaHat_mem {g : Ghat} (hg : g ∈ GB) : sigmaHat * g * sigmaHat⁻¹ ∈ GB :=
  GB_normal.conj_mem g hg sigmaHat

/-! ### The bridge `Gal(Ω_B/B) ≃ₜ* G_B` -/

/-- `chi` restricted to `Ω ≃+* Ω_B`. -/
def omegaEquiv : Omega ≃+* OmegaB where
  toFun x := ⟨chi x, (mem_Omega_iff x).1 x.2⟩
  invFun y := ⟨chi.symm y, (mem_Omega_iff _).2 (by rw [AlgEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (chi.symm_apply_apply (x : Closure))
  right_inv y := Subtype.ext (chi.apply_symm_apply (y : Bbar))
  map_mul' x y := Subtype.ext (map_mul chi (x : Closure) (y : Closure))
  map_add' x y := Subtype.ext (map_add chi (x : Closure) (y : Closure))

@[simp] theorem coe_omegaEquiv (x : Omega) : (omegaEquiv x : Bbar) = chi x := rfl

@[simp] theorem coe_omegaEquiv_symm (y : OmegaB) :
    (omegaEquiv.symm y : Closure) = chi.symm y :=
  rfl

theorem coe_omegaEquiv_symm_algebraMap (b : B) :
    (omegaEquiv.symm (algebraMap B OmegaB b) : Closure) = b :=
  chi_symm_algebraMap b

theorem omegaEquiv_symm_algebraMap_mem (b : B) :
    omegaEquiv.symm (algebraMap B OmegaB b) ∈ BinOmega := by
  rw [mem_BinOmega_iff, coe_omegaEquiv_symm_algebraMap]
  exact b.2

theorem omegaEquiv_rootOmega : omegaEquiv rootOmega = algebraMap B OmegaB sqrt241 :=
  Subtype.ext (chi_coe sqrt241)

/-- The underlying map of the bridge: `g ↦ chi⁻¹ ∘ g ∘ chi` on `Ω`. -/
def bridgeFun (g : GBw) : Ghat :=
  (omegaEquiv.trans (g.toRingEquiv.trans omegaEquiv.symm)).toRatAlgEquiv

theorem bridgeFun_apply (g : GBw) (x : Omega) :
    bridgeFun g x = omegaEquiv.symm (g (omegaEquiv x)) :=
  rfl

theorem bridgeFun_mem (g : GBw) : bridgeFun g ∈ GB := by
  rw [mem_GB_iff, bridgeFun_apply, omegaEquiv_rootOmega, AlgEquiv.commutes]
  exact Subtype.ext (coe_omegaEquiv_symm_algebraMap sqrt241)

/-- The bridge as a group homomorphism `Gal(Ω_B/B) →* G_B`. -/
def bridgeHom : GBw →* GB where
  toFun g := ⟨bridgeFun g, bridgeFun_mem g⟩
  map_one' := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    change omegaEquiv.symm (omegaEquiv x) = x
    rw [RingEquiv.symm_apply_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    change omegaEquiv.symm ((g * h) (omegaEquiv x)) =
      omegaEquiv.symm (g (omegaEquiv (omegaEquiv.symm (h (omegaEquiv x)))))
    rw [RingEquiv.apply_symm_apply, AlgEquiv.mul_apply]

theorem bridgeHom_apply (g : GBw) (x : Omega) :
    (bridgeHom g : Ghat) x = omegaEquiv.symm (g (omegaEquiv x)) :=
  rfl

theorem fixes_BinOmega (h : GB) (x : Omega) (hx : x ∈ BinOmega) : (h : Ghat) x = x :=
  (IntermediateField.mem_fixingSubgroup_iff BinOmega (h : Ghat)).1 h.2 x hx

/-- The inverse of the bridge: an element of `G_B` acts `B`-linearly on `Ω_B`. -/
def bridgeInvFun (h : GB) : GBw :=
  AlgEquiv.ofRingEquiv (f := omegaEquiv.symm.trans ((h : Ghat).toRingEquiv.trans omegaEquiv))
    (fun b ↦ by
      change omegaEquiv ((h : Ghat) (omegaEquiv.symm (algebraMap B OmegaB b))) =
        algebraMap B OmegaB b
      rw [fixes_BinOmega h _ (omegaEquiv_symm_algebraMap_mem b), RingEquiv.apply_symm_apply])

theorem bridgeInvFun_apply (h : GB) (y : OmegaB) :
    bridgeInvFun h y = omegaEquiv ((h : Ghat) (omegaEquiv.symm y)) :=
  rfl

theorem bridgeInvFun_bridgeHom (g : GBw) : bridgeInvFun (bridgeHom g) = g := by
  ext y
  rw [bridgeInvFun_apply, bridgeHom_apply, RingEquiv.apply_symm_apply,
    RingEquiv.apply_symm_apply]

theorem bridgeHom_bridgeInvFun (h : GB) : bridgeHom (bridgeInvFun h) = h := by
  ext x
  rw [bridgeHom_apply, bridgeInvFun_apply, RingEquiv.symm_apply_apply,
    RingEquiv.symm_apply_apply]

theorem bridgeHom_bijective : Function.Bijective bridgeHom :=
  ⟨Function.LeftInverse.injective bridgeInvFun_bridgeHom,
    Function.RightInverse.surjective bridgeHom_bridgeInvFun⟩

/-- An automorphism fixing a generator fixes the simple extension. -/
theorem mem_fixingSubgroup_adjoin_simple {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) {a : L} (h : σ a = a) : σ ∈ (IntermediateField.adjoin K {a}).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have key : (σ : L →ₐ[K] L).comp (IntermediateField.adjoin K {a}).val =
      (IntermediateField.adjoin K {a}).val := by
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h
  exact congrArg (fun φ : IntermediateField.adjoin K {a} →ₐ[K] L ↦ φ ⟨x, hx⟩) key

theorem bridgeHom_continuous : Continuous (fun g : GBw ↦ (bridgeHom g : Ghat)) := by
  let φ : GBw →* Ghat := GB.subtype.comp bridgeHom
  change Continuous φ
  refine continuous_of_continuousAt_one φ ?_
  rw [ContinuousAt, map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff ℚ Omega s).1 hs
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  have haE : E = IntermediateField.adjoin ℚ {(α : Omega)} := by
    have h := IntermediateField.lift_adjoin_simple ℚ E α
    rw [hα, IntermediateField.lift_top] at h
    exact h
  let E' : IntermediateField B OmegaB := IntermediateField.adjoin B {omegaEquiv α}
  have hint : IsIntegral B (omegaEquiv α) := Algebra.IsIntegral.isIntegral _
  have hE' : FiniteDimensional B E' := IntermediateField.adjoin.finiteDimensional hint
  refine (krullTopology_mem_nhds_one_iff B OmegaB (φ ⁻¹' s)).2 ⟨E', hE', ?_⟩
  intro g hg
  apply hEs
  have hga : g (omegaEquiv α) = omegaEquiv α :=
    (IntermediateField.mem_fixingSubgroup_iff E' g).1 hg _
      (IntermediateField.mem_adjoin_simple_self B _)
  have hfix : φ g (α : Omega) = α := by
    change omegaEquiv.symm (g (omegaEquiv α)) = α
    rw [hga, RingEquiv.symm_apply_apply]
  change φ g ∈ E.fixingSubgroup
  rw [haE]
  exact mem_fixingSubgroup_adjoin_simple (φ g) hfix

instance GB_compactSpace : CompactSpace GB :=
  isCompact_iff_compactSpace.mp GB_isClosed.isCompact

/-- The bridge `Gal(Ω_B/B) ≃ₜ* G_B`. -/
def bridge : GBw ≃ₜ* GB :=
  ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2 bridgeHom
    (continuous_induced_rng.2 bridgeHom_continuous) bridgeHom_bijective

theorem bridge_apply (g : GBw) (x : Omega) :
    (bridge g : Ghat) x = omegaEquiv.symm (g (omegaEquiv x)) :=
  rfl

theorem bridge_symm_apply (h : GB) (y : OmegaB) :
    bridge.symm h y = omegaEquiv ((h : Ghat) (omegaEquiv.symm y)) := by
  have : bridge.symm h = bridgeInvFun h := by
    apply bridge.injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact (bridgeHom_bridgeInvFun h).symm
  rw [this]
  rfl

/-! ### Pro-2 bases -/

open ProCGroups ProCGroups.ProC in
/-- `G_B` is pro-2 (through the bridge). -/
theorem GB_hasPGroupOpenNormalBasis : HasPGroupOpenNormalBasis 2 GB :=
  HasOpenNormalBasisInClass.ofContinuousMulEquiv OmegaB_hasPGroupOpenNormalBasis bridge

open ProCGroups ProCGroups.ProC in
/-- `Ĝ` is pro-2: `G_B` is a closed normal pro-2 subgroup of index 2. -/
theorem Ghat_hasPGroupOpenNormalBasis : HasPGroupOpenNormalBasis 2 Ghat := by
  have : GB.FiniteIndex := ⟨by rw [GB_index]; norm_num⟩
  have hfin : Finite (Ghat ⧸ GB) :=
    Subgroup.finite_quotient_of_finiteIndex (H := GB)
  have hcard : Nat.card (Ghat ⧸ GB) = 2 ^ 1 := by
    rw [← Subgroup.index_eq_card, GB_index, pow_one]
  have h2 : IsPGroup 2 (Ghat ⧸ GB) := IsPGroup.of_card hcard
  have : DiscreteTopology (Ghat ⧸ GB) := QuotientGroup.discreteTopology GB_isOpen
  have hQ : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup 2) (Ghat ⧸ GB) := by
    apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
    intro U
    exact ⟨inferInstance, h2.to_quotient _⟩
  exact HasOpenNormalBasisInClass.extension (FiniteGroupClass.pGroup_formation 2).isomClosed
    (FiniteGroupClass.pGroup_formation 2).quotientClosed
    (FiniteGroupClass.pGroup_extensionClosed 2) GB GB_isClosed
    GB_hasPGroupOpenNormalBasis hQ

/-! ### Maximality in the ℚ-world -/

/-- Finite subextensions of `Closure/B` are number fields. -/
local instance numberFieldOfFiniteB (K : IntermediateField B Closure) [FiniteDimensional B K] :
    NumberField K :=
  NumberField.of_module_finite B K

/-- A finite Galois 2-extension `K/B` inside the closure, unramified outside `S`,
lies in `chi⁻¹(Ω_B)`. -/
theorem le_OmegaBcl_of_admissible (K : IntermediateField B Closure) [FiniteDimensional B K]
    [IsGalois B K] (h2 : IsPGroup 2 (K ≃ₐ[B] K))
    (hS : IsUnramifiedAtFinitePlacesOutside B K S) : K ≤ OmegaBcl := by
  let e : K ≃ₐ[B] K.map (chi : Closure →ₐ[B] Bbar) :=
    IntermediateField.equivMap K (chi : Closure →ₐ[B] Bbar)
  have : FiniteDimensional B (K.map (chi : Closure →ₐ[B] Bbar)) :=
    e.toLinearEquiv.finiteDimensional
  have : IsGalois B (K.map (chi : Closure →ₐ[B] Bbar)) := IsGalois.of_algEquiv e
  have : NumberField (K.map (chi : Closure →ₐ[B] Bbar)) := NumberField.of_module_finite B _
  let EF : FiniteGaloisIntermediateField B Bbar :=
    { toIntermediateField := K.map (chi : Closure →ₐ[B] Bbar) }
  have hadm : ProP.IsAdmissibleFiniteLayer B 2 S EF :=
    ⟨h2.of_equiv (AlgEquiv.autCongr e), IsUnramifiedAtFinitePlacesOutside.congrTop e hS⟩
  have hle := (finiteLayer_le_OmegaB_iff EF).2 hadm
  intro x hx
  rw [mem_OmegaBcl_iff]
  exact hle ⟨x, hx, rfl⟩

/-- The identity map `K ≃+* IntermediateField.extendScalars hB`. -/
def extendScalarsRingEquiv (K : IntermediateField ℚ Closure) (hB : B ≤ K) :
    K ≃+* IntermediateField.extendScalars hB where
  toFun x := ⟨x, x.2⟩
  invFun y := ⟨y, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

instance finiteDimensional_extendScalars {K : IntermediateField ℚ Closure}
    [FiniteDimensional ℚ K] (hB : B ≤ K) :
    FiniteDimensional ℚ (IntermediateField.extendScalars hB) :=
  (extendScalarsRingEquiv K hB).toRatAlgEquiv.toLinearEquiv.finiteDimensional

instance numberField_extendScalars {K : IntermediateField ℚ Closure}
    [FiniteDimensional ℚ K] (hB : B ≤ K) : NumberField (IntermediateField.extendScalars hB) :=
  NumberField.of_module_finite ℚ _

/-- Maximality of `Ω` in the ℚ-world form: a finite Galois 2-extension `K/ℚ`
inside the closure, containing `B` and unramified over `B` outside `S`, lies
in `Ω`. -/
theorem le_Omega_of_admissible (K : IntermediateField ℚ Closure) [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (hB : B ≤ K) (h2 : IsPGroup 2 (K ≃ₐ[ℚ] K))
    (hS : IsUnramifiedAtFinitePlacesOutside B (IntermediateField.extendScalars hB) S) : K ≤ Omega := by
  let ι := extendScalarsRingEquiv K hB
  have : FiniteDimensional B (IntermediateField.extendScalars hB) :=
    Module.Finite.of_restrictScalars_finite ℚ B (IntermediateField.extendScalars hB)
  have : IsGalois ℚ (IntermediateField.extendScalars hB) := IsGalois.of_algEquiv ι.toRatAlgEquiv
  have : IsGalois B (IntermediateField.extendScalars hB) := IsGalois.tower_top_of_isGalois ℚ B _
  let φ : ((IntermediateField.extendScalars hB) ≃ₐ[B] (IntermediateField.extendScalars hB)) →* (K ≃ₐ[ℚ] K) :=
    { toFun := fun g ↦ (ι.trans (g.toRingEquiv.trans ι.symm)).toRatAlgEquiv
      map_one' := by
        ext x
        rfl
      map_mul' := fun g h ↦ by
        ext x
        rfl }
  have hφ : Function.Injective φ := by
    intro g h hgh
    ext y
    have := congrArg (fun f : K ≃ₐ[ℚ] K ↦ ((f (ι.symm y) : K) : Closure)) hgh
    exact this
  have h2' : IsPGroup 2 ((IntermediateField.extendScalars hB) ≃ₐ[B] (IntermediateField.extendScalars hB)) :=
    h2.of_injective φ hφ
  exact le_OmegaBcl_of_admissible (IntermediateField.extendScalars hB) h2' hS

end UnitDistance.Sqrt241.Tower
