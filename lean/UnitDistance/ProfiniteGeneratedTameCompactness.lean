module

public import UnitDistance.ProfiniteTameCompactness
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! Compactness preserves both the tame equation and actual generation
in every finite quotient. No compatible choice of finite witnesses is assumed. -/
noncomputable section
namespace UnitDistance.ProfiniteTame
open Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable {I D : Type*} [Group I] [TopologicalSpace I] [CompactSpace I]
  [Group D] [TopologicalSpace D] [CompactSpace D]

/-- The displayed pair generates the inertia and decomposition images in a quotient. -/
def quotientGenerates (i : I →ₜ* G) (d : D →ₜ* G)
    (U : OpenNormalSubgroup G) (τ φ : G) : Prop :=
  (∀ x : I, ∃ n : ℤ, QuotientGroup.mk' (U : Subgroup G) (i x) =
    QuotientGroup.mk' (U : Subgroup G) τ ^ n) ∧
  (∀ y : D, QuotientGroup.mk' (U : Subgroup G) (d y) ∈
    Subgroup.closure ({QuotientGroup.mk' (U : Subgroup G) τ,
      QuotientGroup.mk' (U : Subgroup G) φ} : Set (G ⧸ (U : Subgroup G))))

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [CompactSpace I] [CompactSpace D] in
/-- Quotient generation descends along every larger open normal subgroup. -/
theorem quotientGenerates_mono (i : I →ₜ* G) (d : D →ₜ* G)
    {U V : OpenNormalSubgroup G} (hUV : U ≤ V) {τ φ : G}
    (h : quotientGenerates i d U τ φ) : quotientGenerates i d V τ φ := by
  let f : G ⧸ (U : Subgroup G) →* G ⧸ (V : Subgroup G) :=
    QuotientGroup.map (U : Subgroup G) (V : Subgroup G) (MonoidHom.id G) hUV
  have hf (g : G) : f (QuotientGroup.mk' (U : Subgroup G) g) =
      QuotientGroup.mk' (V : Subgroup G) g := rfl
  refine ⟨?_,?_⟩
  · intro x
    obtain ⟨n,hn⟩ := h.1 x
    refine ⟨n,?_⟩
    have hh := congrArg f hn
    simpa only [map_zpow,hf] using hh
  · let C : Subgroup (G ⧸ (V : Subgroup G)) :=
      Subgroup.closure {QuotientGroup.mk' (V : Subgroup G) τ,
        QuotientGroup.mk' (V : Subgroup G) φ}
    have hmap : Subgroup.closure
        ({QuotientGroup.mk' (U : Subgroup G) τ,
          QuotientGroup.mk' (U : Subgroup G) φ} : Set (G ⧸ (U : Subgroup G))) ≤
        C.comap f := by
      apply (Subgroup.closure_le _).mpr
      intro z hz
      rcases hz with (rfl | rfl)
      · change f (QuotientGroup.mk' (U : Subgroup G) τ) ∈ C
        rw [hf]
        exact Subgroup.subset_closure (by simp)
      · change f (QuotientGroup.mk' (U : Subgroup G) φ) ∈ C
        rw [hf]
        exact Subgroup.subset_closure (by simp)
    intro y
    exact hmap (h.2 y)

omit [CompactSpace G] [TotallyDisconnectedSpace G] [CompactSpace I] [CompactSpace D] in
/-- For a fixed finite quotient, the generation condition is closed on the compact pair space. -/
theorem isClosed_quotientGenerates (i : I →ₜ* G) (d : D →ₜ* G)
    (U : OpenNormalSubgroup G) :
    IsClosed {p : I × D | quotientGenerates i d U (i p.1) (d p.2)} := by
  let B : Set ((G ⧸ (U : Subgroup G)) × (G ⧸ (U : Subgroup G))) :=
    {p | (∀ x : I, ∃ n : ℤ, QuotientGroup.mk' (U : Subgroup G) (i x) = p.1 ^ n) ∧
      (∀ y : D, QuotientGroup.mk' (U : Subgroup G) (d y) ∈
        Subgroup.closure ({p.1,p.2} : Set (G ⧸ (U : Subgroup G))))}
  have hc : Continuous (fun p : I × D =>
      (QuotientGroup.mk' (U : Subgroup G) (i p.1),
        QuotientGroup.mk' (U : Subgroup G) (d p.2))) := by
    have hq : Continuous (QuotientGroup.mk' (U : Subgroup G)) := QuotientGroup.continuous_mk
    exact (hq.comp (i.continuous.comp continuous_fst)).prodMk
      (hq.comp (d.continuous.comp continuous_snd))
  exact (isClosed_discrete B).preimage hc

/-- One pair simultaneously satisfies the labels, literal tame relation,
and both generation conditions in every finite quotient. -/
theorem exists_generated_tame_pair {A : Type*} [TopologicalSpace A] [T2Space A]
    (i : I →ₜ* G) (d : D →ₜ* G) (χ : G → A) (hχ : Continuous χ)
    (a b : A) (q : ℕ)
    (h : ∀ U : OpenNormalSubgroup G, ∃ t : I, ∃ s : D,
      χ (i t) = a ∧ χ (d s) = b ∧
      d s * i t * (d s)⁻¹ * (i t ^ q)⁻¹ ∈ U ∧
      quotientGenerates i d U (i t) (d s)) :
    ∃ t : I, ∃ s : D, χ (i t) = a ∧ χ (d s) = b ∧
      d s * i t * (d s)⁻¹ = i t ^ q ∧
      ∀ U : OpenNormalSubgroup G, quotientGenerates i d U (i t) (d s) := by
  let f : I × D → G := fun p => d p.2 * i p.1 * (d p.2)⁻¹ * (i p.1 ^ q)⁻¹
  have hf : Continuous f := by fun_prop
  let c : I × D → A × A := fun p => (χ (i p.1),χ (d p.2))
  have hc : Continuous c := by fun_prop
  let C : OpenNormalSubgroup G → Set (I × D) := fun U =>
    {p | c p = (a,b) ∧ f p ∈ U ∧ quotientGenerates i d U (i p.1) (d p.2)}
  have hclosed (U : OpenNormalSubgroup G) : IsClosed (C U) :=
    (isClosed_eq hc continuous_const).inter
      ((U.toOpenSubgroup.isClosed.preimage hf).inter (isClosed_quotientGenerates i d U))
  have hnonempty (U : OpenNormalSubgroup G) : (C U).Nonempty := by
    obtain ⟨t,s,ht,hs,hrel,hgen⟩ := h U
    exact ⟨(t,s),Prod.ext ht hs,hrel,hgen⟩
  have hdir : Directed (· ⊇ ·) C := by
    intro U V
    refine ⟨U ⊓ V,?_,?_⟩
    · intro p hp
      exact ⟨hp.1,hp.2.1.1,quotientGenerates_mono i d inf_le_left hp.2.2⟩
    · intro p hp
      exact ⟨hp.1,hp.2.1.2,quotientGenerates_mono i d inf_le_right hp.2.2⟩
  letI : Nonempty (OpenNormalSubgroup G) :=
    ⟨{toOpenSubgroup := ⊤,isNormal' := show (⊤ : Subgroup G).Normal from inferInstance}⟩
  obtain ⟨p,hp⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C
    hdir hnonempty (fun U => (hclosed U).isCompact) hclosed
  have hpU (U : OpenNormalSubgroup G) :
      c p = (a,b) ∧ f p ∈ U ∧ quotientGenerates i d U (i p.1) (d p.2) :=
    mem_iInter.mp hp U
  have hc' := (hpU Classical.ofNonempty).1
  have hrel : f p = 1 := eq_one_of_mem_all_openNormal (fun U => (hpU U).2.1)
  exact ⟨p.1,p.2,congrArg Prod.fst hc',congrArg Prod.snd hc',
    mul_inv_eq_one.mp hrel,fun U => (hpU U).2.2⟩

end UnitDistance.ProfiniteTame
