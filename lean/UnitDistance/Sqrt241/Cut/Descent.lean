module

public import UnitDistance.Sqrt241.Cut.Infinite

@[expose] public section
set_option backward.privateInPublic true


/-!
# Descent of the cut to a Galois group and its `σ̂`-stability

Generic statements for the passage from the free source to an ambient group
`Ĝ` (used in `Retained/Kernel.lean`; no arithmetic is assumed):

* for a continuous surjection `f` of a compact group onto a Hausdorff group,
  the image of a closed normal closure is the closed normal closure of the
  image (`map_closedNormalClosure`); if `ker f ≤ K`, then `(K.map f).comap f = K`
  and the quotients are isomorphic, so infinitude descends (`infinite_map`);
* inside `Ĝ`, with `f` landing onto a normal subgroup `H` (e.g. `G_B`), the
  image `K̂` of a closed normal closure is stable under conjugation by `σ` as
  soon as the `σ`-conjugates of the generators lie in `K̂`
  (`conj_mem_map_of_generators`); if moreover every element of `Ĝ` lies in
  `H ∪ σH`, then `K̂` is normal in `Ĝ` (`normal_of_conj`);
* for the thirty literal cut words: exact `σ`-conjugacy of the first- and
  second-prime lifts, `σ² ∈ H` and `σ F₇⁻¹ ∈ H` (with `F₇² = f(cap 2)`) give
  the generator condition (`SourceLifts.sigma_conj_words`), using that `y₁²` lies in
  the cut kernel by the presentation hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.Cut
open ProCGroups ProCGroups.Presentations GroupData

section Generic
variable {G Γ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]

omit [IsTopologicalGroup G] [IsTopologicalGroup Γ] in
theorem isClosed_map (f : G →ₜ* Γ) (K : Subgroup G) (hK : IsClosed (K : Set G)) :
    IsClosed ((K.map f.toMonoidHom : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.coe_map]
  exact (hK.isCompact.image f.continuous).isClosed

/-- The image of a closed normal closure under a continuous surjection. -/
theorem map_closedNormalClosure (f : G →ₜ* Γ) (hf : Function.Surjective f) (S : Set G) :
    (closedNormalClosure S).map f.toMonoidHom = closedNormalClosure (f '' S) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    have hN : ((closedNormalClosure (f '' S)).comap f.toMonoidHom).Normal :=
      Subgroup.Normal.comap inferInstance _
    apply closedNormalClosure_le_closed_normal
      ((closedNormalClosure_isClosed _).preimage f.continuous)
    intro s hs
    exact subset_closedNormalClosure _ ⟨s,hs,rfl⟩
  · have hN : ((closedNormalClosure S).map f.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ hf
    apply closedNormalClosure_le_closed_normal
      (isClosed_map f _ (closedNormalClosure_isClosed S))
    rintro _ ⟨s,hs,rfl⟩
    exact ⟨s,subset_closedNormalClosure _ hs,rfl⟩

end Generic

section Algebraic
variable {G Γ : Type*} [Group G] [Group Γ]

/-- The image lies in `H` when `f` does. -/
theorem map_le_of_mem (f : G →* Γ) (H : Subgroup Γ) (hfH : ∀ g, f g ∈ H) (K : Subgroup G) :
    K.map f ≤ H := by
  rintro _ ⟨g,_,rfl⟩
  exact hfH g

theorem comap_map_of_ker_le (f : G →* Γ) (K : Subgroup G) (h : f.ker ≤ K) :
    (K.map f).comap f = K := by
  rw [Subgroup.comap_map_eq,sup_eq_left.mpr h]

/-- Infinitude descends along a surjection whose kernel lies in `K`. -/
theorem infinite_map (f : G →* Γ) (hf : Function.Surjective f) (K : Subgroup G) [K.Normal]
    (h : f.ker ≤ K) [hinf : Infinite (G ⧸ K)] : Infinite (Γ ⧸ K.map f) := by
  have hN : (K.map f).Normal := Subgroup.Normal.map inferInstance f hf
  let φ : G →* Γ ⧸ K.map f := (QuotientGroup.mk' (K.map f)).comp f
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective (K.map f)).comp hf
  have hker : φ.ker = K := by
    ext g
    change QuotientGroup.mk' (K.map f) (f g) = 1 ↔ g ∈ K
    rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
    change g ∈ (K.map f).comap f ↔ g ∈ K
    rw [comap_map_of_ker_le f K h]
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have hinf' : Infinite (G ⧸ φ.ker) := by rw [hker]; exact hinf
  exact Infinite.of_injective e e.injective

/-- A subgroup normalized by `H` and by `σ` is normal when `G = H ∪ σH`. -/
theorem normal_of_conj (H K : Subgroup G)
    (hHnorm : ∀ h ∈ H, ∀ x ∈ K, h*x*h⁻¹ ∈ K) (σ : G)
    (hσ : ∀ x ∈ K, σ*x*σ⁻¹ ∈ K) (hcover : ∀ g : G, g ∈ H ∨ σ⁻¹*g ∈ H) : K.Normal := by
  constructor
  intro x hx g
  rcases hcover g with hg | hg
  · exact hHnorm g hg x hx
  · have he : g*x*g⁻¹ = σ*((σ⁻¹*g)*x*(σ⁻¹*g)⁻¹)*σ⁻¹ := by group
    rw [he]
    exact hσ _ (hHnorm _ hg x hx)

end Algebraic

section Ambient
variable {Ĝ : Type*} [Group Ĝ] [TopologicalSpace Ĝ] [IsTopologicalGroup Ĝ] [T2Space Ĝ]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- The image of a closed normal closure is stable under conjugation by `σ`
when the conjugates of the generators are, provided the map is onto a normal
subgroup `H` of `Ĝ`. -/
theorem conj_mem_map_of_generators (H : Subgroup Ĝ) [H.Normal] (f : G →ₜ* Ĝ)
    (hfH : ∀ g, f g ∈ H) (honto : ∀ h ∈ H, ∃ g, f g = h) (S : Set G) (σ : Ĝ)
    (hS : ∀ s ∈ S, σ*f s*σ⁻¹ ∈ (closedNormalClosure S).map f.toMonoidHom)
    (k : Ĝ) (hk : k ∈ (closedNormalClosure S).map f.toMonoidHom) :
    σ*k*σ⁻¹ ∈ (closedNormalClosure S).map f.toMonoidHom := by
  set K := (closedNormalClosure S).map f.toMonoidHom with hKdef
  have hKclosed : IsClosed (K : Set Ĝ) := isClosed_map f _ (closedNormalClosure_isClosed S)
  have hHnorm : ∀ h ∈ H, ∀ x ∈ K, h*x*h⁻¹ ∈ K := by
    intro h hh x hx
    obtain ⟨g,rfl⟩ := honto h hh
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨g*y*g⁻¹,(closedNormalClosure_normal S).conj_mem y hy g,by simp [map_mul,map_inv]⟩
  let M : Subgroup G :=
    { carrier := {g | σ*f g*σ⁻¹ ∈ K}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change σ*f (a*b)*σ⁻¹ ∈ K
        have he : σ*f (a*b)*σ⁻¹ = (σ*f a*σ⁻¹)*(σ*f b*σ⁻¹) := by simp [map_mul,mul_assoc]
        rw [he]
        exact K.mul_mem ha hb
      inv_mem' := by
        intro a ha
        change σ*f a⁻¹*σ⁻¹ ∈ K
        have he : σ*f a⁻¹*σ⁻¹ = (σ*f a*σ⁻¹)⁻¹ := by simp [map_inv,mul_assoc]
        rw [he]
        exact K.inv_mem ha }
  have hMnormal : M.Normal := by
    constructor
    intro m hm t
    change σ*f (t*m*t⁻¹)*σ⁻¹ ∈ K
    have he : σ*f (t*m*t⁻¹)*σ⁻¹ =
        (σ*f t*σ⁻¹)*(σ*f m*σ⁻¹)*(σ*f t*σ⁻¹)⁻¹ := by
      simp [map_mul,map_inv,mul_assoc]
    rw [he]
    exact hHnorm _ ((inferInstance : H.Normal).conj_mem _ (hfH t) σ) _ hm
  have hMclosed : IsClosed (M : Set G) := by
    have hc : Continuous fun g : G => σ*f g*σ⁻¹ :=
      (continuous_const.mul f.continuous).mul continuous_const
    exact hKclosed.preimage hc
  have hle : closedNormalClosure S ≤ M :=
    closedNormalClosure_le_closed_normal hMclosed (fun s hs => hS s hs)
  obtain ⟨g,hg,rfl⟩ := hk
  exact hle hg

end Ambient

namespace SourceLifts
variable (A : SourceLifts)

/-- `y₁²` lies in the cut kernel (it is not a word): the local model presents
`D` with the genuine relation, and `y² = 1` in `D`. -/
theorem dyadicY_zero_sq_mem_kernel (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) : A.lifts.dyadicY 0^2 ∈ A.kernel := by
  let N : Subgroup LocalSource := A.kernel.comap (A.dyadic 0).toMonoidHom
  have hN : IsClosed (N : Set LocalSource) :=
    A.kernel_isClosed.preimage (A.dyadic 0).continuous
  have hpres := Dyadic.ArithmeticPresentation.arithmetic_presentation r hr
  have hle : (Dyadic.ArithmeticPresentation.relationKernel : Subgroup LocalSource) ≤ N := by
    rw [← hpres]
    apply closedNormalClosure_le_closed_normal hN
    intro g hg
    rcases hg with hg | hg
    · rw [hg]
      exact A.genuine_one_mem_kernel r hr hgen
    · exact A.dyadic_cut_mem_kernel 0 g hg
  have hy : Dyadic.ArithmeticPresentation.y^2 ∈
      (Dyadic.ArithmeticPresentation.relationKernel : Subgroup LocalSource) := by
    change Dyadic.ArithmeticPresentation.model (Dyadic.ArithmeticPresentation.y^2) = 1
    rw [map_pow,Dyadic.ArithmeticPresentation.model_y,Dyadic.D.y_sq]
  have h := hle hy
  change A.dyadic 0 (Dyadic.ArithmeticPresentation.y^2) ∈ A.kernel at h
  rwa [map_pow] at h

end SourceLifts
end UnitDistance.Sqrt241.Cut

namespace UnitDistance.Sqrt241.Cut
open ProCGroups ProCGroups.Presentations GroupData
open Dyadic.Presentation (literalRelations)

namespace SourceLifts
variable (A : SourceLifts)
variable {Ĝ : Type*} [Group Ĝ] [TopologicalSpace Ĝ] [IsTopologicalGroup Ĝ] [T2Space Ĝ]

/-- Hypotheses of `σ`-stability for a map of the free source into `Ĝ`: at each
pair of primes of `B` the second-prime lifts are conjugate to the first-prime
lifts by an element `s ∈ Hσ` (for the normalized local maps of `Local/Maps.lean`, `s = σ̂`
or `σ̂⁻¹`), the Frobenius at the inert `7` is a square root of the third cap with
`σ F₇⁻¹ ∈ H`, and `σ² ∈ H`. -/
structure SigmaStable (H : Subgroup Ĝ) (f : Source →ₜ* Ĝ) (σ : Ĝ) : Prop where
  sq_mem : σ^2 ∈ H
  conj : ∃ s, s*σ⁻¹ ∈ H ∧ f (A.conj 1) = MulAut.conj s (f (A.conj 0))
  tame_q : ∃ s, s*σ⁻¹ ∈ H ∧ f (A.tameInertia 1) = MulAut.conj s (f (A.tameInertia 0)) ∧
    f (A.tameFrobenius 1) = MulAut.conj s (f (A.tameFrobenius 0))
  tame_r : ∃ s, s*σ⁻¹ ∈ H ∧ f (A.tameInertia 3) = MulAut.conj s (f (A.tameInertia 2)) ∧
    f (A.tameFrobenius 3) = MulAut.conj s (f (A.tameFrobenius 2))
  dyadic : ∃ s, s*σ⁻¹ ∈ H ∧ ∀ g, f (A.dyadic 1 g) = MulAut.conj s (f (A.dyadic 0 g))
  cap : ∃ s, s*σ⁻¹ ∈ H ∧ f (A.cap 1) = MulAut.conj s (f (A.cap 0))
  frob7 : ∃ F : Ĝ, f (A.cap 2) = F^2 ∧ σ*F⁻¹ ∈ H

variable (H : Subgroup Ĝ) [H.Normal] (f : Source →ₜ* Ĝ)
  (hfH : ∀ g, f g ∈ H) (honto : ∀ h ∈ H, ∃ g, f g = h)

omit [IsTopologicalGroup Ĝ] [T2Space Ĝ] [H.Normal] in
include honto in
theorem kernelHat_conj_H (h : Ĝ) (hh : h ∈ H) (x : Ĝ) (hx : x ∈ A.kernel.map f.toMonoidHom) :
    h*x*h⁻¹ ∈ A.kernel.map f.toMonoidHom := by
  obtain ⟨g,rfl⟩ := honto h hh
  obtain ⟨y,hy,rfl⟩ := hx
  exact ⟨g*y*g⁻¹,(A.kernel_normal).conj_mem y hy g,by simp [map_mul,map_inv]⟩

omit [IsTopologicalGroup Ĝ] [T2Space Ĝ] in
include honto in
/-- A pair of kernel elements related by conjugation by `s ∈ Hσ`: both
`σ`-conjugates lie in the image of the kernel. -/
theorem pair_conj_mem (σ : Ĝ) (hσ2 : σ^2 ∈ H) (s : Ĝ) (hs : s*σ⁻¹ ∈ H) (a b : Source)
    (ha : a ∈ A.kernel) (hb : b ∈ A.kernel) (hab : f b = MulAut.conj s (f a)) :
    MulAut.conj σ (f a) ∈ A.kernel.map f.toMonoidHom ∧
      MulAut.conj σ (f b) ∈ A.kernel.map f.toMonoidHom := by
  constructor
  · have he : MulAut.conj σ (f a) = (s*σ⁻¹)⁻¹*f b*((s*σ⁻¹)⁻¹)⁻¹ := by
      rw [hab,MulAut.conj_apply,MulAut.conj_apply]
      group
    rw [he]
    exact A.kernelHat_conj_H H f honto _ (H.inv_mem hs) _ ⟨b,hb,rfl⟩
  · have hσs : σ*s ∈ H := by
      have he : σ*s = (σ*(s*σ⁻¹)*σ⁻¹)*σ^2 := by rw [pow_two]; group
      rw [he]
      exact H.mul_mem ((inferInstance : H.Normal).conj_mem _ hs σ) hσ2
    have he : MulAut.conj σ (f b) = (σ*s)*f a*(σ*s)⁻¹ := by
      rw [hab,MulAut.conj_apply,MulAut.conj_apply]
      group
    rw [he]
    exact A.kernelHat_conj_H H f honto _ hσs _ ⟨a,ha,rfl⟩

omit [IsTopologicalGroup Ĝ] [T2Space Ĝ] in
include honto in
/-- The `σ`-conjugates of the images of the thirty cut words lie in the image
of the cut kernel. -/
theorem sigma_conj_words (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) (σ : Ĝ) (hσ : A.SigmaStable H f σ) (s : Source)
    (hs : s ∈ A.lifts.words) : σ*f s*σ⁻¹ ∈ A.kernel.map f.toMonoidHom := by
  rw [← MulAut.conj_apply]
  have P := A.pair_conj_mem H f honto σ hσ.sq_mem
  have hq (i : Fin 21) := A.quadratic_mem_kernel i
  have hd (i : Fin 7) := A.deep_mem_kernel i
  obtain ⟨sc,hsc,hc⟩ := hσ.conj
  obtain ⟨sq,hsq,hqi,hqf⟩ := hσ.tame_q
  obtain ⟨sr,hsr,hri,hrf⟩ := hσ.tame_r
  obtain ⟨sd,hsd,hdy⟩ := hσ.dyadic
  obtain ⟨sk,hsk,hk⟩ := hσ.cap
  -- the dyadic pairs
  have hdyp (i : Fin 7) := P sd hsd (A.dyadic 0 (Dyadic.ArithmeticPresentation.relations i))
    (A.dyadic 1 (Dyadic.ArithmeticPresentation.relations i))
    (by
      by_cases hi : i = 1
      · subst hi
        have h := A.dyadicY_zero_sq_mem_kernel r hr hgen
        rw [dyadic_literal]
        exact h
      · exact A.dyadic_cut_mem_kernel 0 _ ⟨i,hi,rfl⟩)
    (by rw [dyadic_literal]; exact A.word_mem_kernel (A.literal_mem_words 1 i (Or.inl rfl)))
    (hdy _)
  have hdy0 (i : Fin 7) : MulAut.conj σ (f (literalRelations (A.lifts.dyadicX 0)
      (A.lifts.dyadicY 0) (A.lifts.dyadicZ 0) i)) ∈ A.kernel.map f.toMonoidHom := by
    rw [← dyadic_literal]; exact (hdyp i).1
  have hdy1 (i : Fin 7) : MulAut.conj σ (f (literalRelations (A.lifts.dyadicX 1)
      (A.lifts.dyadicY 1) (A.lifts.dyadicZ 1) i)) ∈ A.kernel.map f.toMonoidHom := by
    rw [← dyadic_literal]; exact (hdyp i).2
  rcases hs with (⟨i,rfl⟩ | ⟨Q,rfl⟩) | ⟨i,rfl⟩
  · fin_cases i
    · exact (P sc hsc _ _ (hq 0) (hq 1) (by
        simp [lifts,Lifts.quadraticWords,map_pow,hc])).1
    · exact (P sc hsc _ _ (hq 0) (hq 1) (by
        simp [lifts,Lifts.quadraticWords,map_pow,hc])).2
    · exact (P sq hsq _ _ (hq 2) (hq 3) (by
        simp [lifts,Lifts.quadraticWords,Lifts.tameWord,map_pow,map_mul,map_inv,
          hqi,hqf,tameNorm])).1
    · exact (P sq hsq _ _ (hq 2) (hq 3) (by
        simp [lifts,Lifts.quadraticWords,Lifts.tameWord,map_pow,map_mul,map_inv,
          hqi,hqf,tameNorm])).2
    · exact (P sr hsr _ _ (hq 4) (hq 5) (by
        simp [lifts,Lifts.quadraticWords,Lifts.tameWord,map_pow,map_mul,map_inv,
          hri,hrf,tameNorm])).1
    · exact (P sr hsr _ _ (hq 4) (hq 5) (by
        simp [lifts,Lifts.quadraticWords,Lifts.tameWord,map_pow,map_mul,map_inv,
          hri,hrf,tameNorm])).2
    · exact hdy1 1
    · exact hdy0 0
    · exact hdy0 2
    · exact hdy0 3
    · exact hdy1 0
    · exact hdy1 2
    · exact hdy1 3
    · exact (P sq hsq _ _ (hq 13) (hq 14) (by
        simp [lifts,Lifts.quadraticWords,map_pow,hqi])).1
    · exact (P sq hsq _ _ (hq 13) (hq 14) (by
        simp [lifts,Lifts.quadraticWords,map_pow,hqi])).2
    · exact (P sr hsr _ _ (hq 15) (hq 16) (by
        simp [lifts,Lifts.quadraticWords,map_pow,hri])).1
    · exact (P sr hsr _ _ (hq 15) (hq 16) (by
        simp [lifts,Lifts.quadraticWords,map_pow,hri])).2
    · exact (P sq hsq _ _ (hq 17) (hq 18) (by
        simp [lifts,Lifts.quadraticWords,map_pow,hqf])).1
    · exact (P sq hsq _ _ (hq 17) (hq 18) (by
        simp [lifts,Lifts.quadraticWords,map_pow,hqf])).2
    · exact (P sr hsr _ _ (hq 19) (hq 20) (by
        simp [lifts,Lifts.quadraticWords,map_pow,hrf])).1
    · exact (P sr hsr _ _ (hq 19) (hq 20) (by
        simp [lifts,Lifts.quadraticWords,map_pow,hrf])).2
  · fin_cases Q
    · exact hdy0 4
    · exact hdy1 4
  · fin_cases i
    · exact hdy0 5
    · exact hdy0 6
    · exact hdy1 5
    · exact hdy1 6
    · exact (P sk hsk _ _ (hd 4) (hd 5) (by
        simp [lifts,Lifts.deepWords,map_pow,hk])).1
    · exact (P sk hsk _ _ (hd 4) (hd 5) (by
        simp [lifts,Lifts.deepWords,map_pow,hk])).2
    · obtain ⟨F,hF,hσF⟩ := hσ.frob7
      have hw : f (A.lifts.deepWords 6) = F^8 := by
        change f (A.cap 2^4) = _
        rw [map_pow,hF,← pow_mul]
      change MulAut.conj σ (f (A.lifts.deepWords 6)) ∈ _
      rw [hw,MulAut.conj_apply]
      have he : σ*F^8*σ⁻¹ = (σ*F⁻¹)*F^8*(σ*F⁻¹)⁻¹ := by group
      rw [he]
      exact A.kernelHat_conj_H H f honto _ hσF _ (hw ▸ ⟨_,hd 6,rfl⟩)

include hfH honto in
/-- The image of the cut kernel is normal in `Ĝ` under the `σ`-stability
hypotheses and `Ĝ = H ∪ σH`. -/
theorem kernelHat_normal (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) (σ : Ĝ) (hσ : A.SigmaStable H f σ)
    (hcover : ∀ g : Ĝ, g ∈ H ∨ σ⁻¹*g ∈ H) : (A.kernel.map f.toMonoidHom).Normal :=
  normal_of_conj H _ (A.kernelHat_conj_H H f honto) σ
    (conj_mem_map_of_generators H f hfH honto A.lifts.words σ
      (A.sigma_conj_words H f honto r hr hgen σ hσ)) hcover

end SourceLifts
end UnitDistance.Sqrt241.Cut

namespace UnitDistance.Sqrt241.Cut
open ProCGroups ProCGroups.Presentations

namespace SourceLifts
variable (A : SourceLifts) {Γ : Type*} [Group Γ]

/-- If the kernel of `f` is presented by the seven relators, it lies in the
cut kernel. -/
theorem ker_le_kernel (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (f : Source →* Γ) (hker : f.ker ≤ closedNormalClosure (Set.range (A.relators r))) :
    f.ker ≤ A.kernel :=
  hker.trans (A.relators_closure_le_kernel r hr)

/-- If a map `p` out of `Γ` factors the cut projection through a surjection
`f : Source → Γ`, then `ker p` is the image of the cut kernel. -/
theorem ker_eq_map_of_factor {Q : Type*} [Group Q] (f : Source →* Γ)
    (hf : Function.Surjective f) (p : Γ →* Q) (φ : A.ActualQuotient →* Q)
    (hφ : Function.Injective φ) (hp : ∀ g, p (f g) = φ (A.projection g)) :
    p.ker = A.kernel.map f := by
  ext x
  obtain ⟨g,rfl⟩ := hf x
  constructor
  · intro hx
    have h1 : φ (A.projection g) = φ 1 := by rw [← hp,map_one]; exact hx
    exact ⟨g,(QuotientGroup.eq_one_iff g).mp (hφ h1),rfl⟩
  · rintro ⟨g',hg',he⟩
    change p (f g) = 1
    rw [← he,hp,A.projection_eq_one_of_mem hg',map_one]

/-- The pull-back of the image of the cut kernel is the cut kernel. -/
theorem comap_kernelHat (f : Source →* Γ) (hker : f.ker ≤ A.kernel) :
    (A.kernel.map f).comap f = A.kernel :=
  comap_map_of_ker_le f A.kernel hker

/-- The cut quotient of the free source embeds into `Γ ⧸ f(kernel)`. -/
theorem infinite_hat (hL : A.Labels) (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) (f : Source →* Γ) (hker : f.ker ≤ A.kernel)
    [(A.kernel.map f).Normal] : Infinite (Γ ⧸ A.kernel.map f) := by
  have hinf := A.infinite_of_presentation hL r hr hgen
  let φ : Source →* Γ ⧸ A.kernel.map f := (QuotientGroup.mk' (A.kernel.map f)).comp f
  have hφ : φ.ker = A.kernel := by
    ext g
    change QuotientGroup.mk' (A.kernel.map f) (f g) = 1 ↔ g ∈ A.kernel
    rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
    change g ∈ (A.kernel.map f).comap f ↔ g ∈ A.kernel
    rw [A.comap_kernelHat f hker]
  have hinf' : Infinite (Source ⧸ φ.ker) := by rw [hφ]; exact hinf
  exact Infinite.of_injective (QuotientGroup.kerLift φ) (QuotientGroup.kerLift_injective φ)

end SourceLifts
end UnitDistance.Sqrt241.Cut
