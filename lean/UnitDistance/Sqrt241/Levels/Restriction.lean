module

public import UnitDistance.Sqrt241.Levels.Family
public import UnitDistance.Sqrt241.Local.Maps
public import UnitDistance.AbsolutePrimeIndices

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Restriction to admissible fields (generic part)

For a finite Galois `K ≤ Ω` (embedded in the closure by `jK K`), the ℚ package's
absolute decomposition restriction at `p` is the restriction to `K` of
`Local.decompositionMap p` (`decompositionRestriction_eq`). For admissible `K`
(`M ≤ K`, `kernelHat ≤ Gal(Ω/K)`):

* `resB K : G_B →ₜ* Gal(K/ℚ)` kills `kernelHat`;
* equal restrictions of elements of `G_B` have equal genus labels and equal `ρ_B`-images
  (`Gal(Ω/K) ≤ core ≤ ker ρ_B`), which gives all lower bounds on local images.

Also generic group lemmas: conjugated maps have images of equal cardinality.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation Cut GroupData ProCGroups UnitDistance.PrimeCompletion

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ### Generic group lemmas -/

theorem card_range_conj {D H : Type*} [Group D] [Group H] (f g : D →* H) (x : H)
    (h : ∀ d, g d = x * f d * x⁻¹) : Nat.card g.range = Nat.card f.range := by
  have he : g = (MulAut.conj x).toMonoidHom.comp f := by
    ext d
    rw [h d]
    rfl
  rw [he, MonoidHom.range_comp, Subgroup.card_map_of_injective (MulAut.conj x).injective]

/-! ### The embedding of subfields of `Ω` and the decomposition restriction -/

/-- The embedding `K → Closure` of a subfield `K ≤ Ω`. -/
def jK (K : IntermediateField ℚ Omega) : K →ₐ[ℚ] CanonicalGenus.Closure := Omega.val.comp K.val

section Restriction

variable (K : IntermediateField ℚ Omega) [FiniteDimensional ℚ K] [IsGalois ℚ K]

instance numberField_of_le_Omega : NumberField K := NumberField.of_module_finite ℚ K

theorem decompositionRestriction_eq (p : Nat.Primes) (σ : AbsoluteDecomposition p) :
    decompositionRestriction p K (jK K) σ = Input.res K (Local.decompositionMap p σ) := by
  change GaloisEmbedding.restriction (jK K) σ.val = _
  apply GaloisEmbedding.restriction_unique
  intro x
  change (((K.val (GaloisEmbedding.restriction K.val (Local.toGhat σ.val) x)) : Omega) :
    CanonicalGenus.Closure) = σ.val (((K.val x : Omega) : CanonicalGenus.Closure))
  rw [GaloisEmbedding.restriction_commutes, Local.toGhat_apply]

theorem decompositionRestriction_eq_comp (p : Nat.Primes) :
    decompositionRestriction p K (jK K) =
      (Input.res K).toMonoidHom.comp (Local.decompositionMap p).toMonoidHom :=
  MonoidHom.ext (fun σ => decompositionRestriction_eq K p σ)

theorem inertiaRestriction_eq (p : Nat.Primes) (σ : AbsoluteInertia p) :
    inertiaRestriction p K (jK K) σ = Input.res K (Local.decompositionMap p σ.val) :=
  decompositionRestriction_eq K p σ.val

/-- `G_B → Gal(K/ℚ)`. -/
def resB : GB →ₜ* Gal(K/ℚ) :=
  (Input.res K).comp (⟨GB.subtype, continuous_subtype_val⟩ : GB →ₜ* Ghat)

theorem resB_apply (g : GB) : resB K g = Input.res K (g : Ghat) := rfl

theorem res_eq_one_iff (u : Ghat) : Input.res K u = 1 ↔ u ∈ K.fixingSubgroup := by
  rw [← GaloisQuotient.restriction_kernel K]
  rfl

end Restriction

namespace Input

variable (I : Input)

section Admissible

variable {K : IntermediateField ℚ Omega} [FiniteDimensional ℚ K] [IsGalois ℚ K]

theorem res_eq_one_of_kernelHat (hK : I.kernelHat ≤ K.fixingSubgroup) {u : Ghat}
    (hu : u ∈ I.kernelHat) : res K u = 1 :=
  (res_eq_one_iff K u).mpr (hK hu)

theorem res_eq_one_of_word (hK : I.kernelHat ≤ K.fixingSubgroup) {s : Source}
    (hs : s ∈ I.A.lifts.words) : res K ((freeMap s : GB) : Ghat) = 1 :=
  I.res_eq_one_of_kernelHat hK (I.freeMap_mem_kernelHat (I.A.word_mem_kernel hs))

theorem mem_core_of_res_eq_one (hK : K.fixingSubgroup ≤ I.core) {u : Ghat}
    (hu : res K u = 1) : u ∈ I.core :=
  hK ((res_eq_one_iff K u).mp hu)

/-- Elements of `G_B` with equal restrictions to an admissible `K` have equal `ρ_B`-images. -/
theorem retainedMap_eq_of_resB_eq (hK : K.fixingSubgroup ≤ I.core) {g h : GB}
    (he : resB K g = resB K h) : I.retainedMap g = I.retainedMap h := by
  have h1 : res K ((g : Ghat)⁻¹ * h) = 1 := by
    rw [map_mul, map_inv]
    change (resB K g)⁻¹ * resB K h = 1
    rw [he, inv_mul_cancel]
  have hc := I.core_le_retainedKer (I.mem_core_of_res_eq_one hK h1)
  obtain ⟨hB, h2⟩ := (I.mem_retainedKer_iff _).mp hc
  have e : (⟨(g : Ghat)⁻¹ * h, hB⟩ : GB) = g⁻¹ * h := rfl
  rw [e, map_mul, map_inv] at h2
  exact inv_mul_eq_one.mp h2

/-- Elements of `G_B` with equal restrictions to an admissible `K` have equal labels. -/
theorem genusLabel_eq_of_resB_eq (hK : K.fixingSubgroup ≤ I.core) {g h : GB}
    (he : resB K g = resB K h) : genusLabel g = genusLabel h := by
  have h1 := congrArg (fun q : Retained.Q => Multiplicative.ofAdd q.base)
    (I.retainedMap_eq_of_resB_eq hK he)
  simp only [retainedMap_base] at h1
  exact h1

theorem resB_ne_one_of_retainedMap (hK : K.fixingSubgroup ≤ I.core) {g : GB}
    (hg : I.retainedMap g ≠ 1) : resB K g ≠ 1 := by
  intro h
  apply hg
  have := I.retainedMap_eq_of_resB_eq hK (h.trans (map_one (resB K)).symm)
  rw [this, map_one]

end Admissible

end Input

end UnitDistance.Sqrt241.Retained
