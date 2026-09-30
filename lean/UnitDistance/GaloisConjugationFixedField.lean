module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual fixed field of complex conjugation

These constructions use an actual number field, an actual complex embedding,
and its actual conjugation automorphism. The field is the fixed field of the
cyclic subgroup it generates. Its quadratic degree and real embedding are
proved; no signature or assigned degree is supplied as field data.
-/

noncomputable section
namespace UnitDistance.GaloisConjugation
open NumberField NumberField.ComplexEmbedding Module

variable (K : Type*) [Field K] [NumberField K]

/-- The actual intermediate field fixed by the chosen automorphism. -/
def fixedField (c : Gal(K/ℚ)) : IntermediateField ℚ K :=
  IntermediateField.fixedField (Subgroup.zpowers c)

variable {K} (φ : K →+* ℂ) (c : Gal(K/ℚ))

/-- Every element of the fixed field is fixed by the displayed generator. -/
theorem generator_fixes (x : fixedField K c) : c (x : K) = x :=
  (IntermediateField.mem_fixedField_iff _ _).mp x.property c (Subgroup.mem_zpowers c)

/-- The actual chosen embedding restricts to a real embedding of the fixed field. -/
theorem isReal_restriction (hc : IsConj φ c) :
    IsReal (φ.comp (algebraMap (fixedField K c) K)) := by
  ext x
  change star (φ (x : K)) = φ (x : K)
  rw [← hc.eq, generator_fixes]

/-- The actual fixed field has a specified real embedding. -/
def realEmbedding (hc : IsConj φ c) : fixedField K c →+* ℝ :=
  (isReal_restriction φ c hc).embedding

/-- Nontrivial actual complex conjugation has a quadratic fixed field. -/
theorem relativeDegree_eq_two (hc : IsConj φ c) (hc1 : c ≠ 1) :
    finrank (fixedField K c) K = 2 := by
  rw [fixedField, IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
  exact orderOf_isConj_two_of_ne_one hc hc1

/-- The actual absolute degrees satisfy the quadratic tower identity. -/
theorem absoluteDegree_eq_two_mul (hc : IsConj φ c) (hc1 : c ≠ 1) :
    finrank ℚ K = 2 * finrank ℚ (fixedField K c) := by
  rw [← finrank_mul_finrank ℚ (fixedField K c) K, relativeDegree_eq_two φ c hc hc1, mul_comm]

/-- There is at least one actual real place of the conjugation fixed field. -/
theorem nrRealPlaces_pos (hc : IsConj φ c) :
    0 < InfinitePlace.nrRealPlaces (fixedField K c) := by
  classical
  rw [← InfinitePlace.card_real_embeddings]
  exact Fintype.card_pos_iff.mpr ⟨⟨_, isReal_restriction φ c hc⟩⟩

/-- Consequently the actual complex-place ratio is strictly below one half. -/
theorem complexPlaceRatio_lt_half (hc : IsConj φ c) :
    (InfinitePlace.nrComplexPlaces (fixedField K c) : ℝ) /
      finrank ℚ (fixedField K c) < 1/2 := by
  have hdegree := finrank_pos (R := ℚ) (M := fixedField K c)
  have hreal := nrRealPlaces_pos φ c hc
  have hsig := InfinitePlace.card_add_two_mul_card_eq_rank (fixedField K c)
  have hdeg : (0 : ℝ) < finrank ℚ (fixedField K c) := by exact_mod_cast hdegree
  apply (div_lt_iff₀ hdeg).mpr
  have hreal' : (0 : ℝ) < InfinitePlace.nrRealPlaces (fixedField K c) := by exact_mod_cast hreal
  have hsig' : (InfinitePlace.nrRealPlaces (fixedField K c) : ℝ) +
      2 * InfinitePlace.nrComplexPlaces (fixedField K c) = finrank ℚ (fixedField K c) := by
    exact_mod_cast hsig
  linarith

end UnitDistance.GaloisConjugation

namespace UnitDistance.GaloisConjugation
open NumberField NumberField.ComplexEmbedding Module
variable {K : Type*} [Field K] [NumberField K]
variable (φ : K →+* ℂ) (c : Gal(K/ℚ))

/-- Restriction is real exactly when its actual conjugation fixes the field. -/
theorem isReal_restriction_iff_mem_fixingSubgroup
    (hc : IsConj φ c) (F : IntermediateField ℚ K) :
    IsReal (φ.comp (algebraMap F K)) ↔ c ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    apply φ.injective
    rw [hc.eq]
    exact RingHom.congr_fun h ⟨x,hx⟩
  · intro h
    ext x
    change star (φ (x : K)) = φ (x : K)
    rw [← hc.eq,h _ x.property]

/-- A nontrivial involution's cyclic subgroup has exactly its two displayed elements. -/
theorem mem_zpowers_conjugation_iff (hc : IsConj φ c) (hc1 : c ≠ 1)
    (g : Gal(K/ℚ)) : g ∈ Subgroup.zpowers c ↔ g = 1 ∨ g = c := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,orderOf_isConj_two_of_ne_one hc hc1]
  simp [Finset.mem_image, Finset.mem_range,
    Nat.le_one_iff_eq_zero_or_eq_one, eq_comm]

/-- Among actual Galois translates of the chosen embedding, those whose
restriction to the conjugation fixed field is real are exactly the
translates by automorphisms commuting with conjugation. -/
theorem isReal_translate_restriction_iff (hc : IsConj φ c) (hc1 : c ≠ 1)
    (ν : Gal(K/ℚ)) :
    IsReal ((φ.comp ν.toRingHom).comp (algebraMap (fixedField K c) K)) ↔
      Commute c ν := by
  have hcc : IsConj (φ.comp ν.toRingHom) (ν⁻¹ * c * ν) := hc.comp ν
  rw [isReal_restriction_iff_mem_fixingSubgroup _ _ hcc, fixedField,
    IntermediateField.fixingSubgroup_fixedField, mem_zpowers_conjugation_iff φ c hc hc1]
  have hn : ν⁻¹ * c * ν ≠ 1 := by
    intro h
    apply hc1
    have h' := congrArg (fun g : Gal(K/ℚ) => ν * g * ν⁻¹) h
    simpa [mul_assoc] using h'
  rw [or_iff_right hn]
  change ν⁻¹ * c * ν = c ↔ c * ν = ν * c
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]

end UnitDistance.GaloisConjugation

namespace UnitDistance.GaloisConjugation
open NumberField NumberField.ComplexEmbedding Module
variable {K : Type*} [Field K] [NumberField K]
variable (φ : K →+* ℂ) (F : IntermediateField ℚ K)

/-- Restrict an actual Galois translate of the chosen complex embedding. -/
def translateRestriction (ν : Gal(K/ℚ)) : F →+* ℂ :=
  (φ.comp ν.toRingHom).comp (algebraMap F K)

/-- Every embedding of an actual intermediate field extends and is a
Galois translate of the chosen embedding. -/
theorem translateRestriction_surjective [IsGalois ℚ K] :
    Function.Surjective (translateRestriction φ F) := by
  intro ψ
  obtain ⟨ψ', hψ'⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
    (K := ℚ) (L := F) (E := K) (M := ℂ) ψ.toRatAlgHom
  obtain ⟨ν,hν⟩ := exists_comp_symm_eq_of_comp_eq (k := ℚ) φ ψ'.toRingHom
    (RingHom.ext_rat _ _)
  refine ⟨ν.symm,?_⟩
  apply RingHom.ext
  intro x
  change φ (ν.symm (x : K)) = ψ x
  have h1 := RingHom.congr_fun hν (x : K)
  have h2 := AlgHom.congr_fun hψ' x
  exact h1.trans h2

/-- A restriction fiber is an actual coset of the fixing subgroup. -/
def restrictionFiberEquiv (ν : Gal(K/ℚ)) :
    F.fixingSubgroup ≃ {g : Gal(K/ℚ) // translateRestriction φ F g = translateRestriction φ F ν} where
  toFun h := ⟨ν * h, by
    ext x
    change φ (ν (h.val (x : K))) = φ (ν (x : K))
    rw [(IntermediateField.mem_fixingSubgroup_iff _ _).mp h.property _ x.property]⟩
  invFun g := ⟨ν⁻¹ * g, by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hh := RingHom.congr_fun g.property (⟨x,hx⟩ : F)
    change φ (g.val x) = φ (ν x) at hh
    have hh' := φ.injective hh
    change ν.symm (g.val x) = x
    rw [hh',ν.symm_apply_apply]⟩
  left_inv h := by
    apply Subtype.ext
    change ν⁻¹ * (ν * h.val) = h.val
    simp
  right_inv g := by
    apply Subtype.ext
    change ν * (ν⁻¹ * g.val) = g.val
    simp

/-- All actual embedding restriction fibers have the actual relative degree. -/
theorem card_restrictionFiber [IsGalois ℚ K] (ψ : F →+* ℂ) :
    Nat.card {g : Gal(K/ℚ) // translateRestriction φ F g = ψ} =
      finrank F K := by
  obtain ⟨ν,rfl⟩ := translateRestriction_surjective φ F ψ
  rw [← Nat.card_congr (restrictionFiberEquiv φ F ν)]
  rw [Nat.card_congr (IntermediateField.fixingSubgroupEquiv F).toEquiv]
  exact IsGalois.card_aut_eq_finrank F K

end UnitDistance.GaloisConjugation

namespace UnitDistance.GaloisConjugation
open NumberField NumberField.ComplexEmbedding Module
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
variable (φ : K →+* ℂ) (c : Gal(K/ℚ))

/-- The real embeddings of the actual conjugation fixed field are counted
by the actual centralizer: each restriction fiber has size two. -/
theorem centralizer_card_eq_two_mul_nrRealPlaces
    (hc : IsConj φ c) (hc1 : c ≠ 1) :
    Nat.card (Subgroup.centralizer ({c} : Set (Gal(K/ℚ)))) =
      2 * InfinitePlace.nrRealPlaces (fixedField K c) := by
  classical
  letI : Fintype (Gal(K/ℚ)) := Fintype.ofFinite _
  have hreal (ν : Gal(K/ℚ)) : ν ∈ Subgroup.centralizer ({c} : Set (Gal(K/ℚ))) ↔
      IsReal (translateRestriction φ (fixedField K c) ν) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (eq_comm.trans (isReal_translate_restriction_iff φ c hc hc1 ν).symm)
  let e := Equiv.sigmaSubtypeFiberEquivSubtype
    (translateRestriction φ (fixedField K c)) hreal
  have hcard := Fintype.card_congr e
  rw [Fintype.card_sigma] at hcard
  have hfiber (ψ : {ψ : fixedField K c →+* ℂ // IsReal ψ}) :
      Fintype.card {g : Gal(K/ℚ) // translateRestriction φ (fixedField K c) g = ψ.val} = 2 := by
    rw [← Nat.card_eq_fintype_card,card_restrictionFiber,
      relativeDegree_eq_two φ c hc hc1]
  simp_rw [hfiber] at hcard
  rw [Finset.sum_const,Finset.card_univ,smul_eq_mul,
    InfinitePlace.card_real_embeddings] at hcard
  rw [Nat.card_eq_fintype_card]
  exact hcard.symm.trans (mul_comm _ _)

/-- The actual real-place proportion equals the actual centralizer proportion. -/
theorem realPlaceRatio_eq_centralizerRatio
    (hc : IsConj φ c) (hc1 : c ≠ 1) :
    (InfinitePlace.nrRealPlaces (fixedField K c) : ℝ) / finrank ℚ (fixedField K c) =
      (Nat.card (Subgroup.centralizer ({c} : Set (Gal(K/ℚ))))) /
        (Nat.card (Gal(K/ℚ)) : ℝ) := by
  rw [centralizer_card_eq_two_mul_nrRealPlaces φ c hc hc1,
    IsGalois.card_aut_eq_finrank ℚ K,absoluteDegree_eq_two_mul φ c hc hc1]
  push_cast
  field_simp

end UnitDistance.GaloisConjugation

namespace UnitDistance.GaloisConjugation
open NumberField NumberField.ComplexEmbedding Module

/-- Passing to an actual quotient can only decrease a conjugacy-class index. -/
theorem centralizer_index_le_of_surjective
    {G Q : Type*} [Group G] [Finite G] [Group Q] (π : G →* Q)
    (hπ : Function.Surjective π) (c : G) :
    (Subgroup.centralizer ({π c} : Set Q)).index ≤
      (Subgroup.centralizer ({c} : Set G)).index := by
  have hle : Subgroup.centralizer ({c} : Set G) ≤
      (Subgroup.centralizer ({π c} : Set Q)).comap π := by
    intro g hg
    simp only [Subgroup.mem_comap,Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    simpa only [map_mul] using congrArg π hg
  have hi := Subgroup.index_antitone hle
  rwa [Subgroup.index_comap_of_surjective _ hπ] at hi

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
variable (φ : K →+* ℂ) (c : Gal(K/ℚ))

/-- The real-place proportion is the reciprocal of the actual conjugacy index. -/
theorem realPlaceRatio_eq_inv_centralizerIndex
    (hc : IsConj φ c) (hc1 : c ≠ 1) :
    (InfinitePlace.nrRealPlaces (fixedField K c) : ℝ) / finrank ℚ (fixedField K c) =
      1 / (Subgroup.centralizer ({c} : Set (Gal(K/ℚ)))).index := by
  rw [realPlaceRatio_eq_centralizerRatio φ c hc hc1,
    ← (Subgroup.centralizer ({c} : Set (Gal(K/ℚ)))).card_mul_index]
  have hC : (Nat.card (Subgroup.centralizer ({c} : Set (Gal(K/ℚ)))) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := Subgroup.centralizer ({c} : Set (Gal(K/ℚ))))).ne'
  push_cast
  field_simp

/-- A retained finite quotient's independently defined centralizer index
bounds the actual complex-place proportion of the fixed number field. -/
theorem complexPlaceRatio_bounds_of_retained_index
    (hc : IsConj φ c) (hc1 : c ≠ 1)
    {Q : Type*} [Group Q] (π : Gal(K/ℚ) →* Q) (hπ : Function.Surjective π)
    (m : ℕ) (hm : 0 < m)
    (hindex : m ≤ (Subgroup.centralizer ({π c} : Set Q)).index) :
    (1-1/(m : ℝ))/2 ≤
      (InfinitePlace.nrComplexPlaces (fixedField K c) : ℝ) / finrank ℚ (fixedField K c) ∧
    (InfinitePlace.nrComplexPlaces (fixedField K c) : ℝ) / finrank ℚ (fixedField K c) < 1/2 := by
  refine ⟨?_,complexPlaceRatio_lt_half φ c hc⟩
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmi := hindex.trans (centralizer_index_le_of_surjective π hπ c)
  have hmi' : (m : ℝ) ≤ (Subgroup.centralizer ({c} : Set (Gal(K/ℚ)))).index := by
    exact_mod_cast hmi
  have hreal : (InfinitePlace.nrRealPlaces (fixedField K c) : ℝ) /
      finrank ℚ (fixedField K c) ≤ 1/(m : ℝ) := by
    rw [realPlaceRatio_eq_inv_centralizerIndex φ c hc hc1]
    exact one_div_le_one_div_of_le hm' hmi'
  have hd : (0 : ℝ) < finrank ℚ (fixedField K c) := by
    exact_mod_cast (finrank_pos (R := ℚ) (M := fixedField K c))
  have hsig : (InfinitePlace.nrRealPlaces (fixedField K c) : ℝ) +
      2 * InfinitePlace.nrComplexPlaces (fixedField K c) = finrank ℚ (fixedField K c) := by
    exact_mod_cast (InfinitePlace.card_add_two_mul_card_eq_rank (fixedField K c))
  have he : (InfinitePlace.nrRealPlaces (fixedField K c) : ℝ) / finrank ℚ (fixedField K c) +
      2 * ((InfinitePlace.nrComplexPlaces (fixedField K c) : ℝ) /
        finrank ℚ (fixedField K c)) = 1 := by
    rw [← mul_div_assoc, ← add_div, hsig, div_self hd.ne']
  linarith

/-- The manuscript's signature interval follows from a genuine quotient
with centralizer index at least `2^12`; the signature itself is derived. -/
theorem complexPlaceRatio_bounds_4096
    (hc : IsConj φ c) (hc1 : c ≠ 1)
    {Q : Type*} [Group Q] (π : Gal(K/ℚ) →* Q) (hπ : Function.Surjective π)
    (hindex : 4096 ≤ (Subgroup.centralizer ({π c} : Set Q)).index) :
    (4095 : ℝ)/8192 ≤
      (InfinitePlace.nrComplexPlaces (fixedField K c) : ℝ) / finrank ℚ (fixedField K c) ∧
    (InfinitePlace.nrComplexPlaces (fixedField K c) : ℝ) / finrank ℚ (fixedField K c) < 1/2 := by
  have h := complexPlaceRatio_bounds_of_retained_index φ c hc hc1 π hπ 4096 (by norm_num) hindex
  norm_num at h ⊢
  exact h

end UnitDistance.GaloisConjugation

namespace UnitDistance.GaloisConjugation
open NumberField NumberField.ComplexEmbedding Module
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
variable (φ : K →+* ℂ)

/-- Normality constructs the actual conjugation automorphism under any
chosen complex embedding. -/
theorem exists_conjugation : ∃ c : Gal(K/ℚ), IsConj φ c := by
  obtain ⟨ν,hν⟩ := exists_comp_symm_eq_of_comp_eq (k := ℚ) φ (conjugate φ)
    (RingHom.ext_rat _ _)
  exact ⟨ν.symm,hν.symm⟩

/-- An actual square root of minus one rules out real embeddings. -/
theorem not_isReal_of_sqrt_neg_one (x : K) (hx : x^2 = -1) : ¬ IsReal φ := by
  intro h
  have hs := congrArg h.embedding hx
  simp only [map_pow,map_neg,map_one] at hs
  nlinarith [sq_nonneg (h.embedding x)]

/-- A number field containing an actual square root of minus one has a
nontrivial actual conjugation under every complex embedding. -/
theorem exists_nontrivial_conjugation (x : K) (hx : x^2 = -1) :
    ∃ c : Gal(K/ℚ), IsConj φ c ∧ c ≠ 1 := by
  obtain ⟨c,hc⟩ := exists_conjugation φ
  exact ⟨c,hc,(isConj_ne_one_iff hc).mpr (not_isReal_of_sqrt_neg_one φ x hx)⟩

end UnitDistance.GaloisConjugation

namespace UnitDistance.GaloisConjugation
open NumberField NumberField.ComplexEmbedding Module

/-- Actual growing Galois degrees yield growing conjugation-fixed degrees;
no degree sequence for the fixed fields is assumed. -/
theorem fixedField_degree_tendsto
    (K : ℕ → Type*) [∀ j, Field (K j)] [∀ j, NumberField (K j)]
    (φ : ∀ j, K j →+* ℂ) (c : ∀ j, Gal(K j/ℚ))
    (hc : ∀ j, IsConj (φ j) (c j)) (hc1 : ∀ j, c j ≠ 1)
    (hdegree : Filter.Tendsto (fun j => finrank ℚ (K j)) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun j => finrank ℚ (fixedField (K j) (c j))) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  have hb := (Filter.tendsto_atTop.mp hdegree) (2*b)
  filter_upwards [hb] with j hj
  have hd := absoluteDegree_eq_two_mul (φ j) (c j) (hc j) (hc1 j)
  omega

/-- For a growing family of actual Galois number fields containing square
roots of minus one, actual conjugation-fixed fields exist, are quadratic
under the given fields, have real embeddings, and have growing degrees. -/
theorem exists_growing_fixed_fields
    (K : ℕ → Type*) [∀ j, Field (K j)] [∀ j, NumberField (K j)]
    [∀ j, IsGalois ℚ (K j)] (φ : ∀ j, K j →+* ℂ)
    (x : ∀ j, K j) (hx : ∀ j, (x j)^2 = -1)
    (hdegree : Filter.Tendsto (fun j => finrank ℚ (K j)) Filter.atTop Filter.atTop) :
    ∃ c : ∀ j, Gal(K j/ℚ),
      (∀ j, IsConj (φ j) (c j) ∧ c j ≠ 1) ∧
      (∀ j, finrank (fixedField (K j) (c j)) (K j) = 2) ∧
      (∀ j, 0 < InfinitePlace.nrRealPlaces (fixedField (K j) (c j))) ∧
      Filter.Tendsto (fun j => finrank ℚ (fixedField (K j) (c j))) Filter.atTop Filter.atTop := by
  choose c hc hc1 using fun j => exists_nontrivial_conjugation (φ j) (x j) (hx j)
  exact ⟨c,fun j => ⟨hc j,hc1 j⟩,
    fun j => relativeDegree_eq_two (φ j) (c j) (hc j) (hc1 j),
    fun j => nrRealPlaces_pos (φ j) (c j) (hc j),
    fixedField_degree_tendsto K φ c hc hc1 hdegree⟩

end UnitDistance.GaloisConjugation
