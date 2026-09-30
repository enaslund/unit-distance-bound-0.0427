module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.FiniteAbelian.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual relative units in a quadratic number-field extension

The norm here is Mathlib's field norm restricted to the actual rings of integers.
The complexifying-place hypotheses specify embeddings and compatibility with the
nontrivial field automorphism. In particular they do not assume a norm sign,
a torsion count, an index formula, or any regulator identity.
-/

noncomputable section
open scoped NumberField

namespace UnitDistance.RelativeUnits

variable {F K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- The ordinary relative norm on the actual unit groups. -/
def unitNorm : (𝓞 K)ˣ →* (𝓞 F)ˣ := Units.map (RingOfIntegers.norm F)

omit [NumberField F] [NumberField K] [Algebra.IsQuadraticExtension F K] in
@[simp] theorem coe_unitNorm (u : (𝓞 K)ˣ) :
    (unitNorm (F := F) u : F) = Algebra.norm F (u : K) := rfl

/-- The relative unit group, with no prescribed rank or torsion assumption. -/
def normOneUnits : Subgroup (𝓞 K)ˣ := (unitNorm (F := F)).ker

/-- The actual image whose index is denoted `I_U` in the manuscript. -/
def normUnitImage : Subgroup (𝓞 F)ˣ := (unitNorm (F := F) (K := K)).range

lemma automorphism_eq_one_or (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (g : K ≃ₐ[F] K) :
    g = 1 ∨ g = ι := by
  classical
  have hc : Fintype.card (K ≃ₐ[F] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two F K]
  have hu : (Finset.univ : Finset (K ≃ₐ[F] K)) = {1, ι} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa [Finset.card_pair hι.symm] using hc.le
  have := Finset.mem_univ g
  rwa [hu, Finset.mem_insert, Finset.mem_singleton] at this

/-- The ordinary field norm is the product over the two automorphisms. -/
theorem norm_eq_mul_involution (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (x : K) :
    algebraMap F K (Algebra.norm F x) = x * ι x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  have hu : (Finset.univ : Finset (K ≃ₐ[F] K)) = {1, ι} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact automorphism_eq_one_or ι hι g
  rw [hu, Finset.prod_pair hι.symm]
  rfl

variable (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
  (ρ : F →+* ℝ) (σ : K →+* ℂ)
  (hbase : ∀ x : F, σ (algebraMap F K x) = (ρ x : ℂ))
  (hconj : ∀ x : K, σ (ι x) = star (σ x))

include ι hι σ hbase hconj in
/-- Relative norms are strictly positive at the specified complexifying real place. -/
theorem norm_pos_at_real_place (x : K) (hx : x ≠ 0) :
    0 < ρ (Algebra.norm F x) := by
  have he := congrArg σ (norm_eq_mul_involution ι hι x)
  rw [hbase, map_mul, hconj] at he
  change (ρ (Algebra.norm F x) : ℂ) = σ x * (starRingEnd ℂ) (σ x) at he
  rw [Complex.mul_conj] at he
  have hr : ρ (Algebra.norm F x) = Complex.normSq (σ x) := Complex.ofReal_injective he
  rw [hr]
  exact Complex.normSq_pos.mpr (by simpa using σ.injective.ne hx)

include ρ in
/-- A real embedding forces every torsion unit to be `1` or `-1`. -/
theorem torsion_eq_one_or_neg_one (u : (𝓞 F)ˣ)
    (hu : u ∈ NumberField.Units.torsion F) : u = 1 ∨ u = -1 := by
  have ho : IsOfFinOrder u := (CommGroup.mem_torsion u).mp hu
  have hn : ‖ρ (u : F)‖ = 1 :=
    (((ρ.toMonoidHom.comp (algebraMap (𝓞 F) F).toMonoidHom).comp
      (Units.coeHom (𝓞 F))).isOfFinOrder ho).norm_eq_one
  rw [Real.norm_eq_abs, abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at hn
  rcases hn with hp | hm
  · left
    apply NumberField.Units.coe_injective F
    apply ρ.injective
    simpa using hp
  · right
    apply NumberField.Units.coe_injective F
    apply ρ.injective
    simpa using hm

include ι hι ρ σ hbase hconj in
/-- At a complexifying real place, the norm image meets base torsion only in one. -/
theorem norm_torsion_eq_one (u : (𝓞 K)ˣ)
    (hu : unitNorm (F := F) u ∈ NumberField.Units.torsion F) :
    unitNorm (F := F) u = 1 := by
  rcases torsion_eq_one_or_neg_one ρ _ hu with h | h
  · exact h
  · have hp := norm_pos_at_real_place ι hι ρ σ hbase hconj (u : K)
      (NumberField.Units.coe_ne_zero u)
    rw [← coe_unitNorm, h] at hp
    norm_num at hp

include ι hι ρ σ hbase hconj in
/-- Every root of unity of `K` is an actual relative norm-one unit. -/
theorem torsion_le_normOneUnits :
    NumberField.Units.torsion K ≤ normOneUnits (F := F) := by
  intro u hu
  apply norm_torsion_eq_one ι hι ρ σ hbase hconj
  exact (CommGroup.mem_torsion _).mpr
    ((unitNorm (F := F)).isOfFinOrder ((CommGroup.mem_torsion _).mp hu))

include ι hι ρ σ hbase hconj in
/-- The torsion correction in the norm image is trivial, not an extra hypothesis. -/
theorem normUnitImage_inf_torsion :
    normUnitImage (F := F) (K := K) ⊓ NumberField.Units.torsion F = ⊥ := by
  apply le_antisymm
  · rintro u ⟨⟨v, rfl⟩, hu⟩
    exact norm_torsion_eq_one ι hι ρ σ hbase hconj v hu
  · exact bot_le

include ρ in
/-- A number field with the specified real embedding has exactly two roots of unity. -/
theorem torsionOrder_eq_two : NumberField.Units.torsionOrder F = 2 := by
  classical
  let := Fintype.ofFinite (NumberField.Units.torsion F)
  rw [NumberField.Units.torsionOrder, Nat.card_eq_fintype_card]
  refine Finset.card_eq_two.mpr ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_,
      fun _ ↦ Finset.mem_univ _⟩⟩
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact torsion_eq_one_or_neg_one ρ x.val x.property

include ι hι ρ σ hbase hconj in
/-- The manuscript's exact factor two before passage to the logarithmic unit image.
This is an identity of actual group indices; it makes no finiteness assumption. -/
theorem normUnitImage_index_eq_two_mul :
    (normUnitImage (F := F) (K := K)).index =
      2 * (normUnitImage (F := F) (K := K) ⊔ NumberField.Units.torsion F).index := by
  let N := normUnitImage (F := F) (K := K)
  let T := NumberField.Units.torsion F
  have hi : N.relIndex (N ⊔ T) = 2 := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right,
      normUnitImage_inf_torsion ι hι ρ σ hbase hconj, Subgroup.relIndex_bot_left]
    exact torsionOrder_eq_two ρ
  rw [← N.relIndex_mul_index (show N ≤ N ⊔ T from le_sup_left), hi]

/-- The index of the actual logarithmic norm image inside the full logarithmic
unit image; both groups are images of the ordinary weighted log embedding. -/
def logarithmicNormIndex : ℕ :=
  ((normUnitImage (F := F) (K := K)).toAddSubgroup.map
    (NumberField.Units.logEmbedding F)).relIndex (NumberField.Units.logEmbedding F).range

include ι hι ρ σ hbase hconj in
/-- The exact norm-image correction after quotienting out logarithmic torsion.
This is the `I_U/2` appearing in the regulator calculation, proved for the
actual number-field logarithmic embedding. -/
theorem unitNorm_index_eq_two_mul_logarithmicNormIndex :
    (normUnitImage (F := F) (K := K)).index =
      2 * logarithmicNormIndex (F := F) (K := K) := by
  rw [normUnitImage_index_eq_two_mul ι hι ρ σ hbase hconj]
  congr 1
  unfold logarithmicNormIndex
  rw [AddMonoidHom.range_eq_map, AddSubgroup.relIndex_map_map,
    top_sup_eq, AddSubgroup.relIndex_top_right,
    NumberField.Units.dirichletUnitTheorem.logEmbedding_ker]
  rw [← Subgroup.toAddSubgroup.map_sup, Subgroup.index_toAddSubgroup]

omit [NumberField F] [NumberField K] in
/-- Every base unit square lies in the actual relative norm image. -/
theorem square_mem_normUnitImage (u : (𝓞 F)ˣ) :
    u ^ 2 ∈ normUnitImage (F := F) (K := K) := by
  refine ⟨Units.map (algebraMap (𝓞 F) (𝓞 K)) u, ?_⟩
  apply Units.ext
  change RingOfIntegers.norm F (algebraMap (𝓞 F) (𝓞 K) (u : 𝓞 F)) = _
  rw [RingOfIntegers.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two]
  rfl

/-- The norm image has finite index by Dirichlet finite generation and the square inclusion. -/
instance normUnitImage_finiteIndex : (normUnitImage (F := F) (K := K)).FiniteIndex := by
  letI : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  have hpow := Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 F)ˣ
    (by decide : (2 : ℕ) ≠ 0)
  exact Subgroup.finiteIndex_of_le (H := (powMonoidHom (α := (𝓞 F)ˣ) 2).range)
    (by rintro u ⟨v, rfl⟩; exact square_mem_normUnitImage v)

/-- The kernel of the actual weighted logarithm restricted to relative norm-one units. -/
def relativeLogKernel : Subgroup (normOneUnits (F := F) (K := K)) :=
  (((NumberField.Units.logEmbedding K).toMultiplicative).comp
    (normOneUnits (F := F)).subtype).ker

omit [NumberField F] [Algebra.IsQuadraticExtension F K] in
/-- Restriction of Kronecker's theorem to the actual relative unit group. -/
theorem relativeLogKernel_eq :
    relativeLogKernel (F := F) (K := K) =
      (NumberField.Units.torsion K).subgroupOf (normOneUnits (F := F)) := by
  ext u
  change NumberField.Units.logEmbedding K (Additive.ofMul u.val) = 0 ↔
    u.val ∈ NumberField.Units.torsion K
  exact NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff

include ι hι ρ σ hbase hconj in
/-- The relative logarithmic kernel has exactly `w_K` elements; no torsion
normalization is supplied as an assumption. -/
theorem card_relativeLogKernel :
    Nat.card (relativeLogKernel (F := F) (K := K)) = NumberField.Units.torsionOrder K := by
  rw [relativeLogKernel_eq]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (torsion_le_normOneUnits ι hι ρ σ hbase hconj)).toEquiv

include ι hι ρ σ hbase hconj in
/-- The logarithmic image index is the positive integer `I_U / 2`. -/
theorem logarithmicNormIndex_eq_div_two :
    logarithmicNormIndex (F := F) (K := K) =
      (normUnitImage (F := F) (K := K)).index / 2 := by
  rw [unitNorm_index_eq_two_mul_logarithmicNormIndex ι hι ρ σ hbase hconj,
    Nat.mul_div_cancel_left _ (by decide : 0 < (2 : ℕ))]

include ι hι ρ σ hbase hconj in
/-- The actual logarithmic norm index is nonzero; the correction is nonvacuous. -/
theorem logarithmicNormIndex_pos : 0 < logarithmicNormIndex (F := F) (K := K) := by
  have hn := (normUnitImage_finiteIndex (F := F) (K := K)).index_ne_zero
  rw [unitNorm_index_eq_two_mul_logarithmicNormIndex ι hι ρ σ hbase hconj] at hn
  exact Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hn).2

end UnitDistance.RelativeUnits
