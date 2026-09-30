/-
Generalizes `UnitDistance/OneInfinitePlaceNorm.lean` and
`UnitDistance/FiniteCyclicFinitePlaceH2.lean` from a base with one infinite
place to a base with two infinite places: the finite places then detect cyclic
field-unit H² up to a kernel of at most two elements.
-/
module

public import UnitDistance.FiniteCyclicFinitePlaceH2

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Cyclic field-unit H² over a base with two infinite places

(a) For an abelian extension `L/K` and a principal idele that is a local norm
at every finite place and at every infinite place but one, the global Artin
product formula forces the remaining infinite component to be a local norm too
(`infinite_local_norm_of_local_norms_away`); with the cyclic Hasse norm
principle this gives a global norm (`global_norm_of_local_norms_away`).

(b) If `L/K` is quadratic and `K` has two infinite places `v₀, v₁`, the classes
of `H²(Gal(L/K), Lˣ)` vanishing at every finite place form a set `{0, x₀}`
(`finiteQuadraticFieldUnitsH2_pair`): the Artin symbol at `v₀` of a scalar
representative determines the class.
-/

noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField BigOperators IsMulCommutative TensorProduct

namespace UnitDistance.Sqrt241.Relation

open GlobalClassFieldTheory.Reciprocity GlobalClassFieldTheory.ClassFieldAxiom
open UnitDistance.ArithmeticProP ClassFieldTower.Cohomology

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsAbelianGalois K L]

/-- For a principal idele, local norm conditions at all finite places and at
all infinite places but `v₀` imply the local norm condition at `v₀`. -/
theorem infinite_local_norm_of_local_norms_away (x : Kˣ) (v₀ : InfinitePlace K)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K x) ∈
        chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, v ≠ v₀ →
      IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele K x) ∈
        infiniteTensorNormSubgroup (K := K) (L := L) v) :
    IdeleGroup.infiniteComponent v₀ (IdeleGroup.principalIdele K x) ∈
      infiniteTensorNormSubgroup (K := K) (L := L) v₀ := by
  have hf : ∀ w : HeightOneSpectrum (𝓞 K),
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) w
        (IdeleGroup.finiteComponent w (IdeleGroup.principalIdele K x)) = 1 := by
    intro w
    change IdeleGroup.finiteComponent w (IdeleGroup.principalIdele K x) ∈
      (chosenFinitePlaceArtinMonoidHom (K := K) (L := L) w).ker
    rw [chosenFinitePlaceArtinMonoidHom_ker]
    exact hfin w
  have hi : ∀ v : InfinitePlace K, v ≠ v₀ →
      chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v
        (IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele K x)) = 1 := by
    intro v hv
    change IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele K x) ∈
      (chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v).ker
    rw [chosenInfinitePlaceArtinMonoidHom_ker]
    exact hinf v hv
  have hp := chosenLocalArtin_product_principalIdele (K := K) (L := L) x
  rw [finprod_eq_one_of_forall_eq_one hf, mul_one,
    Fintype.prod_eq_single v₀ (fun v hv => hi v hv)] at hp
  rw [← chosenInfinitePlaceArtinMonoidHom_ker]
  exact hp

/-- For a cyclic extension, a field unit that is a local norm at every finite
place and every infinite place but one is a global norm. -/
theorem global_norm_of_local_norms_away [IsCyclic Gal(L/K)] (x : Kˣ)
    (v₀ : InfinitePlace K)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K x) ∈
        chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, v ≠ v₀ →
      IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele K x) ∈
        infiniteTensorNormSubgroup (K := K) (L := L) v) :
    x ∈ globalFieldNormSubgroup K L := by
  rw [hasseNormPrinciple_cyclic K L]
  change IdeleGroup.principalIdele K x ∈
    allPlaceLocalNormCondition (K := K) (L := L)
  refine ⟨Subgroup.mem_iInf.mpr hfin, Subgroup.mem_iInf.mpr ?_⟩
  intro v
  change IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele K x) ∈
    infiniteTensorNormSubgroup (K := K) (L := L) v
  by_cases hv : v = v₀
  · subst hv
    exact infinite_local_norm_of_local_norms_away K L x v hfin hinf
  · exact hinf v hv

/-- The Artin symbol at an infinite place `v₀` of the principal idele of a
field unit. -/
def infiniteArtinAt (v₀ : InfinitePlace K) : Kˣ →* Gal(L/K) :=
  (chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v₀).comp
    ((IdeleGroup.infiniteComponent v₀).comp (IdeleGroup.principalIdele K))

/-- Two nonidentity elements of a group of order two coincide. -/
theorem eq_of_ne_one_of_natCard_eq_two {G : Type*} [Group G] (hG : Nat.card G = 2)
    {a b : G} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  obtain ⟨x, y, hxy, huniv⟩ := Nat.card_eq_two_iff.mp hG
  have hmem : ∀ z : G, z = x ∨ z = y := by
    intro z
    have hz : z ∈ ({x, y} : Set G) := huniv ▸ Set.mem_univ z
    simpa using hz
  rcases hmem 1 with h1 | h1 <;> rcases hmem a with h | h <;> rcases hmem b with h' | h'
  all_goals first
    | (subst_vars; rfl)
    | (exfalso; apply ha; subst_vars; rfl)
    | (exfalso; apply hb; subst_vars; rfl)

section Pair

variable [IsCyclic Gal(L/K)]

local instance quadraticDetectionCommGroup : CommGroup Gal(L/K) := IsCyclic.commGroup

theorem fieldScalarUnitFixed_div (g : Gal(L/K)) (b c : Kˣ) :
    fieldScalarUnitFixed K L g (b / c) =
      fieldScalarUnitFixed K L g b - fieldScalarUnitFixed K L g c := by
  apply Subtype.ext
  change Additive.ofMul (Units.map (algebraMap K L).toMonoidHom (b / c)) =
    Additive.ofMul (Units.map (algebraMap K L).toMonoidHom b) -
      Additive.ofMul (Units.map (algebraMap K L).toMonoidHom c)
  rw [map_div, ofMul_div]

/-- Over a base with two infinite places, the finite-place detection kernel
of quadratic field-unit H² has at most two elements. -/
theorem finiteQuadraticFieldUnitsH2_pair (hG : Nat.card Gal(L/K) = 2)
    (v₀ v₁ : InfinitePlace K) (hK : ∀ v : InfinitePlace K, v = v₀ ∨ v = v₁) :
    ∃ x₀ : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2, ∀ x,
      (∀ v : HeightOneSpectrum (𝓞 K),
        (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom x = 0) → x = 0 ∨ x = x₀ := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let c : Kˣ → groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 := fun b =>
    Rep.FiniteCyclicGroup.groupCohomologyπEven (Rep.ofAlgebraAutOnUnits K L) g hg 2
      (by decide) (fieldScalarUnitFixed K L g b)
  have hc : ∀ x, ∃ b, c b = x := fun x => exists_fieldScalarUnitH2 K L g hg x
  have hloc : ∀ b : Kˣ,
      (∀ v : HeightOneSpectrum (𝓞 K),
        (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom (c b) = 0) →
      ∀ v : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K b) ∈
          chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v := by
    intro b hb v
    have h := (fieldScalarUnitH2_tensor_eq_zero_iff_norm K L (v.adicCompletion K) g hg b).mp
      (hb v)
    rw [← finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
    exact h
  have hzero : ∀ b : Kˣ,
      (∀ v : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K b) ∈
          chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v) →
      infiniteArtinAt K L v₀ b = 1 → c b = 0 := by
    intro b hfin hart
    apply (fieldScalarUnitH2_eq_zero_iff_norm K L g hg b).mpr
    apply global_norm_of_local_norms_away K L b v₁ hfin
    intro v hv
    rcases hK v with rfl | rfl
    · rw [← chosenInfinitePlaceArtinMonoidHom_ker]
      exact hart
    · exact absurd rfl hv
  by_cases hex : ∃ x₁ : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2,
      (∀ v : HeightOneSpectrum (𝓞 K),
        (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom x₁ = 0) ∧ x₁ ≠ 0
  · obtain ⟨x₁, hx₁, hne⟩ := hex
    refine ⟨x₁, fun x hx => ?_⟩
    obtain ⟨b, rfl⟩ := hc x
    obtain ⟨b₁, rfl⟩ := hc x₁
    by_cases hb : infiniteArtinAt K L v₀ b = 1
    · exact Or.inl (hzero b (hloc b hx) hb)
    · right
      have hb₁ : infiniteArtinAt K L v₀ b₁ ≠ 1 := fun h => hne (hzero b₁ (hloc b₁ hx₁) h)
      have heq : infiniteArtinAt K L v₀ b = infiniteArtinAt K L v₀ b₁ :=
        eq_of_ne_one_of_natCard_eq_two hG hb hb₁
      have hdiv : c (b / b₁) = 0 := by
        apply hzero
        · intro v
          rw [map_div, map_div]
          exact Subgroup.div_mem _ (hloc b hx v) (hloc b₁ hx₁ v)
        · rw [map_div, heq, div_self']
      have hsub : c (b / b₁) = c b - c b₁ := by
        change Rep.FiniteCyclicGroup.groupCohomologyπEven (Rep.ofAlgebraAutOnUnits K L) g hg 2
          (by decide) (fieldScalarUnitFixed K L g (b / b₁)) = _
        rw [fieldScalarUnitFixed_div, map_sub]
      rw [hsub] at hdiv
      exact sub_eq_zero.mp hdiv
  · push Not at hex
    exact ⟨0, fun x hx => Or.inl (hex x hx)⟩

end Pair

end UnitDistance.Sqrt241.Relation
