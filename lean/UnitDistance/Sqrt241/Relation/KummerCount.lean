/-
Generalizes `UnitDistance/RationalFiniteKummerReduction.lean` from ℚ to an
arbitrary number field `K`, with the finite-place detection of field-unit H²
weakened to a detection kernel of at most two elements. The elementary
quotient-cardinality argument adapts FiniteKummerSPlaceCardinality at
Yamaguchi/Sawin commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4 (Apache-2.0).
-/
module

public import UnitDistance.RationalFiniteKummerReduction

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Counting the Kummer image of a finite stage with a detection kernel of order two

For a finite Galois `2`-extension `L/K` unramified outside a finite set `S`,
the field-unit Kummer image of `H²(Gal(L/K), μ₂)` has at most `2^|S| · 2`
elements, provided the classes of `H²(Gal(L/K), Lˣ)` that vanish at every
finite place form a set `{0, x₀}` (`FiniteDetectionPair`). Over ℚ the
detection kernel is trivial; over a field with two real places it has order
at most two.
-/

noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct

namespace UnitDistance.Sqrt241.Relation

open ClassFieldTower.Martinet.Shafarevich ClassFieldTower.Cohomology
open UnitDistance.ArithmeticProP

/-- The finite-place detection kernel of field-unit H² of every finite Galois
2-extension of `K` has at most two elements. -/
def FiniteDetectionPair (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L], IsPGroup 2 Gal(L/K) →
    ∃ x₀ : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2, ∀ x,
      (∀ v : HeightOneSpectrum (𝓞 K),
        (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom x = 0) → x = 0 ∨ x = x₀

/-- If `g` kills a subgroup of order at most `k` of `ker f`, then
`|g(A)| ≤ k · |f(A)|`. -/
theorem natCard_range_le_of_map_ker
    {A B' C : Type} [AddCommGroup A] [AddCommGroup B'] [AddCommGroup C]
    (f : A →+ B') (g : A →+ C) [Finite f.range] (k : ℕ)
    (hk : Finite (f.ker.map g) ∧ Nat.card (f.ker.map g) ≤ k) :
    Finite g.range ∧ Nat.card g.range ≤ k * Nat.card f.range := by
  obtain ⟨hkfin, hkcard⟩ := hk
  let H : AddSubgroup g.range := (f.ker.map g).addSubgroupOf g.range
  have hHle : f.ker.map g ≤ g.range := by
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩
  have hHcard : Nat.card H = Nat.card (f.ker.map g) := by
    have e := AddSubgroup.addSubgroupOfEquivOfLe hHle
    exact Nat.card_congr e.toEquiv
  -- the induced map `A → g(A) / H` kills `ker f`
  let π : A →+ g.range ⧸ H := (QuotientAddGroup.mk' H).comp g.rangeRestrict
  have hπ : f.ker ≤ π.ker := by
    intro a ha
    change (QuotientAddGroup.mk' H) (g.rangeRestrict a) = 0
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    change (g.rangeRestrict a : C) ∈ f.ker.map g
    exact ⟨a, ha, rfl⟩
  have hπs : Function.Surjective π :=
    (QuotientAddGroup.mk'_surjective H).comp g.rangeRestrict_surjective
  let q : A ⧸ f.ker →+ g.range ⧸ H := QuotientAddGroup.lift f.ker π hπ
  have hq : Function.Surjective q :=
    QuotientAddGroup.lift_surjective_of_surjective f.ker π hπs hπ
  let e := (QuotientAddGroup.quotientKerEquivRange f).symm
  have hsurj : Function.Surjective (fun x : f.range => q (e x)) := hq.comp e.surjective
  have hQfin : Finite (g.range ⧸ H) := Finite.of_surjective _ hsurj
  have hQcard : Nat.card (g.range ⧸ H) ≤ Nat.card f.range :=
    Nat.card_le_card_of_surjective _ hsurj
  have hHfin : Finite H := by
    have e := AddSubgroup.addSubgroupOfEquivOfLe hHle
    exact Finite.of_equiv _ e.toEquiv.symm
  have hLag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hfin : Finite g.range := by
    apply Nat.finite_of_card_ne_zero
    rw [hLag]
    exact Nat.mul_ne_zero (Nat.card_pos.ne') (Nat.card_pos.ne')
  refine ⟨hfin, ?_⟩
  rw [hLag, hHcard, mul_comm]
  exact Nat.mul_le_mul hkcard hQcard

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local instance kummerCountIdeleAction :
    MulDistribMulAction Gal(L/K) (RelativeIdeleGroup K L) :=
  RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L
local instance kummerCountSupportedAction (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulDistribMulAction Gal(L/K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := K) (L := L) S
local instance kummerCountTensorAction (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L/K) (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.adicCompletion K)

omit [IsGalois K L] in
/-- The support-factorized Kummer coefficient has the tensor localization as
its finite coordinate. -/
theorem kummerSupported_tensor_factor
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hmu : (primitiveRoots ((2 : ℕ+) : ℕ) K).Nonempty) (v : HeightOneSpectrum (𝓞 K)) :
    finiteKummerSSupportedIdeleRepHom K L S (2 : ℕ+) hmu ≫
        supportedIdeleInclusionRepHom K L S ≫ ideleFiniteRepHom K L v =
      finiteKummerCoefficientRepHom K L (2 : ℕ+) hmu ≫
        fieldUnitsTensorRepHom K L (v.adicCompletion K) := by
  ext z
  apply Units.ext
  rfl

/-- A Kummer class vanishing at the places of `S` has field-unit image
vanishing at every finite place (the places outside `S` are unramified). -/
theorem finiteKummer_localizations_eq_zero_of_mem_ker
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hmu : (primitiveRoots ((2 : ℕ+) : ℕ) K).Nonempty)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    ∀ x ∈ (finiteKummerSPlaceH2Localization K L S (2 : ℕ+) hmu).ker,
    ∀ v : HeightOneSpectrum (𝓞 K), (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom
      ((finiteKummerCoefficientH2Map K L (2 : ℕ+) hmu).hom x) = 0 := by
  intro x hx v
  change finiteKummerSPlaceH2Localization K L S (2 : ℕ+) hmu x = 0 at hx
  let C := groupCohomology.functor ℤ Gal(L/K) 2
  let y := (C.map (finiteKummerSSupportedIdeleRepHom K L S (2 : ℕ+) hmu)).hom x
  have hf := congrArg (fun f => (C.map f).hom x)
    (kummerSupported_tensor_factor K L S hmu v)
  simp only [Functor.map_comp] at hf
  change (ideleFiniteH2 K L v).hom
      ((C.map (supportedIdeleInclusionRepHom K L S)).hom y) =
    (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom
      ((finiteKummerCoefficientH2Map K L (2 : ℕ+) hmu).hom x) at hf
  rw [← hf]
  by_cases hv : v ∈ S
  · have hz := congrFun hx ⟨v, hv⟩
    change supportedSPlaceH2Localization K L S y ⟨v, hv⟩ = 0 at hz
    rw [supportedIdeleH2_localization_eq K L S y ⟨v, hv⟩] at hz
    exact hz
  · exact supportedIdeleH2_finite_eq_zero_of_unramified K L S v hv (hfin v hv) y

/-- Every finite Galois 2-extension unramified outside `S` whose finite-place
detection kernel has at most two elements has a field-unit Kummer image of
cardinality at most `2^|S| · 2`. -/
theorem finiteKummerH2_range_natCard_le_of_pair
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hmu : (primitiveRoots ((2 : ℕ+) : ℕ) K).Nonempty) (hP : IsPGroup 2 Gal(L/K))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hpair : ∃ x₀ : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2, ∀ x,
      (∀ v : HeightOneSpectrum (𝓞 K),
        (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom x = 0) → x = 0 ∨ x = x₀) :
    Finite (finiteKummerCoefficientH2Map K L (2 : ℕ+) hmu).hom.toAddMonoidHom.range ∧
      Nat.card (finiteKummerCoefficientH2Map K L (2 : ℕ+) hmu).hom.toAddMonoidHom.range ≤
        2 ^ S.card * 2 := by
  have hlocal := finiteKummerSPlaceH2Localization_range_finite_natCard_le
    K L S (2 : ℕ+) hmu hP
  have := hlocal.1
  obtain ⟨x₀, hx₀⟩ := hpair
  let f := finiteKummerSPlaceH2Localization K L S (2 : ℕ+) hmu
  let g := (finiteKummerCoefficientH2Map K L (2 : ℕ+) hmu).hom.toAddMonoidHom
  have hsub : ((f.ker.map g : AddSubgroup _) :
      Set (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)) ⊆ {0, x₀} := by
    rintro _ ⟨x, hx, rfl⟩
    rcases hx₀ (g x) (finiteKummer_localizations_eq_zero_of_mem_ker K L S hmu hfin x hx)
      with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hpairFin : ({0, x₀} : Set (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)).Finite :=
    Set.toFinite _
  have hk : Finite (f.ker.map g) ∧ Nat.card (f.ker.map g) ≤ 2 := by
    refine ⟨(hpairFin.subset hsub).to_subtype, ?_⟩
    calc Nat.card (f.ker.map g)
        = Nat.card ((f.ker.map g : AddSubgroup _) :
            Set (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)) := rfl
      _ ≤ Nat.card ({0, x₀} : Set (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)) :=
          Nat.card_mono hpairFin hsub
      _ = ({0, x₀} : Set (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have h := natCard_range_le_of_map_ker f g 2 hk
  refine ⟨h.1, h.2.trans ?_⟩
  rw [mul_comm]
  exact Nat.mul_le_mul_right 2 hlocal.2

end UnitDistance.Sqrt241.Relation
