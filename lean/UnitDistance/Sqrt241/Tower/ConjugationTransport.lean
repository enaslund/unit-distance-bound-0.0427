module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.RamificationSupport
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Transport of finite ramification along semilinear isomorphisms

Let `F` be a number field and `τ` a ring automorphism of a field `Ω ⊇ F` which
maps `F` to itself through `τ₀ : F ≃+* F`. For a finite subextension `E/F` of
`Ω`, the image `τ(E)` is again an `F`-subfield; `τ` restricts to a
`τ₀`-semilinear ring isomorphism `E ≃+* τ(E)`.

This file proves that such a semilinear isomorphism transports

* formal unramifiedness (`formallyUnramified_of_toAlgebra_range_eq`: changing
  the structure map of an algebra by an automorphism of the base does not
  change the image of the base, hence does not change formal unramifiedness),
* unramifiedness at a prime (`isUnramifiedAt_of_semilinear`),
* unramifiedness outside a set of finite places
  (`isUnramifiedAtFinitePlacesOutside_of_semilinear`),
* degree, Galois property and Galois group (`mapSemilinear`).

These are the inputs for the stability of the maximal pro-`p` extension of `F`
unramified outside a `τ₀`-stable set under all such `τ`.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.Tower

open ClassFieldTower.Sawin

/-! ### Formal unramifiedness only sees the image of the base -/

section FormallyUnramified

variable {R A : Type*} [CommRing R] [CommRing A]

/-- An algebra formally unramified over `R` is formally unramified over the
image of `R`. -/
theorem formallyUnramified_range [Algebra R A] [Algebra.FormallyUnramified R A] :
    Algebra.FormallyUnramified (algebraMap R A).range A := by
  let : Algebra R (algebraMap R A).range := (algebraMap R A).rangeRestrict.toAlgebra
  have : IsScalarTower R (algebraMap R A).range A :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  exact Algebra.FormallyUnramified.of_restrictScalars R _ _

/-- An algebra formally unramified over the image of `R` is formally
unramified over `R`. -/
theorem formallyUnramified_of_range [Algebra R A]
    [Algebra.FormallyUnramified (algebraMap R A).range A] :
    Algebra.FormallyUnramified R A := by
  let : Algebra R (algebraMap R A).range := (algebraMap R A).rangeRestrict.toAlgebra
  have : IsScalarTower R (algebraMap R A).range A :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : Algebra.FormallyUnramified R (algebraMap R A).range :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId R (algebraMap R A).range)
      (algebraMap R A).rangeRestrict_surjective
  exact Algebra.FormallyUnramified.comp R (algebraMap R A).range A

/-- Formal unramifiedness does not depend on the structure map beyond its
image: if `f` has the same range as the given structure map and `A` is formally
unramified for the algebra structure `f`, it is formally unramified. -/
theorem formallyUnramified_of_toAlgebra_range_eq [Algebra R A] (f : R →+* A)
    (hrange : f.range = (algebraMap R A).range)
    (hf : @Algebra.FormallyUnramified R A _ _ f.toAlgebra) :
    Algebra.FormallyUnramified R A := by
  have h1 : Algebra.FormallyUnramified f.range A := by
    let : Algebra R A := f.toAlgebra
    exact formallyUnramified_range (R := R) (A := A)
  rw [hrange] at h1
  exact formallyUnramified_of_range

end FormallyUnramified

/-! ### Unramifiedness at a prime along a semilinear ring isomorphism -/

section IsUnramifiedAt

variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R S']

/-- Let `e : S ≃+* S'` be semilinear over a ring automorphism `φ` of `R`. If
`S` is unramified over `R` at `P`, then `S'` is unramified over `R` at the
prime corresponding to `P`. -/
theorem isUnramifiedAt_of_semilinear (φ : R ≃+* R) (e : S ≃+* S')
    (he : ∀ r, e (algebraMap R S r) = algebraMap R S' (φ r))
    (P : Ideal S) (P' : Ideal S') [P.IsPrime] [P'.IsPrime] (hP : P = P'.comap e)
    [Algebra.IsUnramifiedAt R P] : Algebra.IsUnramifiedAt R P' := by
  have hM : P.primeCompl.map e.toMonoidHom = P'.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      intro hy
      apply hx
      rw [hP]
      exact hy
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      intro hx
      rw [hP, Ideal.mem_comap, RingEquiv.apply_symm_apply] at hx
      exact hy hx
  let ê : Localization.AtPrime P ≃+* Localization.AtPrime P' :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime P') e hM
  have hê (s : S) : ê (algebraMap S (Localization.AtPrime P) s) =
      algebraMap S' (Localization.AtPrime P') (e s) :=
    IsLocalization.ringEquivOfRingEquiv_eq hM s
  let f : R →+* Localization.AtPrime P' :=
    (ê : Localization.AtPrime P →+* Localization.AtPrime P').comp
      (algebraMap R (Localization.AtPrime P))
  have hf (r : R) : f r = algebraMap R (Localization.AtPrime P') (φ r) := by
    change ê (algebraMap R (Localization.AtPrime P) r) = _
    rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime P), hê, he,
      ← IsScalarTower.algebraMap_apply]
  have hrange : f.range = (algebraMap R (Localization.AtPrime P')).range := by
    ext y
    simp only [RingHom.mem_range]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨φ r, (hf r).symm⟩
    · rintro ⟨r, rfl⟩
      exact ⟨φ.symm r, by rw [hf, RingEquiv.apply_symm_apply]⟩
  apply formallyUnramified_of_toAlgebra_range_eq f hrange
  let : Algebra R (Localization.AtPrime P') := f.toAlgebra
  let eA : Localization.AtPrime P ≃ₐ[R] Localization.AtPrime P' :=
    AlgEquiv.ofRingEquiv (f := ê) (fun _ ↦ rfl)
  exact Algebra.FormallyUnramified.of_equiv eA

end IsUnramifiedAt

/-! ### Unramifiedness outside a set of finite places -/

section NumberField

variable {K L L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field L'] [NumberField L'] [Algebra K L] [Algebra K L']

/-- Unramifiedness outside a set of finite places is transported along a ring
isomorphism `e : L ≃+* L'` which is semilinear over an automorphism `τ₀` of the
base: a place `w` of the base whose `τ₀`-preimage `v` lies outside `T` is
unramified in `L'` when `L` is unramified outside `T`. -/
theorem isUnramifiedAtFinitePlacesOutside_of_semilinear (τ₀ : K ≃+* K) (e : L ≃+* L')
    (he : ∀ a, e (algebraMap K L a) = algebraMap K L' (τ₀ a))
    {T T' : Set (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ v w : HeightOneSpectrum (𝓞 K),
      (∀ x : 𝓞 K, x ∈ v.asIdeal ↔ RingOfIntegers.mapRingEquiv τ₀ x ∈ w.asIdeal) →
        w ∉ T' → v ∉ T)
    (h : IsUnramifiedAtFinitePlacesOutside K L T) :
    IsUnramifiedAtFinitePlacesOutside K L' T' := by
  intro P' hP'
  let eO : 𝓞 L ≃+* 𝓞 L' := RingOfIntegers.mapRingEquiv e
  let τO : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv τ₀
  have heO (r : 𝓞 K) :
      eO (algebraMap (𝓞 K) (𝓞 L) r) = algebraMap (𝓞 K) (𝓞 L') (τO r) := by
    apply RingOfIntegers.ext
    exact he r
  let P : HeightOneSpectrum (𝓞 L) :=
    { asIdeal := P'.asIdeal.comap eO
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P'.ne_bot
        intro hbot
        have hmem : eO.symm y ∈ P'.asIdeal.comap eO := by
          rw [Ideal.mem_comap, RingEquiv.apply_symm_apply]
          exact hy
        rw [hbot, Ideal.mem_bot] at hmem
        apply hy0
        have := congrArg eO hmem
        rwa [RingEquiv.apply_symm_apply, map_zero] at this }
  have hbelow : ∀ x : 𝓞 K, x ∈ (finitePlaceBelow (K := K) P).asIdeal ↔
      τO x ∈ (finitePlaceBelow (K := K) P').asIdeal := by
    intro x
    simp only [finitePlaceBelow_asIdeal, Ideal.mem_under]
    change eO (algebraMap (𝓞 K) (𝓞 L) x) ∈ P'.asIdeal ↔ _
    rw [heO]
  have hv : finitePlaceBelow (K := K) P ∉ T := hT _ _ hbelow hP'
  have hunr : Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal := h P hv
  exact isUnramifiedAt_of_semilinear τO eO heO P.asIdeal P'.asIdeal rfl

end NumberField

/-! ### Images of intermediate fields under semilinear automorphisms -/

section IntermediateField

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- `τ : Ω ≃+* Ω` restricts to `τ₀ : F ≃+* F` on the base. -/
def IsSemilinearOver (τ₀ : F ≃+* F) (τ : Ω ≃+* Ω) : Prop :=
  ∀ a, τ (algebraMap F Ω a) = algebraMap F Ω (τ₀ a)

theorem IsSemilinearOver.symm {τ₀ : F ≃+* F} {τ : Ω ≃+* Ω} (h : IsSemilinearOver τ₀ τ) :
    IsSemilinearOver τ₀.symm τ.symm := by
  intro a
  apply τ.injective
  rw [RingEquiv.apply_symm_apply, h, RingEquiv.apply_symm_apply]

theorem IsSemilinearOver.trans {τ₀ σ₀ : F ≃+* F} {τ σ : Ω ≃+* Ω} (hτ : IsSemilinearOver τ₀ τ)
    (hσ : IsSemilinearOver σ₀ σ) : IsSemilinearOver (τ₀.trans σ₀) (τ.trans σ) := by
  intro a
  simp only [RingEquiv.coe_trans, Function.comp_apply, hτ a, hσ (τ₀ a)]

variable {τ₀ : F ≃+* F} {τ : Ω ≃+* Ω}

/-- The image `τ(E)` of an intermediate field under a `τ₀`-semilinear
automorphism `τ`, as an intermediate field over `F`. -/
def mapSemilinear (hτ : IsSemilinearOver τ₀ τ) (E : IntermediateField F Ω) :
    IntermediateField F Ω :=
  RamificationTheory.Field.absoluteGaloisGroup.semilinearRingEquivPreimageIntermediateField
    τ₀.symm τ.symm hτ.symm E

theorem mem_mapSemilinear_iff (hτ : IsSemilinearOver τ₀ τ) (E : IntermediateField F Ω)
    (x : Ω) : x ∈ mapSemilinear hτ E ↔ τ.symm x ∈ E :=
  Iff.rfl

theorem apply_mem_mapSemilinear (hτ : IsSemilinearOver τ₀ τ) {E : IntermediateField F Ω}
    {x : Ω} (hx : x ∈ E) : τ x ∈ mapSemilinear hτ E := by
  rw [mem_mapSemilinear_iff, RingEquiv.symm_apply_apply]
  exact hx

theorem mapSemilinear_mono (hτ : IsSemilinearOver τ₀ τ) {E E' : IntermediateField F Ω}
    (h : E ≤ E') : mapSemilinear hτ E ≤ mapSemilinear hτ E' :=
  fun _ hx ↦ h hx

/-- The `τ₀`-semilinear ring isomorphism `E ≃+* τ(E)` induced by `τ`. -/
def mapSemilinearEquiv (hτ : IsSemilinearOver τ₀ τ) (E : IntermediateField F Ω) :
    E ≃+* mapSemilinear hτ E where
  toFun x := ⟨τ x, apply_mem_mapSemilinear hτ x.2⟩
  invFun y := ⟨τ.symm y, y.2⟩
  left_inv x := Subtype.ext (τ.symm_apply_apply (x : Ω))
  right_inv y := Subtype.ext (τ.apply_symm_apply (y : Ω))
  map_mul' x y := Subtype.ext (map_mul τ (x : Ω) (y : Ω))
  map_add' x y := Subtype.ext (map_add τ (x : Ω) (y : Ω))

@[simp] theorem coe_mapSemilinearEquiv (hτ : IsSemilinearOver τ₀ τ) (E : IntermediateField F Ω)
    (x : E) : (mapSemilinearEquiv hτ E x : Ω) = τ x :=
  rfl

@[simp] theorem coe_mapSemilinearEquiv_symm (hτ : IsSemilinearOver τ₀ τ)
    (E : IntermediateField F Ω) (y : mapSemilinear hτ E) :
    ((mapSemilinearEquiv hτ E).symm y : Ω) = τ.symm y :=
  rfl

theorem mapSemilinearEquiv_algebraMap (hτ : IsSemilinearOver τ₀ τ) (E : IntermediateField F Ω)
    (a : F) : mapSemilinearEquiv hτ E (algebraMap F E a) =
      algebraMap F (mapSemilinear hτ E) (τ₀ a) :=
  Subtype.ext (hτ a)

theorem mapSemilinearEquiv_symm_algebraMap (hτ : IsSemilinearOver τ₀ τ)
    (E : IntermediateField F Ω) (a : F) :
    (mapSemilinearEquiv hτ E).symm (algebraMap F (mapSemilinear hτ E) a) =
      algebraMap F E (τ₀.symm a) := by
  apply (mapSemilinearEquiv hτ E).injective
  rw [RingEquiv.apply_symm_apply, mapSemilinearEquiv_algebraMap, RingEquiv.apply_symm_apply]

/-- `τ(E)` has the same degree over `F` as `E`. -/
theorem finrank_mapSemilinear (hτ : IsSemilinearOver τ₀ τ) (E : IntermediateField F Ω) :
    Module.finrank F (mapSemilinear hτ E) = Module.finrank F E := by
  symm
  apply Algebra.finrank_eq_of_equiv_equiv τ₀ (mapSemilinearEquiv hτ E)
  exact RingHom.ext fun a ↦ (mapSemilinearEquiv_algebraMap hτ E a).symm

instance finiteDimensional_mapSemilinear (hτ : IsSemilinearOver τ₀ τ)
    (E : IntermediateField F Ω) [FiniteDimensional F E] :
    FiniteDimensional F (mapSemilinear hτ E) :=
  RamificationTheory.Field.absoluteGaloisGroup.finiteDimensional_semilinearRingEquivPreimageIntermediateField
    τ₀.symm τ.symm hτ.symm E

/-- Conjugation by `τ` identifies the automorphism groups of `E` and `τ(E)`
over `F`. -/
def autMapSemilinear (hτ : IsSemilinearOver τ₀ τ) (E : IntermediateField F Ω) :
    (E ≃ₐ[F] E) ≃* (mapSemilinear hτ E ≃ₐ[F] mapSemilinear hτ E) where
  toFun g := AlgEquiv.ofRingEquiv
    (f := ((mapSemilinearEquiv hτ E).symm.trans g.toRingEquiv).trans (mapSemilinearEquiv hτ E))
    (fun a ↦ by
      simp only [RingEquiv.coe_trans, Function.comp_apply,
        mapSemilinearEquiv_symm_algebraMap, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
        mapSemilinearEquiv_algebraMap, RingEquiv.apply_symm_apply])
  invFun g := AlgEquiv.ofRingEquiv
    (f := ((mapSemilinearEquiv hτ E).trans g.toRingEquiv).trans (mapSemilinearEquiv hτ E).symm)
    (fun a ↦ by
      simp only [RingEquiv.coe_trans, Function.comp_apply,
        mapSemilinearEquiv_algebraMap, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
        mapSemilinearEquiv_symm_algebraMap, RingEquiv.symm_apply_apply])
  left_inv g := by
    ext x
    simp
  right_inv g := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

/-- `τ(E)` is Galois over `F` when `E` is. -/
theorem isGalois_mapSemilinear (hτ : IsSemilinearOver τ₀ τ) (E : IntermediateField F Ω)
    [FiniteDimensional F E] [IsGalois F E] : IsGalois F (mapSemilinear hτ E) := by
  apply IsGalois.of_card_aut_eq_finrank
  rw [← Nat.card_congr (autMapSemilinear hτ E).toEquiv, IsGalois.card_aut_eq_finrank,
    finrank_mapSemilinear]

theorem isPGroup_mapSemilinear (hτ : IsSemilinearOver τ₀ τ) (E : IntermediateField F Ω)
    {p : ℕ} (h : IsPGroup p (E ≃ₐ[F] E)) :
    IsPGroup p (mapSemilinear hτ E ≃ₐ[F] mapSemilinear hτ E) :=
  h.of_equiv (autMapSemilinear hτ E)

section NumberField

variable [NumberField F]

/-- A finite subextension of `Ω` over the number field `F` is a number field. -/
local instance numberFieldOfFinite (E : IntermediateField F Ω) [FiniteDimensional F E] :
    NumberField E :=
  NumberField.of_module_finite F E

/-- Unramifiedness outside a set of finite places passes from `E` to `τ(E)`,
with the set moved by `τ₀` (hypothesis `hT`). -/
theorem isUnramifiedAtFinitePlacesOutside_mapSemilinear (hτ : IsSemilinearOver τ₀ τ)
    (E : IntermediateField F Ω) [FiniteDimensional F E]
    {T T' : Set (HeightOneSpectrum (𝓞 F))}
    (hT : ∀ v w : HeightOneSpectrum (𝓞 F),
      (∀ x : 𝓞 F, x ∈ v.asIdeal ↔ RingOfIntegers.mapRingEquiv τ₀ x ∈ w.asIdeal) →
        w ∉ T' → v ∉ T)
    (h : IsUnramifiedAtFinitePlacesOutside F E T) :
    IsUnramifiedAtFinitePlacesOutside F (mapSemilinear hτ E) T' :=
  isUnramifiedAtFinitePlacesOutside_of_semilinear τ₀ (mapSemilinearEquiv hτ E)
    (mapSemilinearEquiv_algebraMap hτ E) hT h

end NumberField

end IntermediateField

end UnitDistance.Sqrt241.Tower
