module

public import UnitDistance.Sqrt241.Local.TamePairs
public import UnitDistance.Sqrt241.ProP.AbsoluteProPUnramified
public import UnitDistance.Sqrt241.ProP.FinitePExtensionSupport
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.RationalRamificationSupport
public import UnitDistance.AbsoluteDecompositionPrime
public import UnitDistance.Sqrt241.ProP.ProPStageLocalConditions

@[expose] public section
set_option backward.privateInPublic true

/-!
# `Ω/ℚ` is unramified outside `{2, 3, 5, 241}`: absolute inertia is killed

* Finite subextensions of `Ω/B` are unramified outside `S` (`layer_unramified`): they lie in
  an admissible layer of `Ω_B` (`ProP.finiteDimensional_le_iSup_pExtension_exists_extension`),
  and unramifiedness descends to subextensions (`IsUnramifiedAtFinitePlacesOutside.bot`).
* `B/ℚ` is unramified outside `241` (`B_unramified`, discriminant `241`), so a finite
  `K/B` unramified outside `S` is unramified over `ℚ` outside `{2, 3, 5, 241}`
  (`isUnramified_rat_of_B`, transitivity of `Algebra.IsUnramifiedAt`).
* For every rational prime `p ∉ {2, 3, 5, 241}`, the chosen absolute inertia group at `p`
  fixes `Ω` pointwise (`inertia_killed`): every `x ∈ Ω` lies in a finite Galois layer of `Ω`
  containing `B`, which is unramified at `p` over `ℚ` (`ProP.finiteInertia_fixes_layer`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Local

open NumberField IsDedekindDomain CanonicalGenus Base UnitDistance.PrimeCompletion Tower
open ClassFieldTower.Sawin ClassFieldTower.Martinet.Shafarevich AlgebraicNumberTheory.Valuations

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-- The finite places of `ℚ` above `2, 3, 5, 241`. -/
def ramSupportQ : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | ((7230 : ℤ) : 𝓞 ℚ) ∈ v.asIdeal}

theorem mem_place_dvd (p : Nat.Primes) (n : ℤ) (h : (n : 𝓞 ℚ) ∈ (place p).asIdeal) :
    (p.val : ℤ) ∣ n := by
  by_contra hnd
  have hp : Prime (p.val : ℤ) := Nat.prime_iff_prime_int.mp p.property
  obtain ⟨a, b, hab⟩ := hp.irreducible.coprime_iff_not_dvd.mpr hnd
  have hpm : ((p.val : ℤ) : 𝓞 ℚ) ∈ (place p).asIdeal := by
    have := prime_mem_place p
    exact_mod_cast this
  have h1 : ((a * p.val + b * n : ℤ) : 𝓞 ℚ) ∈ (place p).asIdeal := by
    push_cast
    exact add_mem ((place p).asIdeal.mul_mem_left _ hpm) ((place p).asIdeal.mul_mem_left _ h)
  rw [hab, Int.cast_one] at h1
  exact (place p).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem place_not_mem_ramSupportQ (p : Nat.Primes) (hp : p.val ∉ ({2, 3, 5, 241} : Finset ℕ)) :
    place p ∉ ramSupportQ := by
  intro h
  have hd := mem_place_dvd p 7230 h
  have hd' : p.val ∣ 2 * 3 * 5 * 241 := by exact_mod_cast hd
  have hpp : Nat.Prime p.val := p.property
  apply hp
  rcases (Nat.Prime.dvd_mul hpp).mp hd' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hpp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hpp).mp h2 with h3 | h3
      · rw [(Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h3]; decide
      · rw [(Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp h3]; decide
    · rw [(Nat.prime_dvd_prime_iff_eq hpp Nat.prime_five).mp h2]; decide
  · rw [(Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h1]; decide

/-- `B/ℚ` is unramified outside `241`, in particular outside `{2, 3, 5, 241}`. -/
theorem B_unramified : IsUnramifiedAtFinitePlacesOutside ℚ B ramSupportQ := by
  rw [isUnramifiedAtFinitePlacesOutside_rat_iff_discr]
  intro q hq
  rw [discr_eq] at hq
  have hq' : q.val ∣ 241 := by exact_mod_cast hq
  have h241 : q.val = 241 :=
    (Nat.prime_dvd_prime_iff_eq q.property (by norm_num)).mp hq'
  change ((7230 : ℤ) : 𝓞 ℚ) ∈ (place q).asIdeal
  have hm : ((q.val : ℤ) : 𝓞 ℚ) ∈ (place q).asIdeal := by
    have := prime_mem_place q
    exact_mod_cast this
  rw [h241] at hm
  have he : ((7230 : ℤ) : 𝓞 ℚ) = 30 * (((241 : ℕ) : ℤ) : 𝓞 ℚ) := by norm_num
  rw [he]
  exact (place q).asIdeal.mul_mem_left _ hm

local instance numberFieldOfFiniteB (K : IntermediateField B Closure) [FiniteDimensional B K] :
    NumberField K :=
  NumberField.of_module_finite B K

/-- A finite `K/B` unramified outside `S` is unramified over `ℚ` outside `{2, 3, 5, 241}`. -/
theorem isUnramified_rat_of_B (L : IntermediateField B Closure) [FiniteDimensional B L]
    (hL : IsUnramifiedAtFinitePlacesOutside B L S) :
    IsUnramifiedAtFinitePlacesOutside ℚ L ramSupportQ := by
  intro P hP
  let p : HeightOneSpectrum (𝓞 B) := finitePlaceBelow (K := B) P
  have hlies : P.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have hpS : p ∉ S := by
    intro h30
    apply hP
    rw [← finitePlaceBelow_finitePlaceBelow (K := ℚ) (M := B) P]
    change ((7230 : ℤ) : 𝓞 ℚ) ∈ p.asIdeal.under (𝓞 ℚ)
    rw [Ideal.under, Ideal.mem_comap, map_intCast]
    have he : ((7230 : ℤ) : 𝓞 B) = 241 * 30 := by norm_num
    rw [he]
    exact p.asIdeal.mul_mem_left _ h30
  have hpQ : finitePlaceBelow (K := ℚ) p ∉ ramSupportQ := by
    rw [finitePlaceBelow_finitePlaceBelow]
    exact hP
  have h1 : Algebra.IsUnramifiedAt (𝓞 ℚ) p.asIdeal := B_unramified p hpQ
  have h2 : Algebra.IsUnramifiedAt (𝓞 B) P.asIdeal := hL P hpS
  exact Algebra.IsUnramifiedAt.comp (R := 𝓞 ℚ) p.asIdeal P.asIdeal

local instance numberFieldOfFiniteBbar (K : IntermediateField B Bbar) [FiniteDimensional B K] :
    NumberField K :=
  NumberField.of_module_finite B K

/-- **Finite subextensions of `Ω/B` are unramified outside `S`.** -/
theorem layer_unramified (K : IntermediateField B Closure) [FiniteDimensional B K]
    (hK : K ≤ OmegaBcl) : IsUnramifiedAtFinitePlacesOutside B K S := by
  let Kb : IntermediateField B Bbar := K.map (chi : Closure →ₐ[B] Bbar)
  let e : K ≃ₐ[B] Kb := IntermediateField.equivMap K (chi : Closure →ₐ[B] Bbar)
  have : FiniteDimensional B Kb := e.toLinearEquiv.finiteDimensional
  have hKb : Kb ≤ ⨆ E : ProP.FinitePExtension B 2 S, E.val.toIntermediateField := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_OmegaBcl_iff x).mp (hK hx)
  obtain ⟨C, hC⟩ := ProP.finiteDimensional_le_iSup_pExtension_exists_extension B 2 S Kb hKb
  have hCun : IsUnramifiedAtFinitePlacesOutside B C.val S := C.property.2
  let : Algebra Kb C.val := (IntermediateField.inclusion hC).toRingHom.toAlgebra
  have : IsScalarTower B Kb C.val := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hKbun : IsUnramifiedAtFinitePlacesOutside B Kb S :=
    IsUnramifiedAtFinitePlacesOutside.bot S hCun
  exact IsUnramifiedAtFinitePlacesOutside.congrTop e.symm hKbun

theorem layerCl_le_Omega (W : OpenNormalSubgroup Ghat) : layerCl W ≤ Omega := by
  rintro _ ⟨y, _, rfl⟩
  exact y.2

/-- **Absolute inertia at `p ∉ {2, 3, 5, 241}` fixes `Ω` pointwise.** -/
theorem inertia_fixes_Omega (p : Nat.Primes) (hp : p.val ∉ ({2, 3, 5, 241} : Finset ℕ))
    (σ : AbsoluteInertia p) (x : Closure) (hx : x ∈ Omega) : σ.val.val x = x := by
  let xo : Omega := ⟨x, hx⟩
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {xo}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral xo)
  have hopen : IsOpen ((IntermediateField.adjoin ℚ {xo}).fixingSubgroup : Set Ghat) :=
    IntermediateField.fixingSubgroup_isOpen _
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen
    (Subgroup.one_mem _)
  have hxW : xo ∈ IntermediateField.fixedField (W : Subgroup Ghat) := by
    rintro ⟨g, hg⟩
    have hgfix := hW hg
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hgfix xo
      (IntermediateField.mem_adjoin_simple_self ℚ xo)
  let F' : IntermediateField ℚ Closure := layerCl W ⊔ B
  have : FiniteDimensional ℚ F' := IntermediateField.finiteDimensional_sup _ _
  have : Normal ℚ F' := IntermediateField.normal_sup ℚ Closure (layerCl W) B
  have : IsGalois ℚ F' := IsGalois.mk
  have : NumberField F' := NumberField.of_module_finite ℚ F'
  have hB : B ≤ F' := le_sup_right
  have hF'Ω : F' ≤ Omega := sup_le (layerCl_le_Omega W) B_le_Omega
  let L : IntermediateField B Closure := IntermediateField.extendScalars hB
  have : FiniteDimensional B L := Module.Finite.of_restrictScalars_finite ℚ B L
  have hL : L ≤ OmegaBcl := fun y hy => hF'Ω hy
  have hLQ := isUnramified_rat_of_B L (layer_unramified L hL)
  have hF'un : IsUnramifiedAtFinitePlacesOutside ℚ F' ramSupportQ :=
    IsUnramifiedAtFinitePlacesOutside.congrTop (extendScalarsRingEquiv F' hB).symm.toRatAlgEquiv hLQ
  let M : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) := { toIntermediateField := F' }
  have : NumberField M := NumberField.of_module_finite ℚ M
  have hfix := ProP.finiteInertia_fixes_layer ℚ M ramSupportQ hF'un (place p)
    (place_not_mem_ramSupportQ p hp) σ
  have hxF' : x ∈ F' := le_sup_left (a := layerCl W) (mem_layerCl W xo hxW)
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hfix x hxF'

/-- **`inertia_killed`**: the chosen absolute inertia group at `p ∉ {2, 3, 5, 241}` maps
trivially into `Ĝ`. -/
theorem inertia_killed (p : Nat.Primes) (hp : p.val ∉ ({2, 3, 5, 241} : Finset ℕ))
    (σ : AbsoluteInertia p) : decompositionMap p σ.val = 1 := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [decompositionMap_apply, toGhat_apply]
  exact inertia_fixes_Omega p hp σ x x.2

theorem inertia_killed_B (p : Nat.Primes) (hp : p.val ∉ ({2, 3, 5, 241} : Finset ℕ))
    (hsq : IsSquare (241 : ℚ_[p.val])) (P₀ P : Fin 2) (σ : AbsoluteInertia p) :
    localMapB p hsq P₀ P σ.val = 1 := by
  apply Subtype.ext
  rw [coe_localMapB, inertia_killed p hp σ, mul_one, mul_inv_cancel]
  rfl

end UnitDistance.Sqrt241.Local
