module

public import UnitDistance.Sqrt241.Levels.Tame
public import UnitDistance.Sqrt241.Cut.LocalImages

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Exact local types of admissible fields at `2, 3, 5, 29, 7`

For every admissible `K` (finite Galois `K ≤ Ω`, `M ≤ K`, `kernelHat ≤ Gal(Ω/K)`;
e.g. `M` and every level `K_j`), the ℚ package's absolute inertia and decomposition
restrictions at the five witness primes have images of cardinalities
`e` and `e f` with `(e, f) = (8,4), (2,2), (2,2), (1,4), (1,8)`
(`admissible_local_image_cards`), hence (`PrimeCompletion.ramification_residue_of_absolute_image_cards`)
`ramificationIdxIn = e` and `inertiaDegIn = f` (`admissible_ramification_residue`).

* `3, 5`: `Levels/Tame.lean` (images of the normalized tame maps; the unnormalized
  maps are conjugate).
* `29`: `Local.decomposition_range_unramified` (cyclic on the Frobenius, inertia killed);
  the Frobenius is conjugate to `Frob(29₁) = E.cap 0`, whose fourth power is a cut word
  and whose square is nontrivial in `Q_B` (`LocalModels.cap_square_ne_one`); order `4`.
* `7`: `⟨F₇⟩` with `F₇⁸ = (E.cap 2)⁴` a cut word and `F₇⁴ = (E.cap 2)²` nontrivial in `Q_B`;
  order `8`.
The computations at `2, 3, 5, 29` use only the cut words of the symmetric input `inputSym`
(`Retained/Sym.lean`), so they hold for every finite Galois `K` with
`inputSym.kernelHat ≤ Gal(Ω/K) ≤ core` (`sym_ramification_residue`); version 2 applies them to
the Galois closures of its levels. Version 1's admissible fields satisfy these hypotheses
(`inputSym_kernelHat_le`, `inputSym_core`).

* `2`: the restriction of `G_B` to `K` factors through the cut quotient; with
  `Cut.SourceLifts.dyadicQuotientMap` the chosen dyadic map factors through the ℚ₂-local
  cut `D` (`Local/DyadicCut.lean`) by an injective map (injectivity through `ρ_B` and
  `Retained.dyadicMapOfLifts`), and `Local.image_cards_of_factor` gives `8` and `32`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation Cut GroupData ProCGroups UnitDistance.PrimeCompletion
open _root_.UnitDistance.Sqrt241.Local
open scoped NumberField

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ### Cap words (any input) -/

theorem cap_fourth_word (I : Input) (k : Fin 3) : I.A.cap k ^ 4 ∈ I.A.lifts.words := by
  fin_cases k
  · exact Or.inr ⟨4, rfl⟩
  · exact Or.inr ⟨5, rfl⟩
  · exact Or.inr ⟨6, rfl⟩

theorem freeMap_cap (I : Input) (k : Fin 3) : freeMap (I.A.cap k) = I.E.cap k :=
  LocalElements.freeMap_lift _

theorem res_cap_fourth (I : Input) {K : IntermediateField ℚ Omega} [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (hker : I.kernelHat ≤ K.fixingSubgroup) (k : Fin 3) :
    Input.res K ((I.E.cap k : Ghat) ^ 4) = 1 := by
  have h := I.res_eq_one_of_word hker (cap_fourth_word I k)
  rw [map_pow, freeMap_cap] at h
  simpa using h

theorem retainedMap_cap_sq_ne_one (I : Input) (k : Fin 3) : I.retainedMap (I.E.cap k ^ 2) ≠ 1 := by
  rw [map_pow]
  apply LocalModels.cap_square_ne_one_of_good
  rw [I.retainedMap_base]
  exact I.labels.cap k

theorem res_cap_sq_ne_one (I : Input) {K : IntermediateField ℚ Omega} [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (hcore : K.fixingSubgroup ≤ I.core) (k : Fin 3) :
    Input.res K ((I.E.cap k : Ghat) ^ 2) ≠ 1 := by
  have h := I.resB_ne_one_of_retainedMap hcore (retainedMap_cap_sq_ne_one I k)
  rw [resB_apply] at h
  simpa using h

section Cards

variable {K : IntermediateField ℚ Omega} [FiniteDimensional ℚ K] [IsGalois ℚ K]
  (hker : inputSym.kernelHat ≤ K.fixingSubgroup) (hcore : K.fixingSubgroup ≤ inputSym.core)

/-! ### `3` and `5` -/

include hker hcore in
theorem tame_image_cards (q : Fin 4) :
    Nat.card (inertiaRestriction (tamePrime (tameK q)) K (jK K)).range = 2 ∧
      Nat.card (decompositionRestriction (tamePrime (tameK q)) K (jK K)).range = 4 := by
  set x := Input.res K (frame (tamePlace (tameK q)) (tameP q))
  constructor
  · rw [← card_tame_inertia_range hker hcore q]
    symm
    apply card_range_conj _ _ x
    intro t
    change Input.res K ((tameDecompositionMap q t.val : GB) : Ghat) = _
    rw [inertiaRestriction_eq, tameDecompositionMap, coe_localMapB, map_mul, map_mul, map_inv]
  · rw [← card_tame_decomposition_range hker hcore q]
    symm
    apply card_range_conj _ _ x
    intro d
    change Input.res K ((tameDecompositionMap q d : GB) : Ghat) = _
    rw [decompositionRestriction_eq, tameDecompositionMap, coe_localMapB, map_mul, map_mul,
      map_inv]

/-! ### `29` -/

theorem cap_zero_eq : ((inputSym.E.cap 0 : GB) : Ghat) =
    frame place29 0 * decompositionMap prime29 frob29Abs * (frame place29 0)⁻¹ :=
  coe_localMapB _ _ _ _ _

include hker hcore in
theorem orderOf_res_frob29 :
    orderOf (Input.res K (decompositionMap prime29 frob29Abs)) = 4 := by
  set x := Input.res K (frame place29 0)
  have hc : Input.res K ((inputSym.E.cap 0 : GB) : Ghat) =
      (MulAut.conj x) (Input.res K (decompositionMap prime29 frob29Abs)) := by
    rw [cap_zero_eq, map_mul, map_mul, map_inv, MulAut.conj_apply]
  have ho : orderOf (Input.res K ((inputSym.E.cap 0 : GB) : Ghat)) = 4 := by
    have h4 := res_cap_fourth inputSym hker 0
    have h2 := res_cap_sq_ne_one inputSym hcore 0
    rw [map_pow] at h4 h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)
  rw [hc] at ho
  rw [← orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective]
  exact ho

include hker hcore in
theorem image_cards_29 :
    Nat.card (inertiaRestriction prime29 K (jK K)).range = 1 ∧
      Nat.card (decompositionRestriction prime29 K (jK K)).range = 4 := by
  constructor
  · have hb : (inertiaRestriction prime29 K (jK K)).range = ⊥ := by
      apply le_antisymm _ bot_le
      rintro _ ⟨σ, rfl⟩
      rw [Subgroup.mem_bot, inertiaRestriction_eq, inertia_killed prime29 twentynine_not_mem σ,
        map_one]
    rw [hb, Subgroup.card_bot]
  · have hr := decomposition_range_unramified prime29 twentynine_not_mem (Input.res K)
    rw [decompositionRestriction_eq_comp]
    change Nat.card ((Input.res K).comp (decompositionMap prime29)).toMonoidHom.range = 4
    rw [hr, Nat.card_zpowers]
    exact orderOf_res_frob29 hker hcore

/-! ### `2` -/

theorem projB_ker_le_resB (hker : inputSym.kernelHat ≤ K.fixingSubgroup) :
    inputSym.projB.toMonoidHom.ker ≤ (resB K).toMonoidHom.ker := by
  intro g hg
  change Input.res K (g : Ghat) = 1
  apply inputSym.res_eq_one_of_kernelHat hker
  exact (inputSym.mem_kernelHat_iff g).mpr ⟨g.2, hg⟩

/-- The restriction to `K`, descended to the cut quotient. -/
def resQ (hker : inputSym.kernelHat ≤ K.fixingSubgroup) :
    inputSym.A.ActualQuotient →* Gal(K/ℚ) :=
  inputSym.projB.toMonoidHom.liftOfSurjective inputSym.projB_surjective
    ⟨(resB K).toMonoidHom, projB_ker_le_resB hker⟩

theorem resQ_projB (g : GB) : resQ hker (inputSym.projB g) = resB K g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The dyadic local group `D` at the chosen place, in `Gal(K/ℚ)`. -/
def dyadicK : Dyadic.D →* Gal(K/ℚ) :=
  (resQ hker).comp
    (inputSym.A.dyadicQuotientMap genuineRelation detector_genuineRelation inputSym.hgen
      dyadicPlace).toMonoidHom

include hcore in
theorem dyadicK_injective : Function.Injective (dyadicK hker) := by
  intro x y hxy
  set d := inputSym.A.dyadicQuotientMap genuineRelation detector_genuineRelation inputSym.hgen
    dyadicPlace
  obtain ⟨g, hg⟩ := inputSym.projB_surjective (d x)
  obtain ⟨h, hh⟩ := inputSym.projB_surjective (d y)
  have hgh : resB K g = resB K h := by
    rw [← resQ_projB hker, ← resQ_projB hker, hg, hh]
    exact hxy
  have hret := inputSym.retainedMap_eq_of_resB_eq hcore hgh
  have hdiag := inputSym.A.retained_dyadicQuotientMap genuineRelation detector_genuineRelation
    inputSym.hgen inputSym.hL dyadicPlace
  apply Retained.dyadicMapOfLifts_injective dyadicPlace _ _ _
  rw [← hdiag]
  change inputSym.A.retained inputSym.hL (d x) = inputSym.A.retained inputSym.hL (d y)
  rw [← hg, ← hh]
  exact hret

theorem dyadicLocal_eq_freeMap (s : LocalSource) :
    dyadicLocal dyadicPlace (localPresentation s) =
      freeMap (inputSym.A.dyadic dyadicPlace s) :=
  (LocalElements.freeMap_dyadicLift inputSym.E dyadicPlace s).symm

theorem resB_dyadicLocal_factor :
    (resB K).toMonoidHom.comp (dyadicLocal dyadicPlace).toMonoidHom =
      (dyadicK hker).comp localCut.toMonoidHom := by
  apply factor_through_localCut
  apply MonoidHom.ext
  intro s
  change resB K (dyadicLocal dyadicPlace (localPresentation s)) =
    resQ hker (inputSym.A.dyadicQuotientMap genuineRelation detector_genuineRelation inputSym.hgen
      dyadicPlace (Dyadic.ArithmeticPresentation.model s))
  rw [SourceLifts.dyadicQuotientMap_model, dyadicLocal_eq_freeMap, ← inputSym.projB_freeMap,
    resQ_projB]

include hker hcore in
theorem image_cards_2 :
    Nat.card (inertiaRestriction prime2 K (jK K)).range = 8 ∧
      Nat.card (decompositionRestriction prime2 K (jK K)).range = 32 := by
  have hψ : decompositionRestriction prime2 K (jK K) = (dyadicK hker).comp dyadicCutD := by
    rw [← decompositionMapB_factor _ _ (resB_dyadicLocal_factor hker),
      decompositionRestriction_eq_comp]
    rfl
  exact image_cards_of_factor _ _ (dyadicK_injective hker hcore) hψ

end Cards

section Seven

variable {K : IntermediateField ℚ Omega} [FiniteDimensional ℚ K] [IsGalois ℚ K]
  (hker : input.kernelHat ≤ K.fixingSubgroup) (hcore : K.fixingSubgroup ≤ input.core)

/-! ### `7` -/

theorem cap_two_eq : ((input.E.cap 2 : GB) : Ghat) = frob7 ^ 2 := rfl

include hker hcore in
theorem orderOf_res_frob7 : orderOf (Input.res K frob7) = 8 := by
  have h8 := res_cap_fourth input hker 2
  have h4 := res_cap_sq_ne_one input hcore 2
  rw [cap_two_eq, ← pow_mul, map_pow] at h8 h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 2) (by simpa using h4) (by simpa using h8)

include hker hcore in
theorem image_cards_7 :
    Nat.card (inertiaRestriction prime7 K (jK K)).range = 1 ∧
      Nat.card (decompositionRestriction prime7 K (jK K)).range = 8 := by
  constructor
  · have hb : (inertiaRestriction prime7 K (jK K)).range = ⊥ := by
      apply le_antisymm _ bot_le
      rintro _ ⟨σ, rfl⟩
      rw [Subgroup.mem_bot, inertiaRestriction_eq, inertia_killed prime7 seven_not_mem σ,
        map_one]
    rw [hb, Subgroup.card_bot]
  · have hr := decomposition7_range' (Input.res K)
    rw [decompositionRestriction_eq_comp]
    change Nat.card ((Input.res K).comp (decompositionMap prime7)).toMonoidHom.range = 8
    rw [hr, Nat.card_zpowers]
    exact orderOf_res_frob7 hker hcore

end Seven

/-! ### The five witness primes -/

/-- Version 1's witness primes `2, 3, 5, 29, 7` (the data of version 1's `Witness`; version 2's
`Witness` has `41` in place of `7`). -/
def v1Primes : Fin 5 → ℕ := ![2, 3, 5, 29, 7]

/-- Version 1's absolute ramification indices at `v1Primes`. -/
def v1Ramification : Fin 5 → ℕ := ![8, 2, 2, 1, 1]

/-- Version 1's absolute residue degrees at `v1Primes`. -/
def v1ResidueDegree : Fin 5 → ℕ := ![4, 2, 2, 4, 8]

/-- The five version-1 witness primes as `Nat.Primes`: `2, 3, 5, 29, 7`. -/
def selectedPrime : Fin 5 → Nat.Primes :=
  ![prime2, tamePrime (tameK 0), tamePrime (tameK 2), prime29, prime7]

theorem selectedPrime_val (a : Fin 5) : (selectedPrime a).val = v1Primes a := by
  fin_cases a <;> rfl

section Types

variable {K : IntermediateField ℚ Omega} [FiniteDimensional ℚ K] [IsGalois ℚ K]
  (hker : input.kernelHat ≤ K.fixingSubgroup) (hcore : K.fixingSubgroup ≤ input.core)

include hker hcore in
/-- **Exact local image cardinalities** at the five witness primes. -/
theorem admissible_local_image_cards (a : Fin 5) :
    Nat.card (inertiaRestriction (selectedPrime a) K (jK K)).range = v1Ramification a ∧
      Nat.card (decompositionRestriction (selectedPrime a) K (jK K)).range =
        v1Ramification a * v1ResidueDegree a := by
  have hker' := inputSym_kernelHat_le.trans hker
  have hcore' : K.fixingSubgroup ≤ inputSym.core := hcore.trans inputSym_core.ge
  fin_cases a
  · exact image_cards_2 hker' hcore'
  · exact tame_image_cards hker' hcore' 0
  · exact tame_image_cards hker' hcore' 2
  · exact image_cards_29 hker' hcore'
  · exact image_cards_7 hker hcore

include hker hcore in
/-- **Exact local types** `(e, f)` at `2, 3, 5, 29, 7`. -/
theorem admissible_ramification_residue (a : Fin 5) :
    (NumberFieldAnalysis.rationalPrimeIdeal (v1Primes a)).ramificationIdxIn (𝓞 K) =
        v1Ramification a ∧
      (NumberFieldAnalysis.rationalPrimeIdeal (v1Primes a)).inertiaDegIn (𝓞 K) =
        v1ResidueDegree a := by
  rw [← selectedPrime_val]
  have h := admissible_local_image_cards hker hcore a
  exact ramification_residue_of_absolute_image_cards (selectedPrime a) K (jK K) _ _
    (by fin_cases a <;> decide) h.1 h.2

end Types

section SymTypes

variable {K : IntermediateField ℚ Omega} [FiniteDimensional ℚ K] [IsGalois ℚ K]
  (hker : inputSym.kernelHat ≤ K.fixingSubgroup) (hcore : K.fixingSubgroup ≤ input.core)

include hker hcore in
/-- **Exact local image cardinalities at `2, 3, 5, 29`** for every finite Galois `K` with
`inputSym.kernelHat ≤ Gal(Ω/K) ≤ core`. -/
theorem sym_local_image_cards (a : Fin 4) :
    Nat.card (inertiaRestriction (selectedPrime a.castSucc) K (jK K)).range =
        v1Ramification a.castSucc ∧
      Nat.card (decompositionRestriction (selectedPrime a.castSucc) K (jK K)).range =
        v1Ramification a.castSucc * v1ResidueDegree a.castSucc := by
  have hcore' : K.fixingSubgroup ≤ inputSym.core := hcore.trans inputSym_core.ge
  fin_cases a
  · exact image_cards_2 hker hcore'
  · exact tame_image_cards hker hcore' 0
  · exact tame_image_cards hker hcore' 2
  · exact image_cards_29 hker hcore'

include hker hcore in
/-- **Exact local types** `(e, f)` at `2, 3, 5, 29` for every finite Galois `K` with
`inputSym.kernelHat ≤ Gal(Ω/K) ≤ core`. -/
theorem sym_ramification_residue (a : Fin 4) :
    (NumberFieldAnalysis.rationalPrimeIdeal (v1Primes a.castSucc)).ramificationIdxIn (𝓞 K) =
        v1Ramification a.castSucc ∧
      (NumberFieldAnalysis.rationalPrimeIdeal (v1Primes a.castSucc)).inertiaDegIn (𝓞 K) =
        v1ResidueDegree a.castSucc := by
  rw [← selectedPrime_val]
  have h := sym_local_image_cards hker hcore a
  exact ramification_residue_of_absolute_image_cards (selectedPrime a.castSucc) K (jK K) _ _
    (by fin_cases a <;> decide) h.1 h.2

end SymTypes

namespace Input

theorem Admissible.local_types {K : IntermediateField ℚ Omega} (hK : input.Admissible K)
    (a : Fin 5) :
    haveI := hK.finiteDimensional
    haveI := hK.isGalois
    (NumberFieldAnalysis.rationalPrimeIdeal (v1Primes a)).ramificationIdxIn (𝓞 K) =
        v1Ramification a ∧
      (NumberFieldAnalysis.rationalPrimeIdeal (v1Primes a)).inertiaDegIn (𝓞 K) =
        v1ResidueDegree a := by
  have := hK.finiteDimensional
  have := hK.isGalois
  exact admissible_ramification_residue hK.kernelHat_le hK.fixing_le_core a

end Input

end UnitDistance.Sqrt241.Retained
