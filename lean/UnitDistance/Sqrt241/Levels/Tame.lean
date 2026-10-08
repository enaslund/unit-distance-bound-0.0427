module

public import UnitDistance.Sqrt241.Levels.Restriction
public import UnitDistance.Sqrt241.Retained.Sym
public import UnitDistance.Sqrt241.GroupData.LocalModels
public import UnitDistance.ProfiniteGeneratedTameFiniteImage
public import UnitDistance.OddLocalRetainedImage

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Local images at the tame primes `3` and `5`

For a `K` admissible for the symmetric input `inputSym` (`inputSym.kernelHat ≤ Gal(Ω/K) ≤ core`;
`Retained/Sym.lean`: every field admissible for version 1's `input` is, and so is the Galois
closure of every version 2 level) and a tame place `q`
(`𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂`), with `t, f` the restrictions to `K` of the tame pair `τ_q, φ_q`
(`Local.tameInertia q`, `Local.tameFrobenius q`):

* upper bounds from the cut words `τ_q², φ_q²` and the tame relation
  `φτφ⁻¹ = τ^N` (`N` odd): `t² = f² = 1`, `t f = f t`;
* lower bounds from the genus labels (`τ_q, φ_q` have independent elementary vectors,
  and `Gal(Ω/K) ≤ core` preserves labels): `C₂ × C₂ → Gal(K/ℚ)`, `(a, b) ↦ tᵃ fᵇ`
  is injective;
* `Local.tame_generates`: the inertia image is `⟨t⟩`, the decomposition image is
  `⟨t, f⟩`.

Hence the images have cardinalities `2` and `4`, and at the rational primes `3`
(`q = 𝔮₁`) and `5` (`q = 𝔯₁`) the ℚ package's absolute restriction maps have images
of cardinalities `e = 2` and `e f = 4` (the normalized maps are conjugates of the
unnormalized ones).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation Cut GroupData ProCGroups UnitDistance.PrimeCompletion
open _root_.UnitDistance.Sqrt241.Local OddLocal RetainedCyclic

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ### Cut words at the tame places -/

theorem tameInertia_sq_word (q : Fin 4) :
    inputSym.A.tameInertia q ^ 2 ∈ inputSym.A.lifts.words := by
  fin_cases q
  · exact Or.inl (Or.inl ⟨13, rfl⟩)
  · exact Or.inl (Or.inl ⟨14, rfl⟩)
  · exact Or.inl (Or.inl ⟨15, rfl⟩)
  · exact Or.inl (Or.inl ⟨16, rfl⟩)

theorem tameFrobenius_sq_word (q : Fin 4) :
    inputSym.A.tameFrobenius q ^ 2 ∈ inputSym.A.lifts.words := by
  fin_cases q
  · exact Or.inl (Or.inl ⟨17, rfl⟩)
  · exact Or.inl (Or.inl ⟨18, rfl⟩)
  · exact Or.inl (Or.inl ⟨19, rfl⟩)
  · exact Or.inl (Or.inl ⟨20, rfl⟩)

theorem freeMap_tameInertia (q : Fin 4) : freeMap (inputSym.A.tameInertia q) = tameInertia q :=
  LocalElements.freeMap_lift _

theorem freeMap_tameFrobenius (q : Fin 4) :
    freeMap (inputSym.A.tameFrobenius q) = tameFrobenius q :=
  LocalElements.freeMap_lift _

section Images

variable {K : IntermediateField ℚ Omega} [FiniteDimensional ℚ K] [IsGalois ℚ K]
  (hker : inputSym.kernelHat ≤ K.fixingSubgroup) (hcore : K.fixingSubgroup ≤ inputSym.core)

include hker in
theorem resB_tameInertia_sq (q : Fin 4) : resB K (tameInertia q) ^ 2 = 1 := by
  have h := inputSym.res_eq_one_of_word hker (tameInertia_sq_word q)
  rw [map_pow, freeMap_tameInertia] at h
  rw [← map_pow]
  exact h

include hker in
theorem resB_tameFrobenius_sq (q : Fin 4) : resB K (tameFrobenius q) ^ 2 = 1 := by
  have h := inputSym.res_eq_one_of_word hker (tameFrobenius_sq_word q)
  rw [map_pow, freeMap_tameFrobenius] at h
  rw [← map_pow]
  exact h

theorem tameN_odd (q : Fin 4) : tameN q % 2 = 1 := by fin_cases q <;> rfl

include hker in
theorem resB_tame_commute (q : Fin 4) :
    Commute (resB K (tameInertia q)) (resB K (tameFrobenius q)) := by
  have h := congrArg (resB K) (tame_relation q)
  simp only [map_mul, map_inv, map_pow] at h
  rw [pow_eq_pow_mod _ (resB_tameInertia_sq hker q), tameN_odd, pow_one] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem tameInertia_label (q : Fin 4) :
    genusLabel (tameInertia q) = Multiplicative.ofAdd (tameInertiaVector q) :=
  inputSym.labels.tameInertia q

theorem tameFrobenius_label (q : Fin 4) :
    genusLabel (tameFrobenius q) = Multiplicative.ofAdd (tameFrobeniusVector q) :=
  inputSym.labels.tameFrobenius q

/-- The local map `C₂ × C₂ → Gal(K/ℚ)`. -/
def tameMapK (q : Fin 4) : D 0 →* Gal(K/ℚ) :=
  OddLocal.map 0 (resB K (tameInertia q)) (resB K (tameFrobenius q))
    (resB_tameInertia_sq hker q) (resB_tameFrobenius_sq hker q) (resB_tame_commute hker q)

theorem tameMapK_apply (q : Fin 4) (x : D 0) :
    tameMapK hker q x = resB K (tameInertia q) ^ x.1.toAdd.val *
      resB K (tameFrobenius q) ^ x.2.toAdd.val := by
  unfold tameMapK OddLocal.map
  rw [MonoidHom.noncommCoprod_apply, cyclicMap_pow_val, cyclicMap_pow_val]

theorem val_lt_two_cases (a : ℕ) (ha : a < 2) (h : (a : GroupData.F) = 0) : a = 0 := by
  rcases (show a = 0 ∨ a = 1 by omega) with h0 | h1
  · exact h0
  · rw [h1] at h
    exact absurd h (by decide)

include hcore in
theorem tameMapK_injective (q : Fin 4) : Function.Injective (tameMapK hker q) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  intro x hx
  change tameMapK hker q x = 1 at hx
  rw [tameMapK_apply, ← map_pow, ← map_pow, ← map_mul] at hx
  have hl := inputSym.genusLabel_eq_of_resB_eq hcore (hx.trans (map_one (resB K)).symm)
  rw [map_mul, map_pow, map_pow, tameInertia_label, tameFrobenius_label, map_one] at hl
  have hv : x.1.toAdd.val • tameInertiaVector q + x.2.toAdd.val • tameFrobeniusVector q = 0 := by
    have := congrArg Multiplicative.toAdd hl
    simpa using this
  have h1 := ZMod.val_lt x.1.toAdd
  have h2 : x.2.toAdd.val < 2 := ZMod.val_lt (n := 2) x.2.toAdd
  have hcast (k : ℕ) (v : Fin 8 → GroupData.F) : k • v = (k : GroupData.F) • v := by
    rw [Nat.cast_smul_eq_nsmul]
  rw [hcast, hcast] at hv
  obtain ⟨ha, hb⟩ := LocalModels.tame_independent_certificate q _ _ hv
  have ha' := val_lt_two_cases _ h1 ha
  have hb' := val_lt_two_cases _ h2 hb
  apply Prod.ext
  · rw [cyclic_pow_val 2 x.1, ha', pow_zero]
    rfl
  · change x.2 = 1
    have hx2 : x.2 = cyclicGenerator 2 ^ x.2.toAdd.val := cyclic_pow_val 2 x.2
    rw [hx2, hb', pow_zero]

include hker hcore in
theorem card_closure_tame (q : Fin 4) :
    Nat.card (Subgroup.closure ({resB K (tameInertia q), resB K (tameFrobenius q)} :
      Set Gal(K/ℚ))) = 4 := by
  classical
  rw [← OddLocal.map_range 0 _ _ (resB_tameInertia_sq hker q) (resB_tameFrobenius_sq hker q)
    (resB_tame_commute hker q)]
  change Nat.card (tameMapK hker q).range = 4
  rw [Nat.card_eq_fintype_card, Fintype.card_coeSort_range (tameMapK_injective hker hcore q),
    ← Nat.card_eq_fintype_card, OddLocal.card]
  rfl

include hcore in
theorem resB_tameInertia_ne_one (q : Fin 4) : resB K (tameInertia q) ≠ 1 := by
  intro h
  have hl := inputSym.genusLabel_eq_of_resB_eq hcore (h.trans (map_one (resB K)).symm)
  rw [tameInertia_label, map_one] at hl
  have hv : tameInertiaVector q = 0 := congrArg Multiplicative.toAdd hl
  have hc := LocalModels.tame_independent_certificate q 1 0 (by rw [hv]; simp)
  exact absurd hc.1 (by decide)

include hker hcore in
theorem orderOf_resB_tameInertia (q : Fin 4) : orderOf (resB K (tameInertia q)) = 2 :=
  orderOf_eq_prime (resB_tameInertia_sq hker q) (resB_tameInertia_ne_one hcore q)

/-! ### Images of the normalized local maps -/

theorem tame_image_generates (q : Fin 4) :
    (∀ x, ∃ n : ℤ, resB K (tameInertiaMap q x) = resB K (tameInertia q) ^ n) ∧
    (∀ y, resB K (tameDecompositionMap q y) ∈
      Subgroup.closure ({resB K (tameInertia q), resB K (tameFrobenius q)} : Set Gal(K/ℚ))) :=
  ProfiniteTame.discrete_image_generates (tameInertiaMap q) (tameDecompositionMap q)
    (tameInertia q) (tameFrobenius q) (tame_generates q) (resB K)

theorem tame_decomposition_range (q : Fin 4) :
    ((resB K).toMonoidHom.comp (tameDecompositionMap q).toMonoidHom).range =
      Subgroup.closure ({resB K (tameInertia q), resB K (tameFrobenius q)} : Set Gal(K/ℚ)) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact (tame_image_generates (K := K) q).2 y
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨(tameInertiaAbs (tameK q)).val, rfl⟩
    · exact ⟨tameFrobeniusAbs (tameK q), rfl⟩

theorem tame_inertia_range (q : Fin 4) :
    ((resB K).toMonoidHom.comp (tameInertiaMap q).toMonoidHom).range =
      Subgroup.zpowers (resB K (tameInertia q)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨n, hn⟩ := (tame_image_generates (K := K) q).1 x
    exact ⟨n, hn.symm⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨tameInertiaAbs (tameK q), rfl⟩

include hker hcore in
theorem card_tame_decomposition_range (q : Fin 4) :
    Nat.card ((resB K).toMonoidHom.comp (tameDecompositionMap q).toMonoidHom).range = 4 := by
  rw [tame_decomposition_range, card_closure_tame hker hcore]

include hker hcore in
theorem card_tame_inertia_range (q : Fin 4) :
    Nat.card ((resB K).toMonoidHom.comp (tameInertiaMap q).toMonoidHom).range = 2 := by
  rw [tame_inertia_range, Nat.card_zpowers, orderOf_resB_tameInertia hker hcore]

end Images

end UnitDistance.Sqrt241.Retained
