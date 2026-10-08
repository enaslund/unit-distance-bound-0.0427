module

public import UnitDistance.Sqrt241.Presentation.LocalLifts
public import UnitDistance.Sqrt241.Local.Caps
public import UnitDistance.Sqrt241.Local.Complex
public import UnitDistance.Sqrt241.Local.DyadicCut
public import UnitDistance.Sqrt241.Local.CapRanges

@[expose] public section
set_option backward.privateInPublic true

/-!
# The local elements of `G_B` as a `Presentation.LocalElements`

`localElements` fills the structure `Presentation.LocalElements` with the local elements:
`c₁, c₂` (`Complex.lean`), the tame pairs at `𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂` (`TamePairs.lean`), the
normalized dyadic local maps at `𝔭₁, 𝔭₂` (`Maps.lean`) and the caps `Frob(29₁)`,
`Frob(29₂)`, `F₇²` (`Caps.lean`). `localElements_relations` and `localElements_labels`
are the facts the presentation needs; with them `Presentation/` gives
`LocalElements.relators_generate` and `LocalElements.presentation`
(`localElements_presentation` below).

Labels are converted from `HasLabelHat` (`Maps.lean`) to the genus label `Tower.genusLabel`
by `genusLabel_of_hasLabelHat` (using `Tower.canonicalGenus_le_Omega`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Local

open Tower GroupData Presentation Multiquadratic CanonicalGenus

/-- Labels `HasLabelHat` give genus labels `genusLabel`. -/
theorem genusLabel_of_hasLabelHat (g : GB) (v : Fin 8 → ZMod 2) (hg : HasLabelHat (g : Ghat) v) :
    genusLabel g = Multiplicative.ofAdd v :=
  genusLabel_eq_of_action g v (fun k => hg.apply_genusRoot canonicalGenus_le_Omega k)

theorem bits_eq_binaryVector (m : ℕ) : GroupData.bits 8 m = RetainedQuadratic.binaryVector 8 m :=
  rfl

/-- **The local elements of `G_B`.** -/
def localElements : LocalElements where
  conj := ![conj₁, conj₂]
  tameInertia := tameInertia
  tameFrobenius := tameFrobenius
  dyadic := dyadicLocal
  cap := ![frob29 0, frob29 1, ⟨frob7 ^ 2, frob7_sq_mem⟩]

theorem tameN_eq_tameNorm (q : Fin 4) : tameN q = tameNorm q := by fin_cases q <;> rfl

theorem localElements_relations : localElements.Relations where
  conj_sq k := by
    fin_cases k
    · exact conj₁_sq
    · exact conj₂_sq
  tame q := by
    rw [← tameN_eq_tameNorm]
    exact tame_relation q

/-- The genus labels of the three caps: `00100111`, `00011011`, `01110000`. -/
theorem localElements_cap_label (k : Fin 3) :
    genusLabel (localElements.cap k) = Multiplicative.ofAdd (capVector k) := by
  fin_cases k
  · exact (genusLabel_of_hasLabelHat _ _ (frob29_hasLabel 0)).trans (congrArg _ rfl)
  · exact (genusLabel_of_hasLabelHat _ _ (frob29_hasLabel 1)).trans (congrArg _ rfl)
  · exact (genusLabel_of_hasLabelHat ⟨frob7 ^ 2, frob7_sq_mem⟩ _ frob7_sq_hasLabel).trans
      (congrArg _ rfl)

theorem localElements_labels : localElements.Labels where
  conj k := by
    fin_cases k
    · exact genusLabel_of_hasLabelHat _ _ conj₁_hasLabel
    · exact genusLabel_of_hasLabelHat _ _ conj₂_hasLabel
  tameInertia q := by
    exact (genusLabel_of_hasLabelHat _ _ (tameInertia_hasLabel q)).trans
      (congrArg _ (by fin_cases q <;> rfl))
  tameFrobenius q := by
    exact (genusLabel_of_hasLabelHat _ _ (tameFrobenius_hasLabel q)).trans
      (congrArg _ (by fin_cases q <;> rfl))
  dyadicA P := by
    exact (genusLabel_of_hasLabelHat _ _ (dyadicLocal_generator_hasLabel P 0)).trans
      (congrArg _ (by fin_cases P <;> rfl))
  dyadicB P := by
    exact (genusLabel_of_hasLabelHat _ _ (dyadicLocal_generator_hasLabel P 1)).trans
      (congrArg _ (by fin_cases P <;> rfl))
  dyadicC P := by
    exact (genusLabel_of_hasLabelHat _ _ (dyadicLocal_generator_hasLabel P 2)).trans
      (congrArg _ (by fin_cases P <;> rfl))
  cap k := by
    rw [localElements_cap_label k]
    exact capVector_good k

/-- **The seven relators normally generate the relation kernel** (for `localElements`). -/
theorem localElements_relators_generate :
    ProCGroups.Presentations.closedNormalClosure
        (Set.range (localElements.sourceLifts.relators genuineRelation)) =
      (relationKernel : Subgroup Free) :=
  LocalElements.relators_generate localElements_relations localElements_labels

/-- **The presentation hypothesis of the cut**, unconditional. -/
theorem localElements_presentation : localElements.sourceLifts.Presentation genuineRelation :=
  LocalElements.presentation localElements_relations localElements_labels

/-! ## Convenience: the split primes indexed by `Fin 4`, conjugation by `σ̂` -/

/-- The prime of `B` below the chosen place above `splitPrime k` (`k = 2, 3, 5, 29`). -/
def placeIndex : Fin 4 → Fin 2 := ![dyadicPlace, place3, place5, place29]

/-- The normalized local map at the prime `P` of `B` above `splitPrime k`. -/
def localMap (k : Fin 4) (P : Fin 2) : UnitDistance.PrimeCompletion.AbsoluteDecomposition (splitPrime k) →ₜ* GB :=
  localMapB (splitPrime k) (isSquare_241 k) (placeIndex k) P

/-- The second-prime map is a `G_B`-conjugate of the `σ̂`-conjugate of the first-prime map. -/
theorem localMapB_sigma (p : Nat.Primes) (hsq : IsSquare (241 : ℚ_[p.val])) (P₀ : Fin 2) :
    ∃ h ∈ GB, ∀ d, (localMapB p hsq P₀ 1 d : Ghat) =
      h * (sigmaHat * (localMapB p hsq P₀ 0 d : Ghat) * sigmaHat⁻¹) * h⁻¹ := by
  rcases Fin.exists_fin_two.mp ⟨P₀, rfl⟩ with h0 | h1
  · subst h0
    refine ⟨1, GB.one_mem, fun d => ?_⟩
    rw [coe_localMapB, coe_localMapB, frame_self, frame_ne (by decide)]
    group
  · subst h1
    refine ⟨(sigmaHat ^ 2)⁻¹, GB.inv_mem sigmaHat_sq_mem, fun d => ?_⟩
    rw [coe_localMapB, coe_localMapB, frame_self, frame_ne (by decide)]
    group

/-- **`genusLabel` and conjugation by `σ̂`**: labels are transformed by `sigmaMatrix`. -/
theorem genusLabel_conj (g : GB) :
    genusLabel (conjGB sigmaHat g) = Multiplicative.ofAdd (sigmaMatrix (genusLabel g).toAdd) := by
  obtain ⟨σ, hσ⟩ := toGhat_surjective (g : Ghat)
  have hl : HasLabel σ (genusLabel g).toAdd := by
    intro k
    have h := genusLabel_action g k
    rw [← hσ, toGhat_apply] at h
    exact h
  exact genusLabel_of_hasLabelHat _ _ (HasLabelHat.conj_sigmaHat ⟨σ, hσ, hl⟩)

theorem dyadicLocal_projection_eq (P : Fin 2) (σ : PadicTwoMaximalProTwo.AbsoluteGroup) :
    dyadicLocal P (PadicTwoMaximalProTwo.projection σ) =
      localMapB prime2 isSquare_241_two dyadicPlace P (PadicTwoGlobalMap.decomposition σ) := rfl

/-- `σ̂`-relation for the dyadic maps: `𝔭₂`-data are `G_B`-conjugates of `σ̂`-conjugates of
`𝔭₁`-data, uniformly. -/
theorem dyadicLocal_sigma : ∃ h ∈ GB, ∀ g : PadicTwoMaximalProTwo.Group,
    (dyadicLocal 1 g : Ghat) = h * (sigmaHat * (dyadicLocal 0 g : Ghat) * sigmaHat⁻¹) * h⁻¹ := by
  obtain ⟨h, hh, hrel⟩ := localMapB_sigma prime2 isSquare_241_two dyadicPlace
  refine ⟨h, hh, fun g => ?_⟩
  obtain ⟨σ, rfl⟩ := PadicTwoMaximalProTwo.projection_surjective g
  rw [dyadicLocal_projection_eq, dyadicLocal_projection_eq]
  exact hrel _

/-- `σ̂`-relation for the tame pairs at `𝔮₂`, `𝔯₂`. -/
theorem tame_sigma (k : Fin 2) : ∃ h ∈ GB,
    (tameInertia (tameIndex k 1) : Ghat) =
      h * (sigmaHat * (tameInertia (tameIndex k 0) : Ghat) * sigmaHat⁻¹) * h⁻¹ ∧
    (tameFrobenius (tameIndex k 1) : Ghat) =
      h * (sigmaHat * (tameFrobenius (tameIndex k 0) : Ghat) * sigmaHat⁻¹) * h⁻¹ := by
  fin_cases k
  · obtain ⟨h, hh, hrel⟩ := localMapB_sigma (tamePrime 0) (tameIsSquare 0) (tamePlace 0)
    exact ⟨h, hh, hrel _, hrel _⟩
  · obtain ⟨h, hh, hrel⟩ := localMapB_sigma (tamePrime 1) (tameIsSquare 1) (tamePlace 1)
    exact ⟨h, hh, hrel _, hrel _⟩

/-- `σ̂`-relation for `Frob(29₂)`. -/
theorem frob29_sigma : ∃ h ∈ GB,
    (frob29 1 : Ghat) = h * (sigmaHat * (frob29 0 : Ghat) * sigmaHat⁻¹) * h⁻¹ := by
  obtain ⟨h, hh, hrel⟩ := localMapB_sigma prime29 isSquare_241_29 place29
  exact ⟨h, hh, hrel _⟩

end UnitDistance.Sqrt241.Local
