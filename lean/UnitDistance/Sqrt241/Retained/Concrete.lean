module

public import UnitDistance.Sqrt241.Retained.Basic
public import UnitDistance.Sqrt241.Local.Elements

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The concrete input: the local elements of `G_B`

`Retained.input : Retained.Input` with `E = Local.localElements`, all fields from `Local/`
(`Local/Elements.lean`: relations, labels, `σ̂`-relations `tame_sigma`,
`dyadicLocal_sigma`, `frob29_sigma`; `Local.coe_conj₂`, `Local.frob7_not_mem`,
`Local.conj₁_isConj`). Everything downstream is therefore unconditional.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation _root_.UnitDistance.Sqrt241.Local

/-- `s = h σ̂` turns the form `x₂ = h (σ̂ x₁ σ̂⁻¹) h⁻¹` of the `σ̂`-relations of `Local/` into
`x₂ = s x₁ s⁻¹`, `s σ̂⁻¹ ∈ G_B`. -/
theorem conj_form {h x y : Ghat} (hx : y = h * (sigmaHat * x * sigmaHat⁻¹) * h⁻¹) :
    y = (h * sigmaHat) * x * (h * sigmaHat)⁻¹ := by
  rw [hx]
  group

theorem mul_sigma_inv_mem {h : Ghat} (hh : h ∈ GB) : h * sigmaHat * sigmaHat⁻¹ ∈ GB := by
  simpa using hh

theorem sigma_mul_inv_mem_of_not_mem {F : Ghat} (hF : F ∉ GB) : sigmaHat * F⁻¹ ∈ GB := by
  rcases mem_GB_or_inv_mul_mem F with h | h
  · exact absurd h hF
  · have h1 : F⁻¹ * sigmaHat ∈ GB := by simpa using GB.inv_mem h
    have h2 := GB_normal.conj_mem _ h1 sigmaHat
    simpa [mul_assoc] using h2

/-- **The concrete input** (`Local.localElements`). -/
def input : Input where
  E := localElements
  relations := localElements_relations
  labels := localElements_labels
  conj_compat := coe_conj₂
  tame_compat_q := by
    obtain ⟨h, hh, h1, h2⟩ := tame_sigma 0
    exact ⟨h * sigmaHat, mul_sigma_inv_mem hh, conj_form h1, conj_form h2⟩
  tame_compat_r := by
    obtain ⟨h, hh, h1, h2⟩ := tame_sigma 1
    exact ⟨h * sigmaHat, mul_sigma_inv_mem hh, conj_form h1, conj_form h2⟩
  dyadic_compat := by
    obtain ⟨h, hh, hrel⟩ := dyadicLocal_sigma
    exact ⟨h * sigmaHat, mul_sigma_inv_mem hh, fun g => conj_form (hrel g)⟩
  cap_compat := by
    obtain ⟨h, hh, hrel⟩ := frob29_sigma
    exact ⟨h * sigmaHat, mul_sigma_inv_mem hh, conj_form hrel⟩
  frob7_compat := Or.inl ⟨frob7, rfl, sigma_mul_inv_mem_of_not_mem frob7_not_mem⟩
  phi := phi₁
  conj_isConj := conj₁_isConj

@[simp] theorem input_E : input.E = localElements := rfl

/-! ### Version 2: the symmetric cut without a cap at `7` -/

/-- The local elements with the third cap `F₇²` replaced by a second copy of `Frob(29₁)`: their
cut consists of version 1's cut words at `2, 3, 5` and both primes above `29`, and no cap at
`7`. It is contained both in version 1's cut and in version 2's cut with the cap at `41`.
(The fields are written out, not copied from `localElements`, so that no kernel check has to
compare the two third caps.) -/
def localElementsSym : LocalElements where
  conj := ![conj₁, conj₂]
  tameInertia := tameInertia
  tameFrobenius := tameFrobenius
  dyadic := dyadicLocal
  cap := ![frob29 0, frob29 1, frob29 0]

theorem localElementsSym_relations : localElementsSym.Relations where
  conj_sq k := by
    fin_cases k
    · exact conj₁_sq
    · exact conj₂_sq
  tame q := by
    rw [← tameN_eq_tameNorm]
    exact tame_relation q

theorem localElementsSym_labels : localElementsSym.Labels where
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
    have h0 : genusLabel (frob29 0) = Multiplicative.ofAdd (GroupData.capVector 0) :=
      (genusLabel_of_hasLabelHat _ _ (frob29_hasLabel 0)).trans (congrArg _ rfl)
    have h1 : genusLabel (frob29 1) = Multiplicative.ofAdd (GroupData.capVector 1) :=
      (genusLabel_of_hasLabelHat _ _ (frob29_hasLabel 1)).trans (congrArg _ rfl)
    fin_cases k
    · change CapGood (genusLabel (frob29 0)).toAdd
      rw [h0]; exact capVector_good 0
    · change CapGood (genusLabel (frob29 1)).toAdd
      rw [h1]; exact capVector_good 1
    · change CapGood (genusLabel (frob29 0)).toAdd
      rw [h0]; exact capVector_good 0

/-- **The symmetric input** (version 2): version 1's `input` with the cap at `7` replaced by a
second copy of `Frob(29₁)`. -/
def inputSym : Input where
  E := localElementsSym
  relations := localElementsSym_relations
  labels := localElementsSym_labels
  conj_compat := coe_conj₂
  tame_compat_q := by
    obtain ⟨h, hh, h1, h2⟩ := tame_sigma 0
    exact ⟨h * sigmaHat, mul_sigma_inv_mem hh, conj_form h1, conj_form h2⟩
  tame_compat_r := by
    obtain ⟨h, hh, h1, h2⟩ := tame_sigma 1
    exact ⟨h * sigmaHat, mul_sigma_inv_mem hh, conj_form h1, conj_form h2⟩
  dyadic_compat := by
    obtain ⟨h, hh, hrel⟩ := dyadicLocal_sigma
    exact ⟨h * sigmaHat, mul_sigma_inv_mem hh, fun g => conj_form (hrel g)⟩
  cap_compat := by
    obtain ⟨h, hh, hrel⟩ := frob29_sigma
    exact ⟨h * sigmaHat, mul_sigma_inv_mem hh, conj_form hrel⟩
  frob7_compat := Or.inr rfl
  phi := phi₁
  conj_isConj := conj₁_isConj

theorem inputSym_E : inputSym.E = localElementsSym := rfl

end UnitDistance.Sqrt241.Retained
