module

public import UnitDistance.Sqrt241.Base.SUnits
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup

@[expose] public section
set_option backward.privateInPublic true

/-!
# The set `S` and the `S`-Selmer group of `B`

* `S = {v | 30 ∈ v}`, the six primes above `2, 3, 5`; `sPlace : Fin 6 → HeightOneSpectrum`,
  `SFin` (a `Finset` with `mem_SFin_iff`, `SFin_card = 6`), and the named places
  `vP2, vP2', vP3, vP3', vP5, vP5'` (and `vP29, vP29'`).
* `alphaB i = radicandA i + radicandB i · √241 ∈ B` (the radicands of `CanonicalGenus`).
* `alpha_independent`: `∏ alphaB i ^ (w i).val` is a square only for `w = 0`
  (`w : Fin 8 → ZMod 2`).
* `mem_V_of_even_outside_S`: an `x ∈ Bˣ` with even valuation outside `S` is
  `∏ alphaB i ^ (w i).val · c²`.
* `CanonicalGenus.base_le_field : B ≤ CanonicalGenus.field`.
-/

noncomputable section

namespace UnitDistance.Sqrt241.Base

open NumberField IsDedekindDomain Ideal WithZero CanonicalGenus

/-- The six primes of `B` above `2, 3, 5`. -/
def S : Set (HeightOneSpectrum (𝓞 B)) := {v | (30 : 𝓞 B) ∈ v.asIdeal}

theorem mem_S {v : HeightOneSpectrum (𝓞 B)} : v ∈ S ↔ (30 : 𝓞 B) ∈ v.asIdeal := Iff.rfl

/-! ## The eight split places -/

/-- The place `𝔭₂ = (π₂)`. -/
def vP2 : HeightOneSpectrum (𝓞 B) := heightOneOf pi2 prime_pi2
/-- The place `𝔭₂' = (π₂')`. -/
def vP2' : HeightOneSpectrum (𝓞 B) := heightOneOf pi2' prime_pi2'
/-- The place `𝔭₃ = (π₃)`. -/
def vP3 : HeightOneSpectrum (𝓞 B) := heightOneOf pi3 prime_pi3
/-- The place `𝔭₃' = (π₃')`. -/
def vP3' : HeightOneSpectrum (𝓞 B) := heightOneOf pi3' prime_pi3'
/-- The place `𝔭₅ = (π₅)`. -/
def vP5 : HeightOneSpectrum (𝓞 B) := heightOneOf pi5 prime_pi5
/-- The place `𝔭₅' = (π₅')`. -/
def vP5' : HeightOneSpectrum (𝓞 B) := heightOneOf pi5' prime_pi5'
/-- The place `𝔭₂₉ = (π₂₉)`. -/
def vP29 : HeightOneSpectrum (𝓞 B) := heightOneOf pi29 prime_pi29
/-- The place `𝔭₂₉' = (π₂₉')`. -/
def vP29' : HeightOneSpectrum (𝓞 B) := heightOneOf pi29' prime_pi29'

@[simp] theorem vP2_asIdeal : vP2.asIdeal = P2 := rfl
@[simp] theorem vP2'_asIdeal : vP2'.asIdeal = P2' := rfl
@[simp] theorem vP3_asIdeal : vP3.asIdeal = P3 := rfl
@[simp] theorem vP3'_asIdeal : vP3'.asIdeal = P3' := rfl
@[simp] theorem vP5_asIdeal : vP5.asIdeal = P5 := rfl
@[simp] theorem vP5'_asIdeal : vP5'.asIdeal = P5' := rfl
@[simp] theorem vP29_asIdeal : vP29.asIdeal = P29 := rfl
@[simp] theorem vP29'_asIdeal : vP29'.asIdeal = P29' := rfl

/-- The six places of `S`: `sPlace j = (alpha (j + 2))`, i.e. `𝔭₂, 𝔭₂', 𝔭₃, 𝔭₃', 𝔭₅, 𝔭₅'`. -/
def sPlace (j : Fin 6) : HeightOneSpectrum (𝓞 B) :=
  primeS ⟨j.val + 2, by omega⟩ (by simp)

theorem sPlace_asIdeal (j : Fin 6) :
    (sPlace j).asIdeal = span {alpha ⟨j.val + 2, by omega⟩} := rfl

theorem sPlace_zero : sPlace 0 = vP2 := rfl
theorem sPlace_one : sPlace 1 = vP2' := rfl
theorem sPlace_two : sPlace 2 = vP3 := rfl
theorem sPlace_three : sPlace 3 = vP3' := rfl
theorem sPlace_four : sPlace 4 = vP5 := rfl
theorem sPlace_five : sPlace 5 = vP5' := rfl

theorem sPlace_injective : Function.Injective sPlace := by
  intro i j h
  have h1 : alpha ⟨i.val + 2, by omega⟩ ∈ (sPlace j).asIdeal := by
    rw [← h, sPlace_asIdeal]
    exact mem_span_singleton_self _
  rw [sPlace_asIdeal, alpha_mem_span_alpha_iff _ _ (by simp)] at h1
  apply Fin.ext
  have := congrArg Fin.val h1
  simp only at this
  omega

theorem sPlace_mem_S (j : Fin 6) : sPlace j ∈ S :=
  thirty_mem_span_alpha _ (by simp)

theorem mem_S_iff (v : HeightOneSpectrum (𝓞 B)) : v ∈ S ↔ ∃ j : Fin 6, v = sPlace j := by
  constructor
  · intro hv
    obtain ⟨i, hi, hvi⟩ := exists_alpha_of_thirty_mem (P := v.asIdeal) hv
    refine ⟨⟨i.val - 2, by omega⟩, ?_⟩
    apply HeightOneSpectrum.ext
    rw [hvi, sPlace_asIdeal]
    have hi' : i = ⟨(⟨i.val - 2, by omega⟩ : Fin 6).val + 2, by omega⟩ := by
      apply Fin.ext
      simp only
      omega
    rw [← hi']
  · rintro ⟨j, rfl⟩
    exact sPlace_mem_S j

theorem mem_S_iff' (v : HeightOneSpectrum (𝓞 B)) :
    v ∈ S ↔ v = vP2 ∨ v = vP2' ∨ v = vP3 ∨ v = vP3' ∨ v = vP5 ∨ v = vP5' := by
  rw [mem_S_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp [sPlace_zero, sPlace_one, sPlace_two, sPlace_three, sPlace_four,
      sPlace_five]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

/-- `S` as a `Finset`. -/
def SFin : Finset (HeightOneSpectrum (𝓞 B)) := Finset.univ.map ⟨sPlace, sPlace_injective⟩

theorem mem_SFin_iff (v : HeightOneSpectrum (𝓞 B)) : v ∈ SFin ↔ v ∈ S := by
  rw [mem_S_iff, SFin, Finset.mem_map]
  simp only [Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  exact ⟨fun ⟨j, hj⟩ ↦ ⟨j, hj.symm⟩, fun ⟨j, hj⟩ ↦ ⟨j, hj.symm⟩⟩

theorem SFin_card : SFin.card = 6 := by
  simp [SFin]

theorem S_finite : S.Finite := by
  have : S = (SFin : Set (HeightOneSpectrum (𝓞 B))) := by
    ext v
    rw [Finset.mem_coe, mem_SFin_iff]
  rw [this]
  exact SFin.finite_toSet

/-! ## The radicands in `B` -/

/-- The Kummer radicand `radicandA i + radicandB i · √241` as an element of `B`. -/
def alphaB (i : Fin 8) : B :=
  algebraMap ℚ B (radicandA i) + algebraMap ℚ B (radicandB i) * sqrt241

theorem alphaB_eq (i : Fin 8) : alphaB i = ((alpha i : 𝓞 B) : B) := (alpha_coords i).symm

theorem coe_alphaB (i : Fin 8) : (alphaB i : Closure) = radicand i := by
  rw [alphaB_eq, coe_alpha]

theorem alphaB_ne_zero (i : Fin 8) : alphaB i ≠ 0 := by
  rw [alphaB_eq]
  exact coe_ne_zero (alpha_ne_zero i)

theorem prod_alphaB_pow_val (w : Fin 8 → ZMod 2) :
    ∏ i, alphaB i ^ (w i).val = alphaProd (fun i ↦ (w i).val) := by
  simp only [alphaProd, alphaB_eq]

/-- **Independence.** A product of distinct radicands is not a square in `B`. -/
theorem alpha_independent (w : Fin 8 → ZMod 2)
    (h : IsSquare (∏ i, alphaB i ^ (w i).val)) : w = 0 := by
  rw [prod_alphaB_pow_val, isSquare_alphaProd_iff (fun i ↦ ZMod.val_lt (w i))] at h
  funext i
  have := congrFun h i
  simp only [Pi.zero_apply] at this
  exact (ZMod.val_eq_zero (w i)).mp this

theorem isSquare_valuation_iff_even (v : HeightOneSpectrum (𝓞 B)) (x : Bˣ) :
    IsSquare (v.valuation B (x : B)) ↔ Even (Multiplicative.toAdd (v.valuationOfNeZero x)) := by
  rw [← HeightOneSpectrum.valuationOfNeZero_eq]
  exact isSquare_exp_iff _

/-- **`S`-units modulo squares.** An element of `B^×` with even valuation at every prime outside
`S` is a product of radicands times a square. -/
theorem mem_V_of_even_outside_S (x : Bˣ)
    (h : ∀ v, v ∉ S → Even (Multiplicative.toAdd (v.valuationOfNeZero x))) :
    ∃ (w : Fin 8 → ZMod 2) (c : Bˣ), (x : B) = (∏ i, alphaB i ^ (w i).val) * c ^ 2 := by
  obtain ⟨e, he, γ, hγ, hx⟩ := sUnit_squareclass (x : B) x.ne_zero
    (fun v hv ↦ (isSquare_valuation_iff_even v x).mpr (h v hv))
  refine ⟨fun i ↦ (e i : ZMod 2), Units.mk0 γ hγ, ?_⟩
  rw [prod_alphaB_pow_val, Units.val_mk0, hx]
  congr 2
  funext i
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (he i)]

end UnitDistance.Sqrt241.Base

namespace UnitDistance.Sqrt241.CanonicalGenus

/-- `B = ℚ(√241)` lies in the canonical genus field `E`. -/
theorem base_le_field : Base.B ≤ CanonicalGenus.field := Base.B_le_field

end UnitDistance.Sqrt241.CanonicalGenus
