module

public import UnitDistance.SIntegerCRTValuations
public import UnitDistance.SIntegerCRTApproximation

@[expose] public section
set_option backward.privateInPublic true


/-! # The actual fractional ideal determined by a rectangular finite period -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain WithZero

namespace UnitDistance.SIntegerCRT

open RelativeIdealCosets

variable {K : Type} [Field K] [NumberField K]
  {T : Type*} [Fintype T]

def primeIdealUnit (v : HeightOneSpectrum (𝓞 K)) : IdealGroup K :=
  FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩

@[simp] theorem primeIdealUnit_coe (v : HeightOneSpectrum (𝓞 K)) :
    (primeIdealUnit v : FractionalIdeal (𝓞 K)⁰ K) = v.asIdeal := rfl

/-- The literal fractional ideal associated to arbitrary signed local period exponents. -/
def periodIdeal (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) : IdealGroup K :=
  ∏ t, primeIdealUnit (P t) ^ a t

theorem idealCountHom_primeIdealUnit (v w : HeightOneSpectrum (𝓞 K)) :
    idealCountHom v (primeIdealUnit w) = Multiplicative.ofAdd (if w = v then 1 else 0) :=
  congrArg Multiplicative.ofAdd (FractionalIdeal.count_maximal K v w)

theorem periodIdeal_count (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (periodIdeal P a).val = ∑ t, if P t = v then a t else 0 := by
  change Multiplicative.toAdd (idealCountHom v (periodIdeal P a)) = _
  simp [periodIdeal, map_prod, map_zpow, idealCountHom_primeIdealUnit, mul_ite]

theorem periodIdeal_count_selected (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) (a : T → ℤ) (t : T) :
    FractionalIdeal.count K (P t) (periodIdeal P a).val = a t := by
  simp [periodIdeal_count, hP.eq_iff]

theorem periodIdeal_count_outside (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ Set.range P) :
    FractionalIdeal.count K v (periodIdeal P a).val = 0 := by
  have hn (t : T) : P t ≠ v := fun h ↦ hv ⟨t, h⟩
  simp [periodIdeal_count, hn]

/-- The actual product of the selected finite-place completions. -/
abbrev LocalProduct (P : T → HeightOneSpectrum (𝓞 K)) := ∀ t, (P t).adicCompletion K

/-- The actual diagonal finite embedding of the field. -/
def localEmbedding (P : T → HeightOneSpectrum (𝓞 K)) : K →+* LocalProduct P :=
  RingHom.pi fun t ↦ algebraMap K ((P t).adicCompletion K)

@[simp] theorem localEmbedding_apply (P : T → HeightOneSpectrum (𝓞 K)) (x : K) (t : T) :
    localEmbedding P x t = algebraMap K ((P t).adicCompletion K) x := rfl

/-- The rectangular compact open additive period, in actual local valuations. -/
def finitePeriod (P : T → HeightOneSpectrum (𝓞 K)) (a : T → ℤ) :
    AddSubgroup (LocalProduct P) where
  carrier := {x | ∀ t, Valued.v (x t) ≤ WithZero.exp (-a t)}
  zero_mem' := by intro t; simp
  add_mem' := by
    intro x y hx hy t
    exact (Valued.v : Valuation ((P t).adicCompletion K) ℤᵐ⁰).map_add_le (hx t) (hy t)
  neg_mem' := by intro x hx t; simpa using hx t

/-- The S-integers whose finite components lie in the specified rectangle
are exactly the actual fractional ideal with those prime exponents. -/
theorem mem_periodIdeal_iff (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) (a : T → ℤ) (x : K) :
    x ∈ (periodIdeal P a).val ↔
      x ∈ (Set.range P).integer K ∧ localEmbedding P x ∈ finitePeriod P a := by
  rw [mem_fractionalIdeal_iff_valuations _ (periodIdeal P a).ne_zero]
  constructor
  · intro h
    constructor
    · intro v hv
      simpa only [periodIdeal_count_outside P a v hv, neg_zero, WithZero.exp_zero] using h v
    · intro t
      change (Valued.v : Valuation ((P t).adicCompletion K) ℤᵐ⁰)
        (algebraMap K ((P t).adicCompletion K) x) ≤ _
      rw [valued_field]
      simpa only [periodIdeal_count_selected P hP] using h (P t)
  · rintro ⟨hx, hf⟩ v
    by_cases hv : v ∈ Set.range P
    · obtain ⟨t, rfl⟩ := hv
      rw [periodIdeal_count_selected P hP]
      simpa only [localEmbedding_apply, valued_field] using hf t
    · rw [periodIdeal_count_outside P a v hv, neg_zero, WithZero.exp_zero]
      exact hx v hv

/-- Every finite-period fiber through an actual S-integer is a translate of
the actual period fractional ideal. -/
theorem finitePeriod_fiber_iff (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) (a : T → ℤ) (y : K) (hy : y ∈ (Set.range P).integer K) (x : K) :
    (x ∈ (Set.range P).integer K ∧ localEmbedding P x - localEmbedding P y ∈ finitePeriod P a) ↔
      x - y ∈ (periodIdeal P a).val := by
  rw [mem_periodIdeal_iff P hP, map_sub]
  constructor
  · rintro ⟨hx, hf⟩
    exact ⟨((Set.range P).integer K).sub_mem hx hy, hf⟩
  · rintro ⟨hxy, hf⟩
    exact ⟨by simpa only [sub_add_cancel] using ((Set.range P).integer K).add_mem hxy hy, hf⟩

end UnitDistance.SIntegerCRT
