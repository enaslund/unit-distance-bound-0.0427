module

public import UnitDistance.SIntegerCRTBasic

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual simultaneous approximation of integral local targets by global integers -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain Set WithZero

namespace UnitDistance.SIntegerCRT

variable {K : Type} [Field K] [NumberField K]

@[simp] theorem valued_field (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (algebraMap K (v.adicCompletion K) x) = v.valuation K x := by
  simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply] using v.valuedAdicCompletion_eq_valuation' x

@[simp] theorem valued_integer (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (algebraMap (𝓞 K) (v.adicCompletion K) a) = v.intValuation a := by
  rw [v.valuedAdicCompletion_eq_valuation, v.valuation_of_algebraMap]

/-- Actual valued balls in the completion are open at every integer radius. -/
theorem local_open_ball (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) (n : ℤ) :
    IsOpen {z : v.adicCompletion K | Valued.v (z - x) < WithZero.exp n} := by
  obtain ⟨b, hb⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp n)
  have h := (Valued.isOpen_ball (v.adicCompletion K)
    ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict b)).preimage
      (continuous_id.sub continuous_const : Continuous (fun z : v.adicCompletion K ↦ z - x))
  simpa only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff, hb, Pi.sub_apply, id_eq] using h

/-- A local integer in an actual completion is approximated to arbitrary
prime-power precision by an actual global algebraic integer. -/
theorem exists_integer_approximation (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) (hx : Valued.v x ≤ (1 : ℤᵐ⁰)) (n : ℕ) :
    ∃ a : 𝓞 K, Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) a - x) <
      WithZero.exp (-(n : ℤ)) := by
  have hxball : x ∈ {z : v.adicCompletion K | Valued.v (z - x) < WithZero.exp (-(n : ℤ))} := by
    simp
  obtain ⟨y, hy⟩ := (v.denseRange_algebraMap K).mem_nhds
    ((local_open_ball v x _).mem_nhds hxball)
  have hr : WithZero.exp (-(n : ℤ)) ≤ (1 : ℤᵐ⁰) := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hyO : v.valuation K y ≤ 1 := by
    have hh := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_add_le
      (hy.le.trans hr) hx
    simpa only [sub_add_cancel, valued_field] using hh
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hyO
    (Units.mk0 (WithZero.exp (-(n : ℤ)) : ℤᵐ⁰) WithZero.exp_ne_zero)
  refine ⟨a, ?_⟩
  have ha' : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a - y)) <
        WithZero.exp (-(n : ℤ)) := by
    rw [valued_field]
    exact ha
  have hid : algebraMap (𝓞 K) (v.adicCompletion K) a - x =
      algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a - y) +
        (algebraMap K (v.adicCompletion K) y - x) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply]
    ring
  rw [hid]
  exact ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_add _ _).trans_lt (max_lt ha' hy)

variable {T : Type*} [Fintype T]

/-- Powers of distinct actual prime ideals are pairwise coprime. -/
theorem prime_powers_pairwise_coprime (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) (n : T → ℕ) :
    Pairwise (fun i j ↦ IsCoprime ((P i).asIdeal ^ n i) ((P j).asIdeal ^ n j)) := by
  intro i j hij
  letI := (P i).isMaximal
  letI := (P j).isMaximal
  apply IsCoprime.pow
  apply Ideal.isCoprime_of_isMaximal
  intro h
  exact hij (hP (HeightOneSpectrum.ext h))

/-- Ordinary ideal CRT simultaneously approximates integral targets in the
actual finite collection of completions. -/
theorem exists_simultaneous_integer_approximation (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) (x : ∀ t, (P t).adicCompletion K)
    (hx : ∀ t, Valued.v (x t) ≤ (1 : ℤᵐ⁰)) (n : T → ℕ) :
    ∃ a : 𝓞 K, ∀ t,
      Valued.v (algebraMap (𝓞 K) ((P t).adicCompletion K) a - x t) ≤ WithZero.exp (-(n t : ℤ)) := by
  choose a ha using fun t ↦ exists_integer_approximation (P t) (x t) (hx t) (n t)
  obtain ⟨b, hb⟩ := Ideal.pi_quotient_surjective (prime_powers_pairwise_coprime P hP n)
    (fun t ↦ Ideal.Quotient.mk ((P t).asIdeal ^ n t) (a t))
  refine ⟨b, fun t ↦ ?_⟩
  have hd : b - a t ∈ (P t).asIdeal ^ n t := Ideal.Quotient.eq.mp (hb t)
  have hv : (Valued.v : Valuation ((P t).adicCompletion K) ℤᵐ⁰)
      (algebraMap (𝓞 K) ((P t).adicCompletion K) b -
        algebraMap (𝓞 K) ((P t).adicCompletion K) (a t)) ≤ WithZero.exp (-(n t : ℤ)) := by
    rw [← map_sub, valued_integer]
    exact ((P t).intValuation_le_pow_iff_mem _ _).mpr hd
  have hid : algebraMap (𝓞 K) ((P t).adicCompletion K) b - x t =
      (algebraMap (𝓞 K) ((P t).adicCompletion K) b -
        algebraMap (𝓞 K) ((P t).adicCompletion K) (a t)) +
      (algebraMap (𝓞 K) ((P t).adicCompletion K) (a t) - x t) := by ring
  rw [hid]
  exact (Valued.v : Valuation ((P t).adicCompletion K) ℤᵐ⁰).map_add_le hv (ha t).le

end UnitDistance.SIntegerCRT
