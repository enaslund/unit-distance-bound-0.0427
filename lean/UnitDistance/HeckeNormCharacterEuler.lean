module

public import UnitDistance.HeckeSignedSeries
public import UnitDistance.DedekindEuler

@[expose] public section
set_option backward.privateInPublic true


/-! Actual ideal Euler product of the existing norm character modulo four.
Uses the factorization bijection and absolutely convergent geometric-product
machinery in `DedekindEuler`, originally adapted from Formal Frontier Team's
sum_product project (Apache-2.0; provenance retained in that module). -/
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Real Classical nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace UnitDistance.NumberFieldAnalysis
open UnitDistance.DedekindEuler
variable (K : Type*) [Field K] [NumberField K]

/-- The multiplicative coefficient at an ordinary natural norm. -/
def chiFourNormCpowHom (s : ℂ) : ℕ →* ℂ where
  toFun n := chiFourComplex n * (n : ℂ)^(-s)
  map_one' := by simp
  map_mul' m n := by
    rw [chiFourComplex_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring

/-- Multiplicativity along the actual prime factorization of an ideal. -/
theorem chiFour_absNorm_cpow_eq_finprod {I : Ideal (𝓞 K)} (hI : I ≠ 0) (s : ℂ) :
    chiFourComplex (Ideal.absNorm I)*(Ideal.absNorm I : ℂ)^(-s) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (chiFourComplex (Ideal.absNorm v.asIdeal)*(Ideal.absNorm v.asIdeal : ℂ)^(-s))^
          idealExp K I v := by
  let H : Ideal (𝓞 K) →* ℂ := (chiFourNormCpowHom s).comp Ideal.absNorm.toMonoidHom
  have hfin : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
      v.asIdeal^idealExp K I v) := by
    apply (finite_idealExp_support K hI).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    intro h
    exact hv (by rw [h, pow_zero])
  change H I = _
  conv_lhs => rw [← finprod_asIdeal_pow_idealExp K hI]
  rw [map_finprod H hfin]
  apply finprod_congr
  intro v
  rw [map_pow]
  rfl

/-- The two standard subtypes of nonzero integral ideals agree literally. -/
def nonzeroIdealEquivNonZeroDivisors : NonzeroIdeal K ≃ (Ideal (𝓞 K))⁰ :=
  Equiv.subtypeEquivRight (fun _ => mem_nonZeroDivisors_iff_ne_zero.symm)

/-- Unconditional Euler product of the ordinary mod-four norm-character ideal
series on its absolute-convergence half-plane. -/
theorem chiFourIdealSeries_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      (1-chiFourComplex (Ideal.absNorm v.asIdeal)*(Ideal.absNorm v.asIdeal : ℂ)^(-s))⁻¹)
      (chiFourIdealSeries K s) := by
  let g : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    chiFourComplex (Ideal.absNorm v.asIdeal)*(Ideal.absNorm v.asIdeal : ℂ)^(-s)
  have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 K) =>
      (⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩ : (Ideal (𝓞 K))⁰)) := by
    intro v w h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)
  have hsum : Summable (fun v => ‖g v‖) := by
    have hall : Summable (fun I : (Ideal (𝓞 K))⁰ =>
        ‖chiFourComplex (Ideal.absNorm (I : Ideal (𝓞 K))) *
          (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)^(-s)‖) :=
      (summable_chiFourIdealSeries K hs).norm
    have hcomp := hall.comp_injective (i := fun v : HeightOneSpectrum (𝓞 K) =>
      (⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩ : (Ideal (𝓞 K))⁰)) hinj
    exact hcomp
  have hg (v : HeightOneSpectrum (𝓞 K)) : ‖g v‖ < 1 := by
    have hn0 : 0 < Ideal.absNorm v.asIdeal :=
      Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
    have hn1 : 1 < Ideal.absNorm v.asIdeal := by
      have hne : Ideal.absNorm v.asIdeal ≠ 1 :=
        fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
      omega
    dsimp [g]
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
    calc
      _ ≤ 1*(Ideal.absNorm v.asIdeal : ℝ)^(-s.re) :=
        mul_le_mul_of_nonneg_right (norm_chiFourComplex_le_one _) (by positivity)
      _ < 1 := by
        rw [one_mul]
        exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn1) (by linarith)
  have heq : (∑' f : HeightOneSpectrum (𝓞 K) →₀ ℕ, ∏ᶠ v, g v^f v) =
      chiFourIdealSeries K s := by
    rw [← Equiv.tsum_eq (nonzeroIdealEquivFinsupp K) (fun f => ∏ᶠ v, g v^f v)]
    have hterms (I : NonzeroIdeal K) :
        (∏ᶠ v, g v ^ (nonzeroIdealEquivFinsupp K I) v) =
          chiFourComplex (Ideal.absNorm (I : Ideal (𝓞 K))) *
            (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)^(-s) :=
      (chiFour_absNorm_cpow_eq_finprod K I.2 s).symm
    rw [tsum_congr hterms, chiFourIdealSeries]
    exact Equiv.tsum_eq (nonzeroIdealEquivNonZeroDivisors K)
      (fun I : (Ideal (𝓞 K))⁰ => chiFourComplex (Ideal.absNorm (I : Ideal (𝓞 K))) *
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ)^(-s))
  exact heq ▸ hasProd_finsuppMonomial hg hsum

theorem chiFourIdealSeries_eq_tprod {s : ℂ} (hs : 1 < s.re) :
    chiFourIdealSeries K s = ∏' v : HeightOneSpectrum (𝓞 K),
      (1-chiFourComplex (Ideal.absNorm v.asIdeal)*(Ideal.absNorm v.asIdeal : ℂ)^(-s))⁻¹ :=
  (chiFourIdealSeries_eulerProduct K hs).tprod_eq.symm

theorem chiFourComplex_zero_of_even {n : ℕ} (hn : Even n) : chiFourComplex n = 0 := by
  rw [chiFourComplex_eq_ofReal, chiFourReal_zero_of_even hn]
  simp

theorem chiFourComplex_one_of_mod_four {n : ℕ} (hn : n%4=1) : chiFourComplex n = 1 := by
  rw [chiFourComplex, ZMod.χ₄_nat_eq_if_mod_four, if_neg (by omega : ¬ n%2=0), if_pos hn]
  norm_num

theorem chiFourComplex_neg_one_of_mod_four {n : ℕ} (hn : n%4=3) : chiFourComplex n = -1 := by
  rw [chiFourComplex, ZMod.χ₄_nat_eq_if_mod_four, if_neg (by omega : ¬ n%2=0), if_neg (by omega : ¬ n%4=1)]
  norm_num

end UnitDistance.NumberFieldAnalysis
