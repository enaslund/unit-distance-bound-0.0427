module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! Rational coordinate and norm congruences for Q(sqrt7).
These are elementary arithmetic lemmas; the field norm/trace identifications
are a separate application. -/
noncomputable section
namespace UnitDistance.QuadraticSeven

theorem rat_int_of_sq_int {r : ℚ} (h : ∃ n : ℤ, r^2 = (n:ℚ)) :
    ∃ n : ℤ, r = (n:ℚ) := by
  obtain ⟨n, hn⟩ := h
  have hi : IsIntegral ℤ (r^2) := by
    rw [hn]
    exact IsIntegrallyClosed.isIntegral_iff.mpr ⟨n, rfl⟩
  obtain ⟨m,hm⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (by norm_num : 0 < (2:ℕ)) hi
  exact ⟨m, hm.symm⟩

theorem rat_int_of_seven_mul_sq_int {r : ℚ} (h : ∃ n : ℤ, 7*r^2 = (n:ℚ)) :
    ∃ n : ℤ, r = (n:ℚ) := by
  obtain ⟨n, hn⟩ := h
  have hsq : (7*r)^2 = ((7*n:ℤ):ℚ) := by push_cast; nlinarith
  obtain ⟨m, hm⟩ := rat_int_of_sq_int ⟨7*n, hsq⟩
  have hm2 : m^2 = 7*n := by
    exact_mod_cast (show (m:ℚ)^2 = 7*(n:ℚ) by rw [← hm]; nlinarith)
  have hp : Prime (7:ℤ) := by norm_num
  have hdiv : (7:ℤ) ∣ m := hp.dvd_of_dvd_pow (show (7:ℤ) ∣ m^2 from ⟨n,hm2⟩)
  obtain ⟨k,hk⟩ := hdiv
  refine ⟨k, ?_⟩
  rw [hk] at hm
  push_cast at hm
  linarith

theorem norm_emod_four (a b : ℤ) :
    (a^2-7*b^2)%4 = ((a%4)^2-7*(b%4)^2)%4 := by
  have ha : a^2%4 = (a%4)^2%4 := by
    simpa only [pow_two] using Int.mul_emod a a 4
  have hb : b^2%4 = (b%4)^2%4 := by
    simpa only [pow_two] using Int.mul_emod b b 4
  rw [Int.sub_emod (a^2) (7*b^2) 4, Int.sub_emod ((a%4)^2) (7*(b%4)^2) 4,
    Int.mul_emod 7 (b^2) 4,
    Int.mul_emod 7 ((b%4)^2) 4, ha, hb]

theorem four_dvd_norm_implies_even (a b : ℤ) (h : (4:ℤ) ∣ a^2-7*b^2) :
    (2:ℤ) ∣ a ∧ (2:ℤ) ∣ b := by
  have hmod : (a^2-7*b^2)%4 = 0 := Int.emod_eq_zero_of_dvd h
  have ha0 := Int.emod_nonneg a (by norm_num : (4:ℤ)≠0)
  have ha1 := Int.emod_lt_of_pos a (by norm_num : (0:ℤ)<4)
  have hb0 := Int.emod_nonneg b (by norm_num : (4:ℤ)≠0)
  have hb1 := Int.emod_lt_of_pos b (by norm_num : (0:ℤ)<4)
  rw [norm_emod_four] at hmod
  interval_cases ha : a%4 <;> interval_cases hb : b%4 <;>
    norm_num [ha,hb] at hmod <;> constructor <;> omega

theorem rational_coordinates_of_trace_norm (x y : ℚ) (a n : ℤ)
    (htrace : 2*x = (a:ℚ)) (hnorm : x^2-7*y^2 = (n:ℚ)) :
    ∃ u v : ℤ, x = (u:ℚ) ∧ y = (v:ℚ) := by
  have hseven : 7*(2*y)^2 = ((a^2-4*n:ℤ):ℚ) := by
    push_cast
    linear_combination htrace*(2*x+(a:ℚ))-4*hnorm
  obtain ⟨b,hb⟩ := rat_int_of_seven_mul_sq_int ⟨a^2-4*n,hseven⟩
  have heq : a^2-7*b^2 = 4*n := by
    exact_mod_cast (show (a:ℚ)^2-7*(b:ℚ)^2 = 4*(n:ℚ) by
      rw [← htrace, ← hb]
      nlinarith [hnorm])
  obtain ⟨hu,hv⟩ := four_dvd_norm_implies_even a b ⟨n,heq⟩
  obtain ⟨u,hu⟩ := hu
  obtain ⟨v,hv⟩ := hv
  refine ⟨u,v,?_,?_⟩
  · rw [hu] at htrace
    push_cast at htrace
    linarith
  · rw [hv] at hb
    push_cast at hb
    linarith

theorem odd_norm_mod_four (a b : ℤ) (h : Odd (a^2-7*b^2)) :
    (a^2-7*b^2)%4 = 1 := by
  have hmod := Int.odd_iff.mp h
  have ha0 := Int.emod_nonneg a (by norm_num : (4:ℤ)≠0)
  have ha1 := Int.emod_lt_of_pos a (by norm_num : (0:ℤ)<4)
  have hb0 := Int.emod_nonneg b (by norm_num : (4:ℤ)≠0)
  have hb1 := Int.emod_lt_of_pos b (by norm_num : (0:ℤ)<4)
  have hmod4 : (a^2-7*b^2)%4%2 = 1 := by omega
  rw [norm_emod_four] at hmod4 ⊢
  interval_cases ha : a%4 <;> interval_cases hb : b%4 <;>
    norm_num at hmod4 <;> norm_num

theorem norm_eq_one_of_isUnit (a b : ℤ) (h : IsUnit (a^2-7*b^2)) :
    a^2-7*b^2 = 1 := by
  rcases Int.isUnit_iff.mp h with hp | hn
  · exact hp
  · have hm := odd_norm_mod_four a b (by rw [hn]; norm_num)
    rw [hn] at hm
    norm_num at hm

theorem chi4_natAbs_eq_sign_of_mod_four (n : ℤ) (hn : n%4 = 1) :
    ZMod.χ₄ (n.natAbs : ZMod 4) = Int.sign n := by
  have heq : (n.natAbs : ZMod 4) = ((|n| : ℤ) : ZMod 4) := by
    rw [← Int.natCast_natAbs]
    simp
  rw [heq]
  rcases lt_trichotomy n 0 with hneg | hzero | hpos
  · rw [abs_of_neg hneg, Int.sign_eq_neg_one_of_neg hneg]
    exact ZMod.χ₄_int_three_mod_four (by omega)
  · subst n
    norm_num at hn
  · rw [abs_of_pos hpos, Int.sign_eq_one_of_pos hpos]
    exact ZMod.χ₄_int_one_mod_four hn

theorem chi4_natAbs_norm_eq_sign (a b : ℤ) (h : Odd (a^2-7*b^2)) :
    ZMod.χ₄ ((a^2-7*b^2).natAbs : ZMod 4) = Int.sign (a^2-7*b^2) :=
  chi4_natAbs_eq_sign_of_mod_four _ (odd_norm_mod_four a b h)

end UnitDistance.QuadraticSeven
