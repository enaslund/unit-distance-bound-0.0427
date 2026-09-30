module

public import UnitDistance.Sqrt241.Geometry.QuadraticRootField
public import UnitDistance.QuadraticSevenIntegrality

@[expose] public section
set_option backward.privateInPublic true


/-!
# Rational coordinate and norm congruences for `ℚ(√d)`

Copy of `UnitDistance.QuadraticSevenIntegrality` for an admissible radicand
`d` (a prime with `d % 4 = 3`) in place of `7`. The only arithmetic input is
`a² - d b² ≡ a² + b² (mod 4)`. The radicand-free lemmas
(`rat_int_of_sq_int`, `chi4_natAbs_eq_sign_of_mod_four`) are used from the
original.
-/

noncomputable section
set_option autoImplicit false
namespace UnitDistance.Sqrt241.QuadraticRoot

variable {d : ℕ} [hd : Fact (Admissible d)]

theorem rat_int_of_root_mul_sq_int {r : ℚ} (h : ∃ n : ℤ, (d : ℚ)*r^2 = (n:ℚ)) :
    ∃ n : ℤ, r = (n:ℚ) := by
  obtain ⟨n, hn⟩ := h
  have hsq : ((d : ℚ)*r)^2 = (((d : ℤ)*n:ℤ):ℚ) := by
    push_cast
    calc ((d : ℚ)*r)^2 = (d : ℚ)*((d : ℚ)*r^2) := by ring
      _ = (d : ℚ)*(n : ℚ) := by rw [hn]
  obtain ⟨m, hm⟩ := UnitDistance.QuadraticSeven.rat_int_of_sq_int ⟨(d : ℤ)*n, hsq⟩
  have hm2 : m^2 = (d : ℤ)*n := by
    have h' : (m:ℚ)^2 = (d : ℚ)*(n : ℚ) := by
      rw [← hm, hsq]
      push_cast
      ring
    exact_mod_cast h'
  have hp : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hd.out.prime
  have hdiv : (d : ℤ) ∣ m := hp.dvd_of_dvd_pow (show (d : ℤ) ∣ m^2 from ⟨n,hm2⟩)
  obtain ⟨k,hk⟩ := hdiv
  refine ⟨k, ?_⟩
  rw [hk] at hm
  push_cast at hm
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.out.prime.ne_zero
  exact mul_left_cancel₀ hd0 hm

omit hd in
theorem sq_emod_four (a : ℤ) : a^2 % 4 = (a % 4)^2 % 4 := by
  simpa only [pow_two] using Int.mul_emod a a 4

/-- Since `d ≡ -1 (mod 4)`, the norm form is `a² + b²` modulo four. -/
theorem norm_emod_four (a b : ℤ) :
    (a^2-(d : ℤ)*b^2)%4 = ((a%4)^2+(b%4)^2)%4 := by
  have hd4 : (d : ℤ) % 4 = 3 := by exact_mod_cast hd.out.mod_four
  have hdvd : (4 : ℤ) ∣ (d : ℤ) + 1 := by omega
  have hmod : (a^2-(d : ℤ)*b^2) % 4 = (a^2+b^2) % 4 := by
    have h : Int.ModEq 4 (a^2-(d : ℤ)*b^2) (a^2+b^2) := by
      rw [Int.modEq_iff_dvd]
      have he : a^2+b^2-(a^2-(d : ℤ)*b^2) = ((d : ℤ)+1)*b^2 := by ring
      rw [he]
      exact Dvd.dvd.mul_right hdvd _
    exact h
  rw [hmod, Int.add_emod, sq_emod_four a, sq_emod_four b, ← Int.add_emod]

theorem four_dvd_norm_implies_even (a b : ℤ) (h : (4:ℤ) ∣ a^2-(d : ℤ)*b^2) :
    (2:ℤ) ∣ a ∧ (2:ℤ) ∣ b := by
  have hmod : (a^2-(d : ℤ)*b^2)%4 = 0 := Int.emod_eq_zero_of_dvd h
  have ha0 := Int.emod_nonneg a (by norm_num : (4:ℤ)≠0)
  have ha1 := Int.emod_lt_of_pos a (by norm_num : (0:ℤ)<4)
  have hb0 := Int.emod_nonneg b (by norm_num : (4:ℤ)≠0)
  have hb1 := Int.emod_lt_of_pos b (by norm_num : (0:ℤ)<4)
  rw [norm_emod_four] at hmod
  interval_cases ha : a%4 <;> interval_cases hb : b%4 <;>
    norm_num [ha,hb] at hmod <;> constructor <;> omega

theorem rational_coordinates_of_trace_norm (x y : ℚ) (a n : ℤ)
    (htrace : 2*x = (a:ℚ)) (hnorm : x^2-(d : ℚ)*y^2 = (n:ℚ)) :
    ∃ u v : ℤ, x = (u:ℚ) ∧ y = (v:ℚ) := by
  have hroot : (d : ℚ)*(2*y)^2 = ((a^2-4*n:ℤ):ℚ) := by
    push_cast
    linear_combination htrace*(2*x+(a:ℚ))-4*hnorm
  obtain ⟨b,hb⟩ := rat_int_of_root_mul_sq_int (d := d) ⟨a^2-4*n,hroot⟩
  have heq : a^2-(d : ℤ)*b^2 = 4*n := by
    have h' : (a:ℚ)^2-(d : ℚ)*(b:ℚ)^2 = 4*(n:ℚ) := by
      rw [← htrace, ← hb]
      linear_combination 4*hnorm
    exact_mod_cast h'
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

theorem odd_norm_mod_four (a b : ℤ) (h : Odd (a^2-(d : ℤ)*b^2)) :
    (a^2-(d : ℤ)*b^2)%4 = 1 := by
  have hmod := Int.odd_iff.mp h
  have ha0 := Int.emod_nonneg a (by norm_num : (4:ℤ)≠0)
  have ha1 := Int.emod_lt_of_pos a (by norm_num : (0:ℤ)<4)
  have hb0 := Int.emod_nonneg b (by norm_num : (4:ℤ)≠0)
  have hb1 := Int.emod_lt_of_pos b (by norm_num : (0:ℤ)<4)
  have hmod4 : (a^2-(d : ℤ)*b^2)%4%2 = 1 := by omega
  rw [norm_emod_four] at hmod4 ⊢
  interval_cases ha : a%4 <;> interval_cases hb : b%4 <;>
    norm_num at hmod4 <;> norm_num

theorem norm_eq_one_of_isUnit (a b : ℤ) (h : IsUnit (a^2-(d : ℤ)*b^2)) :
    a^2-(d : ℤ)*b^2 = 1 := by
  rcases Int.isUnit_iff.mp h with hp | hn
  · exact hp
  · have hm := odd_norm_mod_four a b (by rw [hn]; norm_num)
    rw [hn] at hm
    norm_num at hm

theorem chi4_natAbs_norm_eq_sign (a b : ℤ) (h : Odd (a^2-(d : ℤ)*b^2)) :
    ZMod.χ₄ ((a^2-(d : ℤ)*b^2).natAbs : ZMod 4) = Int.sign (a^2-(d : ℤ)*b^2) :=
  UnitDistance.QuadraticSeven.chi4_natAbs_eq_sign_of_mod_four _ (odd_norm_mod_four a b h)

end UnitDistance.Sqrt241.QuadraticRoot
