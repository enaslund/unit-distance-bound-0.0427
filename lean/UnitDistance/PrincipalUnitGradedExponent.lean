module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! Actual principal-unit layers and prime-to-residue-characteristic groups. -/
namespace UnitDistance.OddTame

theorem hom_eq_one_of_coprime_exponent {G H : Type*} [Group G] [Group H]
    {p q : ℕ} (hG : IsPGroup p G) (hpq : p.Coprime q)
    (f : G →* H) (hpow : ∀ h : H, h^q=1) (g : G) : f g=1 := by
  obtain ⟨x,hx⟩ := (hG.powEquiv hpq).surjective g
  rw [← hx, hG.powEquiv_apply, map_pow, hpow]

theorem one_add_pow_of_square_zero {R : Type*} [CommRing R]
    (x : R) (hx : x^2=0) (q : ℕ) : (1+x)^q=1+q*x := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ,ih,Nat.cast_add,Nat.cast_one]
    have hx' : x*x=0 := by simpa only [pow_two] using hx
    calc
      (1+q*x)*(1+x)=1+(q+1)*x+q*(x*x) := by ring
      _ = _ := by rw [hx']; ring

/-- A principal unit at depth n≥1 has qth power at depth n+1 whenever
the residue characteristic divides q. Both depths are actual ideal powers. -/
theorem principal_unit_pow_mem {R : Type*} [CommRing R]
    (m : Ideal R) (q n : ℕ) (hn : 1≤n) (hq : (q : R)∈m)
    (a : R) (ha : a-1∈m^n) : a^q-1∈m^(n+1) := by
  let J := m^(n+1)
  let π := Ideal.Quotient.mk J
  have hsquare : (a-1)^2∈J := by
    have h := Ideal.mul_mem_mul ha ha
    have he : m^n*m^n=m^(n+n) := (pow_add m n n).symm
    rw [he] at h
    exact Ideal.pow_le_pow_right (by omega : n+1≤n+n) (by simpa only [pow_two] using h)
  have hlinear : (q : R)*(a-1)∈J := by
    have h := Ideal.mul_mem_mul hq ha
    simpa only [← pow_succ'] using h
  have hz : (π (a-1))^2=0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hsquare
  have hlin : (q : R ⧸ J)*π (a-1)=0 := by
    rw [← map_natCast π q, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hlinear
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π (a^q-1)=0
  rw [map_sub,map_pow,map_one]
  have he : π a=1+π (a-1) := by rw [map_sub,map_one]; ring
  rw [he,one_add_pow_of_square_zero _ hz q,hlin]
  ring

end UnitDistance.OddTame
