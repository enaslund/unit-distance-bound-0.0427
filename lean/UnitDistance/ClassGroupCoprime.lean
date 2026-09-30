module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! Integral representatives of an ideal class avoiding any specified nonzero ideal. -/
noncomputable section
open scoped nonZeroDivisors
namespace UnitDistance.ClassGroupCoprime
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem exists_inverse_rep_coprime (I : (Ideal R)⁰) (D : Ideal R)
    (hD : D ≠ 0) (hDtop : D ≠ ⊤) :
    ∃ J : (Ideal R)⁰, ClassGroup.mk0 J = (ClassGroup.mk0 I)⁻¹ ∧
      IsCoprime (J : Ideal R) D := by
  have hI : (I : Ideal R) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (I := (I : Ideal R)*D) (J := (I : Ideal R)) Ideal.mul_le_left (mul_ne_zero hI hD)
  obtain ⟨J, hJ⟩ : (I : Ideal R) ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr (le_sup_right.trans_eq ha)
  have hsum : D ⊔ J = ⊤ := by
    apply mul_left_cancel₀ hI
    rw [Ideal.mul_top, Ideal.mul_sup, ← hJ]
    exact ha
  have ha0 : a ≠ 0 := by
    intro hz
    have hJ0 : J = 0 := by
      apply (mul_eq_zero.mp (hJ.symm.trans (by simp [hz]))).resolve_left hI
    exact hDtop (by simpa [hJ0] using hsum)
  have hJ0 : J ≠ 0 := by
    intro hz
    have he : Ideal.span {a} = ⊥ := by simpa [hz] using hJ
    exact ha0 (Ideal.span_singleton_eq_bot.mp he)
  let J' : (Ideal R)⁰ := ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ0⟩
  refine ⟨J', ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨a, ha0, ?_⟩, ?_⟩
  · change J * (I : Ideal R) = Ideal.span {a}
    simpa [mul_comm] using hJ.symm
  · exact Ideal.isCoprime_iff_sup_eq.mpr (by simpa [sup_comm] using hsum)

theorem exists_rep_coprime (c : ClassGroup R) (D : Ideal R) (hD : D ≠ 0) :
    ∃ J : (Ideal R)⁰, ClassGroup.mk0 J = c ∧ IsCoprime (J : Ideal R) D := by
  by_cases hDtop : D = ⊤
  · obtain ⟨J,hJ⟩ := ClassGroup.mk0_surjective c
    exact ⟨J,hJ,Ideal.isCoprime_iff_sup_eq.mpr (by simp [hDtop])⟩
  obtain ⟨I,hI⟩ := ClassGroup.mk0_surjective c⁻¹
  obtain ⟨J,hJ,hcop⟩ := exists_inverse_rep_coprime I D hD hDtop
  exact ⟨J, by simpa [hI] using hJ, hcop⟩

theorem odd_natCard_of_two_isUnit (A : Type*) [CommRing A] [Finite A]
    (h : IsUnit (2 : A)) : Odd (Nat.card A) := by
  classical
  letI := Fintype.ofFinite A
  by_contra hn
  rw [Nat.not_odd_iff_even, even_iff_two_dvd, Nat.card_eq_fintype_card] at hn
  obtain ⟨x,hx⟩ := exists_prime_addOrderOf_dvd_card 2 hn
  have hz : 2*x = (0:A) := by
    simpa [hx, two_nsmul, two_mul] using addOrderOf_nsmul_eq_zero x
  have hx0 : x = 0 := h.mul_left_cancel (by simpa using hz)
  simp [hx0] at hx

theorem isUnit_quotient_mk_of_coprime_span {A : Type*} [CommRing A]
    (I : Ideal A) (a : A) (h : IsCoprime I (Ideal.span {a})) :
    IsUnit (Ideal.Quotient.mk I a) := by
  have htop := Ideal.isCoprime_iff_sup_eq.mp h
  obtain ⟨u,hu,v,hv,he⟩ := Submodule.mem_sup.mp
    (show (1:A) ∈ I ⊔ Ideal.span {a} by rw [htop]; trivial)
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp hv
  have hu0 := Ideal.Quotient.eq_zero_iff_mem.mpr hu
  have hmul : Ideal.Quotient.mk I a * Ideal.Quotient.mk I b = 1 := by
    have hq := congrArg (Ideal.Quotient.mk I) he
    rw [hb, map_add, map_mul, hu0, zero_add, map_one] at hq
    exact hq
  exact isUnit_iff_exists_inv.mpr ⟨_,hmul⟩

theorem exists_odd_norm_rep (F : Type*) [Field F] [NumberField F]
    (c : ClassGroup (NumberField.RingOfIntegers F)) :
    ∃ J : (Ideal (NumberField.RingOfIntegers F))⁰,
      ClassGroup.mk0 J = c ∧ Odd (Ideal.absNorm (J : Ideal (NumberField.RingOfIntegers F))) := by
  let R := NumberField.RingOfIntegers F
  have htwo : Ideal.span {(2:R)} ≠ 0 := by
    simpa only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using
      (show (2:R) ≠ 0 by norm_num)
  obtain ⟨J,hJ,hcop⟩ := exists_rep_coprime c (Ideal.span {(2:R)}) htwo
  refine ⟨J,hJ,?_⟩
  letI : Finite (R ⧸ (J : Ideal R)) := Ideal.absNorm_ne_zero_iff _ |>.mp
    (Ideal.absNorm_ne_zero_of_nonZeroDivisors J)
  change Odd (Nat.card (R ⧸ (J : Ideal R)))
  apply odd_natCard_of_two_isUnit (R ⧸ (J : Ideal R))
  have hu := isUnit_quotient_mk_of_coprime_span (J : Ideal R) (2:R) hcop
  norm_num only [map_ofNat] at hu
  exact hu

end UnitDistance.ClassGroupCoprime
