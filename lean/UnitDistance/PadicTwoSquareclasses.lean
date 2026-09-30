module

public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! Actual square roots and squareclasses over Q₂, proved from Hensel's
lemma and the literal residue ring modulo eight. -/
noncomputable section
namespace UnitDistance.PadicTwo
open Polynomial
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev residue8 : ℤ_[2] →+* ZMod 8 := PadicInt.toZModPow 3

/-- Hensel's lemma produces an actual square root of every 2-adic integer congruent to one modulo eight. -/
theorem exists_sq_eq_of_residue_one (u : ℤ_[2]) (hu : residue8 u=1) :
    ∃ z : ℤ_[2],z^2=u := by
  have hm : u-1∈Ideal.span ({(2 : ℤ_[2])^3} : Set ℤ_[2]) := by
    have hk : u-1∈RingHom.ker (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2^3)) := by
      change residue8 (u-1)=0
      simp [hu]
    simpa only [PadicInt.ker_toZModPow,Nat.cast_ofNat] using hk
  have hn : ‖u-1‖≤(2 : ℝ)^(-(3 : ℕ) : ℤ) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ 3).mpr hm
  let P : Polynomial ℤ_[2] := X^2-C u
  have hnorm : ‖P.aeval (1 : ℤ_[2])‖<‖P.derivative.aeval (1 : ℤ_[2])‖^2 := by
    have h2 : ‖(2 : ℤ_[2])‖=(1/2 : ℝ) := by
      simpa using (PadicInt.norm_p (p := 2))
    have hp : P.aeval (1 : ℤ_[2])=1-u := by simp [P]
    have hd : P.derivative.aeval (1 : ℤ_[2])=2 := by simp [P,Polynomial.derivative_pow]
    rw [hp,hd,h2,norm_sub_rev]
    norm_num at hn ⊢
    linarith
  obtain ⟨z,hz,_⟩ := hensels_lemma (p := 2) (F := P) (a := (1 : ℤ_[2])) hnorm
  refine ⟨z,?_⟩
  exact sub_eq_zero.mp (by simpa [P] using hz)

/-- Four literal odd-unit squareclass representatives. -/
def unitRepresentative : Fin 4 → ℤ := ![1,-1,5,-5]

theorem unitRepresentative_isUnit (i : Fin 4) : IsUnit (unitRepresentative i : ℤ_[2]) := by
  apply PadicInt.isUnit_iff.mpr
  apply PadicInt.norm_intCast_eq_one_iff.mpr
  fin_cases i <;> norm_num [unitRepresentative]

noncomputable def representativeUnit (i : Fin 4) : ℤ_[2]ˣ := (unitRepresentative_isUnit i).unit

@[simp] theorem representativeUnit_val (i : Fin 4) :
    (representativeUnit i : ℤ_[2])=(unitRepresentative i : ℤ_[2]) :=
  (unitRepresentative_isUnit i).unit_spec

set_option maxHeartbeats 2000000 in
theorem residue_unit_representatives : ∀ a : ZMod 8, IsUnit a →
    ∃ i : Fin 4,a=(unitRepresentative i : ZMod 8) := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem residue_unit_square : ∀ a : ZMod 8,IsUnit a → a^2=1 := by decide +kernel

/-- Every actual 2-adic integer unit is one of the four representatives times a square. -/
theorem unit_squareclass (u : ℤ_[2]ˣ) :
    ∃ (i : Fin 4) (z : ℤ_[2]),(u : ℤ_[2])=(unitRepresentative i : ℤ_[2])*z^2 := by
  obtain ⟨i,hi⟩ := residue_unit_representatives (residue8 (u : ℤ_[2])) (u.isUnit.map residue8)
  let q : ℤ_[2]ˣ := u*(representativeUnit i)⁻¹
  have hq : residue8 (q : ℤ_[2])=1 := by
    have hm : Units.map residue8.toMonoidHom u=Units.map residue8.toMonoidHom (representativeUnit i) := by
      apply Units.ext
      simpa using hi
    have huq : Units.map residue8.toMonoidHom q=1 := by
      change Units.map residue8.toMonoidHom (u*(representativeUnit i)⁻¹)=1
      rw [map_mul,map_inv,hm,mul_inv_cancel]
    exact congrArg (fun v : (ZMod 8)ˣ => (v : ZMod 8)) huq
  obtain ⟨z,hz⟩ := exists_sq_eq_of_residue_one (q : ℤ_[2]) hq
  refine ⟨i,z,?_⟩
  rw [hz,← representativeUnit_val]
  change (u : ℤ_[2])=(representativeUnit i : ℤ_[2])*
    ((u : ℤ_[2])*((representativeUnit i)⁻¹ : ℤ_[2]ˣ))
  simp [mul_left_comm]

/-- Every nonzero 2-adic number has an integral unit factor after removing its valuation. -/
theorem exists_unit_factor (x : ℚ_[2]) (hx : x ≠ 0) :
    ∃ u : ℤ_[2]ˣ, x = (u : ℚ_[2]) * (2 : ℚ_[2]) ^ x.valuation := by
  have hn : ‖x * (2 : ℚ_[2]) ^ (-x.valuation)‖ = 1 := by
    rw [norm_mul,Padic.norm_eq_zpow_neg_valuation hx]
    have h2 := Padic.norm_p_zpow (p := 2) (-x.valuation)
    norm_num only [Nat.cast_ofNat,neg_neg] at h2 ⊢
    rw [h2]
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  refine ⟨PadicInt.mkUnits hn,?_⟩
  rw [PadicInt.mkUnits_eq,mul_assoc,← zpow_add₀ (by norm_num : (2 : ℚ_[2]) ≠ 0)]
  simp

/-- The eight actual squareclass representatives of Q₂. -/
def representative (i : Fin 4) (e : Fin 2) : ℤ := unitRepresentative i * 2 ^ e.val

/-- The full squareclass classification, including valuation parity. -/
theorem squareclass (x : ℚ_[2]) (hx : x ≠ 0) :
    ∃ (i : Fin 4) (e : Fin 2) (z : ℚ_[2]), x = (representative i e : ℚ_[2]) * z^2 := by
  obtain ⟨u,hu⟩ := exists_unit_factor x hx
  obtain ⟨i,z,hz⟩ := unit_squareclass u
  let e : Fin 2 := ⟨Int.toNat (x.valuation % 2),by omega⟩
  have he : (e.val : ℤ) = x.valuation % 2 := by
    dsimp [e]
    omega
  have hv : x.valuation = (e.val : ℤ) + (x.valuation / 2) * 2 := by omega
  refine ⟨i,e,(z : ℚ_[2])*(2 : ℚ_[2])^(x.valuation/2),?_⟩
  have hz' : (u : ℚ_[2]) = (unitRepresentative i : ℚ_[2])*(z : ℚ_[2])^2 := by
    simpa using congrArg (fun a : ℤ_[2] => (a : ℚ_[2])) hz
  calc
    x = (u : ℚ_[2]) * (2 : ℚ_[2]) ^ x.valuation := hu
    _ = (representative i e : ℚ_[2]) * ((z : ℚ_[2])*(2 : ℚ_[2])^(x.valuation/2))^2 := by
      conv_lhs => rw [hz',hv,zpow_add₀ (by norm_num : (2 : ℚ_[2]) ≠ 0),zpow_natCast,zpow_mul]
      push_cast [representative]
      norm_num only [zpow_ofNat]
      ring

/-- A 2-adic integer unit which is a square in Q₂ already has a unit square root. -/
theorem unit_root_of_square (u : ℤ_[2]ˣ) (z : ℚ_[2]) (hz : z^2=(u : ℚ_[2])) :
    ∃ v : ℤ_[2]ˣ,(v : ℚ_[2])=z := by
  have hu : ‖(u : ℚ_[2])‖=1 := by
    exact PadicInt.isUnit_iff.mp u.isUnit
  have hn : ‖z‖^2=1 := by rw [← norm_pow,hz,hu]
  have hnz : ‖z‖=1 := by nlinarith [norm_nonneg z]
  exact ⟨PadicInt.mkUnits hnz,PadicInt.mkUnits_eq hnz⟩

/-- For an actual unit, being a square is exactly the residue-one condition modulo eight. -/
theorem unit_isSquare_iff (u : ℤ_[2]ˣ) : IsSquare (u : ℚ_[2]) ↔ residue8 (u : ℤ_[2])=1 := by
  constructor
  · rintro ⟨z,hz⟩
    have hz' : z^2=(u : ℚ_[2]) := by simpa [pow_two] using hz.symm
    obtain ⟨v,hv⟩ := unit_root_of_square u z hz'
    have he : (v : ℤ_[2])^2=(u : ℤ_[2]) := by
      apply PadicInt.ext
      simpa [hv] using hz'
    rw [← he,map_pow]
    exact residue_unit_square _ (v.isUnit.map residue8)
  · intro hu
    obtain ⟨z,hz⟩ := exists_sq_eq_of_residue_one (u : ℤ_[2]) hu
    refine ⟨(z : ℚ_[2]),?_⟩
    have h := congrArg (fun a : ℤ_[2] => (a : ℚ_[2])) hz
    simpa [pow_two] using h.symm

end UnitDistance.PadicTwo
