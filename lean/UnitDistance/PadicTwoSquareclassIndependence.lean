module

public import UnitDistance.PadicTwoSquareclasses

@[expose] public section
set_option backward.privateInPublic true


/-! Exact nonsquareness and local relations among the rational radicands. -/
noncomputable section
namespace UnitDistance.PadicTwo
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem unitRepresentative_valuation (i : Fin 4) :
    Padic.valuation (unitRepresentative i : ℚ_[2])=0 := by
  rw [Padic.valuation_intCast]
  have h : padicValInt 2 (unitRepresentative i)=0 := by
    change padicValNat 2 (unitRepresentative i).natAbs=0
    apply padicValNat.eq_zero_of_not_dvd
    fin_cases i <;> decide
  rw [h]
  rfl

theorem representative_ne_zero (i : Fin 4) (e : Fin 2) :
    (representative i e : ℚ_[2])≠0 := by
  have h : representative i e≠0 := by fin_cases i <;> fin_cases e <;> decide
  exact_mod_cast h

theorem representative_valuation (i : Fin 4) (e : Fin 2) :
    Padic.valuation (representative i e : ℚ_[2])=e.val := by
  have hn : (unitRepresentative i : ℚ_[2])≠0 := by
    have h : unitRepresentative i≠0 := by fin_cases i <;> decide
    exact_mod_cast h
  have h2 : Padic.valuation (2 : ℚ_[2])=1 := by simpa using (Padic.valuation_p (p := 2))
  push_cast [representative]
  rw [Padic.valuation_mul hn (pow_ne_zero _ (by norm_num)),Padic.valuation_pow,
    unitRepresentative_valuation,h2]
  simp

theorem representative_isSquare_iff (i : Fin 4) (e : Fin 2) :
    IsSquare (representative i e : ℚ_[2]) ↔ i=0 ∧ e=0 := by
  constructor
  · intro h
    obtain ⟨z,hz⟩ := h.exists_sq
    have hv := congrArg Padic.valuation hz
    rw [representative_valuation,Padic.valuation_pow] at hv
    have he : e=0 := by apply Fin.ext; have := e.isLt; omega
    subst e
    have hu : IsSquare (representativeUnit i : ℚ_[2]) := by
      simpa [representative] using h
    have hr := (unit_isSquare_iff _).mp hu
    rw [representativeUnit_val,map_intCast] at hr
    have hc : ∀ j : Fin 4,(unitRepresentative j : ZMod 8)=1 → j=0 := by decide +kernel
    have hi : i=0 := hc i hr
    exact ⟨hi,rfl⟩
  · rintro ⟨rfl,rfl⟩
    norm_num [representative,unitRepresentative]

end UnitDistance.PadicTwo

namespace UnitDistance.PadicTwo
open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def independentRadicand : Fin 3 → ℤ := ![-1,2,5]
def unitIndex (w : Fin 3 → ZMod 2) : Fin 4 :=
  ⟨(w 0).val+2*(w 2).val,by have h0 := ZMod.val_lt (w 0); have h2 := ZMod.val_lt (w 2); omega⟩
def parityIndex (w : Fin 3 → ZMod 2) : Fin 2 := ⟨(w 1).val,ZMod.val_lt _⟩

theorem product_representative : ∀ w : Fin 3 → ZMod 2,
    (∏ i,independentRadicand i ^ (w i).val)=representative (unitIndex w) (parityIndex w) := by
  decide +kernel

theorem indices_zero : ∀ w : Fin 3 → ZMod 2,
    unitIndex w=0 → parityIndex w=0 → w=0 := by decide +kernel

/-- The three actual squareclasses of −1, 2, 5 are independent. -/
theorem independent_products (w : Fin 3 → ZMod 2)
    (h : IsSquare (∏ i,(independentRadicand i : ℚ_[2])^(w i).val)) : w=0 := by
  have he : (∏ i,(independentRadicand i : ℚ_[2])^(w i).val)=
      (representative (unitIndex w) (parityIndex w) : ℚ_[2]) := by
    exact_mod_cast product_representative w
  rw [he,representative_isSquare_iff] at h
  exact indices_zero w h.1 h.2

/-- Integral congruence modulo eight supplies an actual square in Q₂. -/
theorem int_isSquare_of_residue_one (n : ℤ) (hn : (n : ZMod 8)=1) :
    IsSquare (n : ℚ_[2]) := by
  obtain ⟨z,hz⟩ := exists_sq_eq_of_residue_one (n : ℤ_[2]) (by rw [map_intCast]; exact hn)
  refine ⟨(z : ℚ_[2]),?_⟩
  have he := congrArg (fun x : ℤ_[2] => (x : ℚ_[2])) hz
  simpa [pow_two] using he.symm

/-- The four actual local relations among the seven global genus radicands. -/
theorem genus_relations : IsSquare (-15 : ℚ_[2]) ∧ IsSquare (-7 : ℚ_[2]) ∧
    IsSquare (-55 : ℚ_[2]) ∧ IsSquare (65 : ℚ_[2]) := by
  refine ⟨int_isSquare_of_residue_one (-15) ?_,int_isSquare_of_residue_one (-7) ?_,
    int_isSquare_of_residue_one (-55) ?_,int_isSquare_of_residue_one 65 ?_⟩ <;> decide +kernel

end UnitDistance.PadicTwo
