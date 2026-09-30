module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! Exact local nonsquareness and the five odd-prime residue sign tables. -/
noncomputable section
namespace UnitDistance.PadicOdd

theorem prime_mul_unit_not_isSquare (p : ℕ) [Fact p.Prime]
    (d : ℤ) (hd : ¬(p : ℤ)∣d) : ¬IsSquare ((p : ℚ_[p])*(d : ℚ_[p])) := by
  have hd0 : d≠0 := fun h ↦ hd (h ▸ dvd_zero _)
  have hdP : (d : ℚ_[p])≠0 := by exact_mod_cast hd0
  have hpP : (p : ℚ_[p])≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hvd : Padic.valuation (d : ℚ_[p])=0 := by
    rw [Padic.valuation_intCast]
    change (padicValNat p d.natAbs : ℤ)=0
    rw [padicValNat.eq_zero_of_not_dvd]
    · rfl
    · exact fun h ↦ hd (Int.natCast_dvd.mpr h)
  intro h
  obtain ⟨z,hz⟩ := h.exists_sq
  have hv := congrArg Padic.valuation hz
  rw [Padic.valuation_mul hpP hdP, Padic.valuation_p, hvd, Padic.valuation_pow] at hv
  omega

theorem prime_not_isSquare (p : ℕ) [Fact p.Prime] : ¬IsSquare (p : ℚ_[p]) := by
  have h : ¬(p : ℤ)∣(1 : ℤ) := by
    exact_mod_cast (Nat.Prime.not_dvd_one (Fact.out : p.Prime))
  simpa using prime_mul_unit_not_isSquare p 1 h

abbrev primes : Fin 5 → ℕ := ![3,5,7,11,13]
abbrev radicands : Fin 7 → ℤ := ![-1,2,3,5,7,11,13]
abbrev masks : Fin 5 → ℕ := ![43,86,77,83,58]
def ramifiedIndex (i : Fin 5) : Fin 7 := ⟨i.val+2,by omega⟩
def residueSign (i : Fin 5) (j : Fin 7) : ℤ := if (masks i).testBit j.val then -1 else 1
abbrev nonresidueIndex : Fin 5 → Fin 7 := ![0,1,0,0,1]

theorem primes_prime (i : Fin 5) : (primes i).Prime := by
  have h : ∀ i : Fin 5,(primes i).Prime := by decide +kernel
  exact h i

theorem primes_odd (i : Fin 5) : primes i=2*((primes i-1)/2)+1 := by
  have h : ∀ i : Fin 5, primes i=2*((primes i-1)/2)+1 := by decide +kernel
  exact h i

theorem radicands_unit (i : Fin 5) (j : Fin 7) (hij : j≠ramifiedIndex i) :
    ¬(primes i : ℤ)∣radicands j := by
  have h : ∀ i : Fin 5, ∀ j : Fin 7, j≠ramifiedIndex i →
      ¬(primes i : ℤ)∣radicands j := by decide +kernel
  exact h i j hij

theorem euler_residue_sign (i : Fin 5) (j : Fin 7) (hij : j≠ramifiedIndex i) :
    (radicands j : ZMod (primes i))^((primes i-1)/2)=residueSign i j := by
  have h : ∀ i : Fin 5, ∀ j : Fin 7, j≠ramifiedIndex i →
      (radicands j : ZMod (primes i))^((primes i-1)/2)=residueSign i j := by decide +kernel
  exact h i j hij

theorem nonresidue_index_ne (i : Fin 5) : nonresidueIndex i≠ramifiedIndex i := by
  have h : ∀ i : Fin 5, nonresidueIndex i≠ramifiedIndex i := by decide +kernel
  exact h i

theorem nonresidue_sign (i : Fin 5) : residueSign i (nonresidueIndex i)= -1 := by
  have h : ∀ i : Fin 5, residueSign i (nonresidueIndex i)= -1 := by decide +kernel
  exact h i

theorem ramified_sign (i : Fin 5) : residueSign i (ramifiedIndex i)=1 := by
  have h : ∀ i : Fin 5, residueSign i (ramifiedIndex i)=1 := by decide +kernel
  exact h i

end UnitDistance.PadicOdd
