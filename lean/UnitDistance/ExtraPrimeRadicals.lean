module

public import UnitDistance.GroupAugmentationRetainedQuadratic
public import UnitDistance.SigmaPrimeSupport
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! Exact residue signs at the five additional primes, and their order-four
quadratic images. All finite arithmetic certificates are kernel checked. -/
noncomputable section
namespace UnitDistance.ExtraPrime
abbrev primes : Fin 5 → ℕ := ![17,19,23,29,31]
abbrev radicands : Fin 7 → ℤ := ![-1,2,3,5,7,11,13]
abbrev masks : Fin 5 → ℕ := ![60,71,57,38,101]
def vector (i : Fin 5) : Fin 7 → ZMod 2 := RetainedQuadratic.binaryVector 7 (masks i)
def residueSign (i : Fin 5) (j : Fin 7) : ℤ := if (masks i).testBit j.val then -1 else 1

theorem primes_prime (i : Fin 5) : (primes i).Prime := by
  have h : ∀i : Fin 5,(primes i).Prime := by decide +kernel
  exact h i

def prime (i : Fin 5) : Nat.Primes := ⟨primes i,primes_prime i⟩

theorem outside_support (i : Fin 5) :
    Rat.HeightOneSpectrum.primesEquiv.symm (prime i)∉ArithmeticProP.sigmaPrimeSupport := by
  change ¬(Rat.HeightOneSpectrum.primesEquiv (Rat.HeightOneSpectrum.primesEquiv.symm (prime i))).val∈ArithmeticProP.sigmaRationalPrimes
  rw [Equiv.apply_symm_apply]
  have h : ∀i : Fin 5,primes i∉ArithmeticProP.sigmaRationalPrimes := by decide +kernel
  exact h i

theorem primes_odd (i : Fin 5) : primes i=2*((primes i-1)/2)+1 := by
  have h : ∀i : Fin 5,primes i=2*((primes i-1)/2)+1 := by decide +kernel
  exact h i

theorem primes_ne_two (i : Fin 5) : primes i≠2 := by
  have h : ∀i : Fin 5,primes i≠2 := by decide +kernel
  exact h i

theorem radicands_unit (i : Fin 5) (j : Fin 7) : ¬(primes i : ℤ)∣radicands j := by
  have h : ∀i : Fin 5,∀j : Fin 7,¬(primes i : ℤ)∣radicands j := by decide +kernel
  exact h i j

theorem euler_residue_sign (i : Fin 5) (j : Fin 7) :
    (radicands j : ZMod (primes i))^((primes i-1)/2)=residueSign i j := by
  have h : ∀i : Fin 5,∀j : Fin 7,
      (radicands j : ZMod (primes i))^((primes i-1)/2)=residueSign i j := by decide +kernel
  exact h i j

theorem vector_ne_zero (i : Fin 5) : vector i≠0 := by
  have h : ∀i : Fin 5,vector i≠0 := by decide +kernel
  exact h i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem square_ne_zero (i : Fin 5) : RetainedQuadratic.cocycle (vector i) (vector i)≠0 := by
  have h : ∀i : Fin 5,RetainedQuadratic.cocycle (vector i) (vector i)≠0 := by decide +kernel
  exact h i

/-- Every retained-model lift of the specified genus vector has exact order four. -/
theorem retained_order (i : Fin 5) (g : RetainedQuadratic.Q) (hg : g.base=vector i) : orderOf g=4 := by
  have h2 : g^2≠1 := by
    rw [ClassTwo.GroupModel.square_coordinates,hg]
    intro h
    exact square_ne_zero i (congrArg ClassTwo.GroupModel.central h)
  have h4 : g^4=1 := by
    change g^(2*2)=1
    rw [pow_mul,ClassTwo.GroupModel.square_coordinates,ClassTwo.GroupModel.square_coordinates]
    ext <;> simp
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p:=2) (n:=1) h2 h4

end UnitDistance.ExtraPrime
