module

public import UnitDistance.Sqrt241.V2.Types
public import UnitDistance.Sqrt241.Levels.PrimeFreedom

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Version 2: complex conjugation moves every prime above `2, 3, 5, 29, 41`

An elementary form of version 1's `√d` argument that needs no Galois structure on `K_j`.
For each witness prime `p` there is `√d ∈ E ⊆ K_j` with `d < 0`
(`d = −15, −2, −1, −1, −1`; version 1's `rootD` at indices `0, 1, 2, 3, 2`), and `c_j`
negates it. If `p` is odd and `t² ≡ d (mod p)` with `p ∤ 2t` (`t = 1, 2, 12, 9`), the
integral element `w = √d − t` has `w c(w) = t² − d ≡ 0` and `w + c(w) = −2t ≢ 0 (mod p)`; at
`p = 2` the element `w = (√−15 − 1)/2` (a root of `X² + X + 4`) has `w c(w) = 4` and
`w + c(w) = −1`. In both cases a prime `P ∋ p` fixed by `c_j` would contain `w` or `c(w)`,
hence both, hence `w + c(w)` (`map_ne_of_mul_add`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.V2

open Tower Retained UnitDistance.NumberFieldAnalysis IsDedekindDomain NumberField CanonicalGenus
open scoped NumberField

/-! ### `√d` in the levels -/

/-- Version 1's index of `√d` for the witness index `a` of version 2. -/
def rootIndex : Fin 5 → Fin 5 := ![0, 1, 2, 3, 2]

theorem EOmega_le_level (j : ℕ) : EOmega ≤ level j := input.EOmega_le_M.trans (M_le_level j)

/-- `√d` in `K_j`. -/
def rootLevel (j : ℕ) (b : Fin 5) : level j :=
  ⟨⟨((rootD b : CanonicalGenus.Carrier) : Closure), canonicalGenus_le_Omega (rootD b).2⟩,
    EOmega_le_level j (Input.mem_EOmega_of_mem_field (rootD b).2)⟩

theorem rootLevel_sq (j : ℕ) (b : Fin 5) :
    rootLevel j b ^ 2 = ((dInt b : ℤ) : level j) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((rootD b : CanonicalGenus.Carrier) : Closure) ^ 2 = _
  rw [rootD_sq_closure]
  simp

theorem levelConj_rootLevel (j : ℕ) (b : Fin 5) :
    levelConjRing j (rootLevel j b) = -rootLevel j b := by
  apply Subtype.ext
  rw [coe_levelConjRing, IntermediateField.coe_neg]
  apply Subtype.ext
  rw [IntermediateField.coe_neg]
  exact conj_moves_rootD input b

theorem isIntegral_rootLevel (j : ℕ) (b : Fin 5) : IsIntegral ℤ (rootLevel j b) := by
  apply IsIntegral.of_pow two_pos
  rw [rootLevel_sq]
  have h := isIntegral_algebraMap (R := ℤ) (A := level j) (x := dInt b)
  simpa using h

/-- `√d` in `𝓞 K_j`. -/
def rootInt (j : ℕ) (b : Fin 5) : 𝓞 (level j) :=
  ⟨rootLevel j b, (mem_integralClosure_iff ℤ _).mpr (isIntegral_rootLevel j b)⟩

theorem coe_rootInt (j : ℕ) (b : Fin 5) : ((rootInt j b : 𝓞 (level j)) : level j) =
    rootLevel j b := rfl

/-- `(√−15 − 1)/2` in `K_j`, a root of `X² + X + 4`. -/
def halfRoot (j : ℕ) : level j := (rootLevel j 0 - 1) / 2

theorem halfRoot_eq (j : ℕ) : halfRoot j ^ 2 + halfRoot j + 4 = 0 := by
  have h := rootLevel_sq j 0
  have h15 : ((dInt 0 : ℤ) : level j) = -15 := by
    change (((-15 : ℤ)) : level j) = -15
    push_cast
    ring
  rw [h15] at h
  unfold halfRoot
  field_simp
  linear_combination h

theorem isIntegral_halfRoot (j : ℕ) : IsIntegral ℤ (halfRoot j) := by
  refine ⟨Polynomial.X ^ 2 + (Polynomial.X + Polynomial.C 4), ?_, ?_⟩
  · apply (Polynomial.monic_X_pow 2).add_of_left
    rw [Polynomial.degree_X_add_C, Polynomial.degree_X_pow]
    exact_mod_cast (by norm_num : (1 : ℕ) < 2)
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    rw [show (algebraMap ℤ (level j)) 4 = 4 by simp, ← add_assoc]
    exact halfRoot_eq j

def halfRootInt (j : ℕ) : 𝓞 (level j) :=
  ⟨halfRoot j, (mem_integralClosure_iff ℤ _).mpr (isIntegral_halfRoot j)⟩

@[simp] theorem algebraMap_halfRootInt (j : ℕ) :
    algebraMap (𝓞 (level j)) (level j) (halfRootInt j) = halfRoot j := rfl

@[simp] theorem algebraMap_rootInt (j : ℕ) (b : Fin 5) :
    algebraMap (𝓞 (level j)) (level j) (rootInt j b) = rootLevel j b := rfl

theorem levelConj_halfRoot (j : ℕ) : levelConjRing j (halfRoot j) = -1 - halfRoot j := by
  unfold halfRoot
  rw [map_div₀, map_sub, map_one, levelConj_rootLevel]
  have h2 : levelConjRing j 2 = 2 := map_ofNat _ 2
  rw [h2]
  ring

/-! ### Moving the primes -/

/-- The conjugation on `𝓞 K_j`. -/
abbrev levelConjInt (j : ℕ) : 𝓞 (level j) →+* 𝓞 (level j) :=
  RingOfIntegers.mapRingHom (levelConjRing j : level j →+* level j)

theorem levelConjInt_bijective (j : ℕ) : Function.Bijective (levelConjInt j) :=
  (RingOfIntegers.mapRingEquiv (levelConjRing j)).bijective

@[simp] theorem algebraMap_levelConjInt (j : ℕ) (x : 𝓞 (level j)) :
    algebraMap (𝓞 (level j)) (level j) (levelConjInt j x) =
      levelConjRing j (algebraMap (𝓞 (level j)) (level j) x) := rfl

theorem algebraMap_int_injective (j : ℕ) :
    Function.Injective (algebraMap (𝓞 (level j)) (level j)) :=
  fun _ _ h => RingOfIntegers.ext h

/-- The value `t` with `t² ≡ d (mod p)` at the odd witness primes. -/
def tOdd : Fin 5 → ℤ := ![0, 1, 2, 12, 9]

theorem tOdd_facts : ∀ a : Fin 5, a ≠ 0 →
    (Witness.primes a : ℤ) ∣ tOdd a ^ 2 - dInt (rootIndex a) ∧
      ¬ (Witness.primes a : ℤ) ∣ -2 * tOdd a := by
  decide

theorem dInt_rootIndex_neg (a : Fin 5) : dInt (rootIndex a) < 0 := by
  fin_cases a <;> decide

/-- **Prime freedom in the levels**: `c_j` moves every prime of `K_j` above a witness prime. -/
theorem level_prime_moved (j : ℕ) (a : Fin 5) (P : Ideal (𝓞 (level j))) [P.IsPrime]
    [P.LiesOver (rationalPrimeIdeal (Witness.primes a))] :
    Ideal.map (levelConjInt j) P ≠ P := by
  by_cases ha : a = 0
  · subst ha
    have h2 : ((Witness.primes 0 : ℕ) : ℤ) = 2 := rfl
    apply map_ne_of_mul_add (levelConjInt j) (levelConjInt_bijective j) P (halfRootInt j)
    · have he : halfRootInt j * levelConjInt j (halfRootInt j) = ((4 : ℤ) : 𝓞 (level j)) := by
        apply algebraMap_int_injective j
        rw [map_mul, algebraMap_levelConjInt, algebraMap_halfRootInt, levelConj_halfRoot,
          map_intCast]
        have h := halfRoot_eq j
        push_cast
        linear_combination -h
      rw [he, Genus.intCast_mem_iff (p := Witness.primes 0) P, h2]
      norm_num
    · have he : halfRootInt j + levelConjInt j (halfRootInt j) = ((-1 : ℤ) : 𝓞 (level j)) := by
        apply algebraMap_int_injective j
        rw [map_add, algebraMap_levelConjInt, algebraMap_halfRootInt, levelConj_halfRoot,
          map_intCast]
        push_cast
        ring
      rw [he, Genus.intCast_mem_iff (p := Witness.primes 0) P, h2]
      norm_num
  · obtain ⟨hdvd, hndvd⟩ := tOdd_facts a ha
    set w : 𝓞 (level j) := rootInt j (rootIndex a) - (tOdd a : 𝓞 (level j)) with hw
    have hw' : algebraMap (𝓞 (level j)) (level j) w =
        rootLevel j (rootIndex a) - (tOdd a : level j) := by
      rw [hw, map_sub, algebraMap_rootInt, map_intCast]
    have hcw : algebraMap (𝓞 (level j)) (level j) (levelConjInt j w) =
        -rootLevel j (rootIndex a) - (tOdd a : level j) := by
      rw [algebraMap_levelConjInt, hw', map_sub, levelConj_rootLevel, map_intCast]
    apply map_ne_of_mul_add (levelConjInt j) (levelConjInt_bijective j) P w
    · have he : w * levelConjInt j w =
          ((tOdd a ^ 2 - dInt (rootIndex a) : ℤ) : 𝓞 (level j)) := by
        apply algebraMap_int_injective j
        rw [map_mul, hcw, hw', map_intCast]
        have h := rootLevel_sq j (rootIndex a)
        push_cast at h ⊢
        linear_combination -h
      rw [he, Genus.intCast_mem_iff (p := Witness.primes a) P]
      exact hdvd
    · have he : w + levelConjInt j w = ((-2 * tOdd a : ℤ) : 𝓞 (level j)) := by
        apply algebraMap_int_injective j
        rw [map_add, hcw, hw', map_intCast]
        push_cast
        ring
      rw [he, Genus.intCast_mem_iff (p := Witness.primes a) P]
      exact hndvd

end UnitDistance.Sqrt241.V2
