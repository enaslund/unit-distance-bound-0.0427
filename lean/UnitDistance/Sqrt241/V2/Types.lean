module

public import UnitDistance.Sqrt241.V2.Levels
public import UnitDistance.Sqrt241.V2.Interface
public import UnitDistance.Sqrt241.Levels.Unramified
public import UnitDistance.NonGaloisPrimeTypes

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Version 2: local types of the levels at `2, 3, 5, 29`, and `K_j / M` unramified

The level `K_j` need not be Galois over `ℚ`, but it sits between two Galois fields with the
same types: `M ≤ K_j ≤ K̃_j` (`levelClosure j`), both admissible for the symmetric input, so
`sym_ramification_residue` gives the types `(8,4), (2,2), (2,2), (1,4)` at `2, 3, 5, 29` in
`M` and in `K̃_j`. Ramification indices and residue degrees are multiplicative in towers, so
every prime of `K_j` above these primes has the same type (`level_types`), and the windows
`0` at `2, 3, 5, 29` (all primes of norm `p^f`) have `[K_j : ℚ]/(e f)` primes
(`level_window_count_small`).

`K̃_j` and `M` also have the same ramification index at every prime (`2, 3, 5` by the types,
`241` by `ramificationIdxIn_241`, `1` elsewhere), so every prime of `K_j` has the
ramification index of the prime of `M` below it, and `K_j / M` is unramified at the finite
places (`level_finiteUnramified`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.V2

open Tower Retained UnitDistance.NumberFieldAnalysis IsDedekindDomain UnitDistance.PrimeCompletion
open scoped NumberField

/-! ### Galois intermediate fields: every prime has the common type -/

section Galois

variable {L : IntermediateField ℚ Omega} [FiniteDimensional ℚ L] [IsGalois ℚ L]

theorem ramificationIdx_eq_ramificationIdxIn (p : ℕ) (W : Ideal (𝓞 L)) [W.IsPrime]
    [W.LiesOver (rationalPrimeIdeal p)] :
    W.ramificationIdx ℤ = (rationalPrimeIdeal p).ramificationIdxIn (𝓞 L) :=
  (Ideal.ramificationIdxIn_eq_ramificationIdx (rationalPrimeIdeal p) W Gal(L/ℚ)).symm

theorem inertiaDeg_eq_inertiaDegIn (p : ℕ) (W : Ideal (𝓞 L)) [W.IsPrime]
    [W.LiesOver (rationalPrimeIdeal p)] :
    W.inertiaDeg ℤ = (rationalPrimeIdeal p).inertiaDegIn (𝓞 L) :=
  (Ideal.inertiaDegIn_eq_inertiaDeg (rationalPrimeIdeal p) W Gal(L/ℚ)).symm

end Galois

/-! ### `M` and the Galois closures are admissible for the symmetric input -/

theorem M_kernelHat_sym : inputSym.kernelHat ≤ input.M.fixingSubgroup := by
  rw [input.M_fixingSubgroup]
  exact inputSym_kernelHat_le.trans input.kernelHat_le_core

theorem M_fixing_le_core : input.M.fixingSubgroup ≤ input.core :=
  le_of_eq input.M_fixingSubgroup

theorem v1Primes_prime (a : Fin 4) : (v1Primes a.castSucc).Prime := by
  fin_cases a <;> decide

/-! ### Types at `2, 3, 5, 29` -/

/-- **The types of the level `K_j` at `2, 3, 5, 29`**: every prime of `K_j` above
`p = 2, 3, 5, 29` has type `(8,4), (2,2), (2,2), (1,4)`. -/
theorem level_types (j : ℕ) (a : Fin 4) (P : Ideal (𝓞 (level j))) [P.IsPrime]
    [P.LiesOver (rationalPrimeIdeal (v1Primes a.castSucc))] :
    P.ramificationIdx ℤ = v1Ramification a.castSucc ∧
      P.inertiaDeg ℤ = v1ResidueDegree a.castSucc := by
  let := algebraOfLe (M_le_level j)
  let := algebraOfLe (level_le_levelClosure j)
  have hp := v1Primes_prime a
  have := rationalPrimeIdeal_isMaximal_of_prime hp
  have hp0 := rationalPrimeIdeal_ne_bot_of_prime hp
  obtain ⟨hMe, hMf⟩ := sym_ramification_residue (K := input.M) M_kernelHat_sym M_fixing_le_core a
  obtain ⟨hLe, hLf⟩ := sym_ramification_residue (K := levelClosure j)
    (inputSym_kernelHat_le_levelClosure j) (levelClosure_fixing_le_core j) a
  constructor
  · apply ramificationIdx_eq_of_sandwich (M := input.M) (L := levelClosure j) _ hp0
    · intro V _ _
      rw [ramificationIdx_eq_ramificationIdxIn (v1Primes a.castSucc) V, hMe]
    · intro W _ _
      rw [ramificationIdx_eq_ramificationIdxIn (v1Primes a.castSucc) W, hLe]
  · apply inertiaDeg_eq_of_sandwich (M := input.M) (L := levelClosure j) _ hp0
    · intro V _ _
      rw [inertiaDeg_eq_inertiaDegIn (v1Primes a.castSucc) V, hMf]
    · intro W _ _
      rw [inertiaDeg_eq_inertiaDegIn (v1Primes a.castSucc) W, hLf]

theorem witness_small (a : Fin 4) :
    Witness.primes a.castSucc = v1Primes a.castSucc ∧
      Witness.ramification a.castSucc = v1Ramification a.castSucc ∧
      Witness.residueDegree a.castSucc = v1ResidueDegree a.castSucc := by
  fin_cases a <;> decide

/-- The window `0` is the whole norm fiber. -/
def windowFiberZeroEquiv (K : Type*) [Field K] [NumberField K] (q : ℕ) :
    WindowFiber K q 0 ≃ PrimeNormFiber K q :=
  Equiv.subtypeEquivRight (fun P => and_iff_left P.asIdeal.zero_mem)

/-- **Window counts at `2, 3, 5, 29`.** -/
theorem level_window_count_small (j : ℕ) (a : Fin 4) :
    Nat.card (WindowFiber (level j) (Witness.primeNorm a.castSucc) 0) *
      (Witness.ramification a.castSucc * Witness.residueDegree a.castSucc) =
        Module.finrank ℚ (level j) := by
  obtain ⟨h1, h2, h3⟩ := witness_small a
  rw [Nat.card_congr (windowFiberZeroEquiv _ _), Witness.primeNorm, h1, h2, h3]
  have hp := v1Primes_prime a
  have hf : 0 < v1ResidueDegree a.castSucc := by fin_cases a <;> decide
  exact primeNormCount_mul_of_uniform (level j) _ hp _ _ hf
    (fun P _ _ => (level_types j a P).1) (fun P _ _ => (level_types j a P).2)

/-! ### `K_j / M` is unramified -/

/-- In finite Galois `K ≤ Ω` admissible for the symmetric input, with `M ≤ K`, the
ramification index at every prime is that of `M`. -/
theorem ramificationIdxIn_eq_M_sym {K : IntermediateField ℚ Omega} [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (hker : inputSym.kernelHat ≤ K.fixingSubgroup)
    (hcore : K.fixingSubgroup ≤ input.core) (hM : input.M ≤ K) (p : ℕ) (hp : p.Prime) :
    (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) =
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 input.M) := by
  have hKt := sym_ramification_residue hker hcore
  have hMt := sym_ramification_residue (K := input.M) M_kernelHat_sym M_fixing_le_core
  by_cases h2 : p = 2
  · subst h2
    exact (hKt 0).1.trans (hMt 0).1.symm
  by_cases h3 : p = 3
  · subst h3
    exact (hKt 1).1.trans (hMt 1).1.symm
  by_cases h5 : p = 5
  · subst h5
    exact (hKt 2).1.trans (hMt 2).1.symm
  have hBM : BinOmega ≤ input.M := BinOmega_le_EOmega.trans input.EOmega_le_M
  by_cases h241 : p = 241
  · subst h241
    rw [ramificationIdxIn_241 K (hBM.trans hM), ramificationIdxIn_241 input.M hBM]
  have hmem : (⟨p, hp⟩ : Nat.Primes).val ∉ ({2, 3, 5, 241} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h2, h3, h5, h241⟩
  rw [ramificationIdxIn_eq_one_away K ⟨p, hp⟩ hmem,
    ramificationIdxIn_eq_one_away input.M ⟨p, hp⟩ hmem]

/-- **`K_j / M` is unramified at every finite place.** -/
theorem level_finiteUnramified (j : ℕ) :
    letI := algebraOfLe (M_le_level j)
    FiniteUnramified input.M (level j) := by
  let := algebraOfLe (M_le_level j)
  let := algebraOfLe (level_le_levelClosure j)
  apply finiteUnramified_of_absolute_ramificationIdx_eq input.M (level j)
  intro P
  let V := P.under (𝓞 input.M)
  let : P.asIdeal.IsPrime := P.isPrime
  let : V.asIdeal.IsPrime := V.isPrime
  let p := (P.asIdeal.under ℤ).absNorm
  let : NeZero P.asIdeal := ⟨P.ne_bot⟩
  have hp : p.Prime := Nat.absNorm_under_prime P.asIdeal
  have hspan : rationalPrimeIdeal p = P.asIdeal.under ℤ := Int.ideal_span_absNorm_eq_self _
  have := rationalPrimeIdeal_isMaximal_of_prime hp
  let : P.asIdeal.LiesOver (rationalPrimeIdeal p) := hspan ▸ inferInstance
  let : P.asIdeal.LiesOver V.asIdeal := ⟨rfl⟩
  let : V.asIdeal.LiesOver (rationalPrimeIdeal p) := by
    constructor
    change rationalPrimeIdeal p = (P.asIdeal.under (𝓞 input.M)).under ℤ
    rw [Ideal.under_under]
    exact hspan
  have hKM := ramificationIdxIn_eq_M_sym (inputSym_kernelHat_le_levelClosure j)
    (levelClosure_fixing_le_core j) (M_le_levelClosure j) p hp
  rw [ramificationIdx_eq_ramificationIdxIn p V.asIdeal]
  apply ramificationIdx_eq_of_sandwich (M := input.M) (L := levelClosure j) _
    (rationalPrimeIdeal_ne_bot_of_prime hp)
  · intro W _ _
    rw [ramificationIdx_eq_ramificationIdxIn p W]
  · intro W _ _
    rw [ramificationIdx_eq_ramificationIdxIn p W, hKM]

end UnitDistance.Sqrt241.V2
