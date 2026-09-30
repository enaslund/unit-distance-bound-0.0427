module

public import UnitDistance.Sqrt241.Base.Integers
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Ideal.Int

@[expose] public section
set_option backward.privateInPublic true

/-!
# Primes of `B = ℚ(√241)` above `2, 3, 5, 7, 29, 241`

* `2, 3, 5, 29` split: `(p) = 𝔭 𝔭'` with `𝔭 = (π_p)`, `𝔭' = (π_p')`, both of norm `p`,
  residue fields `ZMod p`. The residue maps are `evalHom r`, `ω ↦ r`, for the two roots `r`
  of `X² - X - 60` modulo `p`.
* `7` is inert: `(7)` is prime of norm `49`, residue field `GaloisField 7 2`.
* `241` ramifies: `(241) = (√241)²`, residue field `ZMod 241`.

Every prime ideal containing `p ∈ {2, 3, 5, 29}` is one of the two listed primes.
The names follow PARI's `idealprimedec` order (`kummer241.gp`).
-/

noncomputable section

namespace UnitDistance.Sqrt241.Base

open CanonicalGenus IntermediateField NumberField Ideal

/-! ## Coordinates and evaluation maps -/

/-- The first coordinate of `x = m + n ω`. -/
def coordM (x : 𝓞 B) : ℤ := (exists_mk x).choose

/-- The second coordinate of `x = m + n ω`. -/
def coordN (x : 𝓞 B) : ℤ := (exists_mk x).choose_spec.choose

theorem mk_coord (x : 𝓞 B) : mk (coordM x) (coordN x) = x :=
  (exists_mk x).choose_spec.choose_spec.symm

@[simp] theorem coordM_mk (m n : ℤ) : coordM (mk m n) = m :=
  (mk_inj.mp (mk_coord (mk m n))).1

@[simp] theorem coordN_mk (m n : ℤ) : coordN (mk m n) = n :=
  (mk_inj.mp (mk_coord (mk m n))).2

/-- The ring homomorphism `𝓞 B → R`, `m + n ω ↦ m + n r`, for a root `r` of `X² - X - 60`. -/
def evalHom {R : Type*} [CommRing R] (r : R) (hr : r * r = r + 60) : 𝓞 B →+* R where
  toFun x := (coordM x : R) + (coordN x : R) * r
  map_one' := by
    rw [← mk_one_zero, coordM_mk, coordN_mk]
    simp
  map_mul' x y := by
    obtain ⟨a, b, rfl⟩ := exists_mk x
    obtain ⟨c, d, rfl⟩ := exists_mk y
    simp only [mk_mul, coordM_mk, coordN_mk]
    push_cast
    linear_combination (-(b : R) * d) * hr
  map_zero' := by
    rw [← mk_zero_zero, coordM_mk, coordN_mk]
    simp
  map_add' x y := by
    obtain ⟨a, b, rfl⟩ := exists_mk x
    obtain ⟨c, d, rfl⟩ := exists_mk y
    simp only [mk_add, coordM_mk, coordN_mk]
    push_cast
    ring

@[simp] theorem evalHom_mk {R : Type*} [CommRing R] (r : R) (hr : r * r = r + 60) (m n : ℤ) :
    evalHom r hr (mk m n) = (m : R) + (n : R) * r := by
  change (coordM (mk m n) : R) + (coordN (mk m n) : R) * r = _
  rw [coordM_mk, coordN_mk]

@[simp] theorem evalHom_omega {R : Type*} [CommRing R] (r : R) (hr : r * r = r + 60) :
    evalHom r hr omega = r := by
  rw [← mk_zero_one, evalHom_mk]
  simp

theorem evalHom_surjective {p : ℕ} (r : ZMod p) (hr : r * r = r + 60) :
    Function.Surjective (evalHom r hr) := by
  intro y
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨mk z 0, ?_⟩
  rw [evalHom_mk]
  simp

/-! ## Principal primes of prime norm -/

theorem absNorm_span_eq {π : 𝓞 B} {p : ℕ} (hπ : (Algebra.norm ℤ π).natAbs = p) :
    absNorm (span {π}) = p := by
  rw [absNorm_span_singleton, hπ]

theorem isPrime_span_of_norm {π : 𝓞 B} {p : ℕ} (hp : p.Prime)
    (hπ : (Algebra.norm ℤ π).natAbs = p) : (span {π}).IsPrime :=
  isPrime_of_irreducible_absNorm (by rw [absNorm_span_eq hπ]; exact hp)

theorem ne_zero_of_norm {π : 𝓞 B} {p : ℕ} (hp : p.Prime)
    (hπ : (Algebra.norm ℤ π).natAbs = p) : π ≠ 0 := by
  rintro rfl
  rw [Algebra.norm_zero] at hπ
  simp only [Int.natAbs_zero] at hπ
  exact hp.ne_zero hπ.symm

theorem isMaximal_span_of_norm {π : 𝓞 B} {p : ℕ} (hp : p.Prime)
    (hπ : (Algebra.norm ℤ π).natAbs = p) : (span {π}).IsMaximal :=
  (isPrime_span_of_norm hp hπ).isMaximal
    (by rw [Ne, span_singleton_eq_bot]; exact ne_zero_of_norm hp hπ)

theorem prime_of_norm {π : 𝓞 B} {p : ℕ} (hp : p.Prime)
    (hπ : (Algebra.norm ℤ π).natAbs = p) : Prime π :=
  (span_singleton_prime (ne_zero_of_norm hp hπ)).mp (isPrime_span_of_norm hp hπ)

/-- A principal prime of prime norm `p` is the kernel of any ring map to `ZMod p` killing
its generator. -/
theorem span_eq_ker_of_norm {π : 𝓞 B} {p : ℕ} [hp : Fact p.Prime]
    (hπ : (Algebra.norm ℤ π).natAbs = p) (f : 𝓞 B →+* ZMod p) (hf : f π = 0) :
    span {π} = RingHom.ker f := by
  apply (isMaximal_span_of_norm hp.out hπ).eq_of_le
  · exact RingHom.ker_ne_top f
  · rw [span_le, Set.singleton_subset_iff]
    exact hf

/-! ## Lying over and inertia degrees -/

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance fact_prime_29 : Fact (Nat.Prime 29) := ⟨by norm_num⟩
instance fact_prime_241 : Fact (Nat.Prime 241) := ⟨prime_241⟩

/-- A prime ideal containing the rational prime `p` lies over `p`. -/
theorem liesOver_of_natCast_mem {P : Ideal (𝓞 B)} [hP : P.IsPrime] {p : ℕ} (hp : p.Prime)
    (h : (p : 𝓞 B) ∈ P) : P.LiesOver (span {(p : ℤ)}) := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  refine (Int.ideal_span_isMaximal_of_prime p).eq_of_le (IsPrime.under ℤ P).ne_top ?_
  rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_under]
  simpa using h

/-- A prime ideal lying over `p` contains `p`. -/
theorem natCast_mem_of_liesOver (P : Ideal (𝓞 B)) (p : ℕ) [P.LiesOver (span {(p : ℤ)})] :
    (p : 𝓞 B) ∈ P := by
  have h := (mem_of_liesOver P (span {(p : ℤ)}) (p : ℤ)).mp (mem_span_singleton_self _)
  simpa using h

theorem inertiaDeg_eq_of_absNorm {P : Ideal (𝓞 B)} [P.IsPrime] (p : ℕ) {f : ℕ}
    [P.LiesOver (span {(p : ℤ)})] (hp : p.Prime) (h : absNorm P = p ^ f) :
    P.inertiaDeg ℤ = f := by
  have h2 := pow_inertiaDeg p P
  rw [h] at h2
  exact Nat.pow_right_injective hp.two_le h2

/-- If `a b ∈ P` for a prime `P` and `(a)`, `(b)` are maximal, then `P` is `(a)` or `(b)`. -/
theorem eq_span_or_eq_span_of_mul_mem {P : Ideal (𝓞 B)} [hP : P.IsPrime] {a b : 𝓞 B}
    (ha : (span {a}).IsMaximal) (hb : (span {b}).IsMaximal) (h : a * b ∈ P) :
    P = span {a} ∨ P = span {b} := by
  rcases hP.mem_or_mem h with h1 | h1
  · exact Or.inl (ha.eq_of_le hP.ne_top (span_le.mpr (Set.singleton_subset_iff.mpr h1))).symm
  · exact Or.inr (hb.eq_of_le hP.ne_top (span_le.mpr (Set.singleton_subset_iff.mpr h1))).symm

/-! ## The split primes and the ramified prime -/

-- BEGIN Generated by scripts/sqrt241/generate_base_tables.py primes — do not edit by hand.
/-- The residue map at `((-6101 - 393√241)/2)`: `ω ↦ 0` modulo `2`. -/
def res2 : 𝓞 B →+* ZMod 2 := evalHom (0 : ZMod 2) (by decide)

/-- The prime ideal `((-6101 - 393√241)/2)` of norm `2`. -/
def P2 : Ideal (𝓞 B) := span {pi2}

theorem res2_pi2 : res2 pi2 = 0 := by
  rw [res2, pi2, evalHom_mk]; decide

theorem natAbs_norm_pi2 : (Algebra.norm ℤ pi2).natAbs = 2 := by
  rw [norm_pi2]; rfl

theorem prime_pi2 : Prime pi2 := prime_of_norm (by norm_num) natAbs_norm_pi2

theorem pi2_ne_zero : pi2 ≠ 0 := ne_zero_of_norm (by norm_num) natAbs_norm_pi2

theorem P2_eq_ker : P2 = RingHom.ker res2 :=
  span_eq_ker_of_norm natAbs_norm_pi2 res2 res2_pi2

theorem mem_P2 {x : 𝓞 B} : x ∈ P2 ↔ res2 x = 0 := by
  rw [P2_eq_ker, RingHom.mem_ker]

instance isMaximal_P2 : P2.IsMaximal := isMaximal_span_of_norm (by norm_num) natAbs_norm_pi2

instance isPrime_P2 : P2.IsPrime := isMaximal_P2.isPrime

theorem P2_ne_bot : P2 ≠ ⊥ := by
  rw [P2, Ne, span_singleton_eq_bot]; exact pi2_ne_zero

theorem absNorm_P2 : absNorm P2 = 2 := absNorm_span_eq natAbs_norm_pi2

theorem natCast_mem_P2 : ((2 : ℕ) : 𝓞 B) ∈ P2 := by
  rw [mem_P2, map_natCast]; decide

instance liesOver_P2 : P2.LiesOver (span {((2 : ℕ) : ℤ)}) :=
  liesOver_of_natCast_mem (by norm_num) natCast_mem_P2

theorem inertiaDeg_P2 : P2.inertiaDeg ℤ = 1 :=
  inertiaDeg_eq_of_absNorm 2 (by norm_num) (by rw [absNorm_P2]; norm_num)

/-- The residue field at `((-6101 - 393√241)/2)` is `ZMod 2`. -/
def residueEquiv2 : 𝓞 B ⧸ P2 ≃+* ZMod 2 :=
  (quotEquivOfEq P2_eq_ker).trans
    (RingHom.quotientKerEquivOfSurjective (evalHom_surjective _ _))

/-- The residue map at `((6101 - 393√241)/2)`: `ω ↦ 1` modulo `2`. -/
def res2' : 𝓞 B →+* ZMod 2 := evalHom (1 : ZMod 2) (by decide)

/-- The prime ideal `((6101 - 393√241)/2)` of norm `2`. -/
def P2' : Ideal (𝓞 B) := span {pi2'}

theorem res2'_pi2' : res2' pi2' = 0 := by
  rw [res2', pi2', evalHom_mk]; decide

theorem natAbs_norm_pi2' : (Algebra.norm ℤ pi2').natAbs = 2 := by
  rw [norm_pi2']; rfl

theorem prime_pi2' : Prime pi2' := prime_of_norm (by norm_num) natAbs_norm_pi2'

theorem pi2'_ne_zero : pi2' ≠ 0 := ne_zero_of_norm (by norm_num) natAbs_norm_pi2'

theorem P2'_eq_ker : P2' = RingHom.ker res2' :=
  span_eq_ker_of_norm natAbs_norm_pi2' res2' res2'_pi2'

theorem mem_P2' {x : 𝓞 B} : x ∈ P2' ↔ res2' x = 0 := by
  rw [P2'_eq_ker, RingHom.mem_ker]

instance isMaximal_P2' : P2'.IsMaximal := isMaximal_span_of_norm (by norm_num) natAbs_norm_pi2'

instance isPrime_P2' : P2'.IsPrime := isMaximal_P2'.isPrime

theorem P2'_ne_bot : P2' ≠ ⊥ := by
  rw [P2', Ne, span_singleton_eq_bot]; exact pi2'_ne_zero

theorem absNorm_P2' : absNorm P2' = 2 := absNorm_span_eq natAbs_norm_pi2'

theorem natCast_mem_P2' : ((2 : ℕ) : 𝓞 B) ∈ P2' := by
  rw [mem_P2', map_natCast]; decide

instance liesOver_P2' : P2'.LiesOver (span {((2 : ℕ) : ℤ)}) :=
  liesOver_of_natCast_mem (by norm_num) natCast_mem_P2'

theorem inertiaDeg_P2' : P2'.inertiaDeg ℤ = 1 :=
  inertiaDeg_eq_of_absNorm 2 (by norm_num) (by rw [absNorm_P2']; norm_num)

/-- The residue field at `((6101 - 393√241)/2)` is `ZMod 2`. -/
def residueEquiv2' : 𝓞 B ⧸ P2' ≃+* ZMod 2 :=
  (quotEquivOfEq P2'_eq_ker).trans
    (RingHom.quotientKerEquivOfSurjective (evalHom_surjective _ _))

/-- The residue map at `(31 - 2√241)`: `ω ↦ 0` modulo `3`. -/
def res3 : 𝓞 B →+* ZMod 3 := evalHom (0 : ZMod 3) (by decide)

/-- The prime ideal `(31 - 2√241)` of norm `3`. -/
def P3 : Ideal (𝓞 B) := span {pi3}

theorem res3_pi3 : res3 pi3 = 0 := by
  rw [res3, pi3, evalHom_mk]; decide

theorem natAbs_norm_pi3 : (Algebra.norm ℤ pi3).natAbs = 3 := by
  rw [norm_pi3]; rfl

theorem prime_pi3 : Prime pi3 := prime_of_norm (by norm_num) natAbs_norm_pi3

theorem pi3_ne_zero : pi3 ≠ 0 := ne_zero_of_norm (by norm_num) natAbs_norm_pi3

theorem P3_eq_ker : P3 = RingHom.ker res3 :=
  span_eq_ker_of_norm natAbs_norm_pi3 res3 res3_pi3

theorem mem_P3 {x : 𝓞 B} : x ∈ P3 ↔ res3 x = 0 := by
  rw [P3_eq_ker, RingHom.mem_ker]

instance isMaximal_P3 : P3.IsMaximal := isMaximal_span_of_norm (by norm_num) natAbs_norm_pi3

instance isPrime_P3 : P3.IsPrime := isMaximal_P3.isPrime

theorem P3_ne_bot : P3 ≠ ⊥ := by
  rw [P3, Ne, span_singleton_eq_bot]; exact pi3_ne_zero

theorem absNorm_P3 : absNorm P3 = 3 := absNorm_span_eq natAbs_norm_pi3

theorem natCast_mem_P3 : ((3 : ℕ) : 𝓞 B) ∈ P3 := by
  rw [mem_P3, map_natCast]; decide

instance liesOver_P3 : P3.LiesOver (span {((3 : ℕ) : ℤ)}) :=
  liesOver_of_natCast_mem (by norm_num) natCast_mem_P3

theorem inertiaDeg_P3 : P3.inertiaDeg ℤ = 1 :=
  inertiaDeg_eq_of_absNorm 3 (by norm_num) (by rw [absNorm_P3]; norm_num)

/-- The residue field at `(31 - 2√241)` is `ZMod 3`. -/
def residueEquiv3 : 𝓞 B ⧸ P3 ≃+* ZMod 3 :=
  (quotEquivOfEq P3_eq_ker).trans
    (RingHom.quotientKerEquivOfSurjective (evalHom_surjective _ _))

/-- The residue map at `(31 + 2√241)`: `ω ↦ 1` modulo `3`. -/
def res3' : 𝓞 B →+* ZMod 3 := evalHom (1 : ZMod 3) (by decide)

/-- The prime ideal `(31 + 2√241)` of norm `3`. -/
def P3' : Ideal (𝓞 B) := span {pi3'}

theorem res3'_pi3' : res3' pi3' = 0 := by
  rw [res3', pi3', evalHom_mk]; decide

theorem natAbs_norm_pi3' : (Algebra.norm ℤ pi3').natAbs = 3 := by
  rw [norm_pi3']; rfl

theorem prime_pi3' : Prime pi3' := prime_of_norm (by norm_num) natAbs_norm_pi3'

theorem pi3'_ne_zero : pi3' ≠ 0 := ne_zero_of_norm (by norm_num) natAbs_norm_pi3'

theorem P3'_eq_ker : P3' = RingHom.ker res3' :=
  span_eq_ker_of_norm natAbs_norm_pi3' res3' res3'_pi3'

theorem mem_P3' {x : 𝓞 B} : x ∈ P3' ↔ res3' x = 0 := by
  rw [P3'_eq_ker, RingHom.mem_ker]

instance isMaximal_P3' : P3'.IsMaximal := isMaximal_span_of_norm (by norm_num) natAbs_norm_pi3'

instance isPrime_P3' : P3'.IsPrime := isMaximal_P3'.isPrime

theorem P3'_ne_bot : P3' ≠ ⊥ := by
  rw [P3', Ne, span_singleton_eq_bot]; exact pi3'_ne_zero

theorem absNorm_P3' : absNorm P3' = 3 := absNorm_span_eq natAbs_norm_pi3'

theorem natCast_mem_P3' : ((3 : ℕ) : 𝓞 B) ∈ P3' := by
  rw [mem_P3', map_natCast]; decide

instance liesOver_P3' : P3'.LiesOver (span {((3 : ℕ) : ℤ)}) :=
  liesOver_of_natCast_mem (by norm_num) natCast_mem_P3'

theorem inertiaDeg_P3' : P3'.inertiaDeg ℤ = 1 :=
  inertiaDeg_eq_of_absNorm 3 (by norm_num) (by rw [absNorm_P3']; norm_num)

/-- The residue field at `(31 + 2√241)` is `ZMod 3`. -/
def residueEquiv3' : 𝓞 B ⧸ P3' ≃+* ZMod 3 :=
  (quotEquivOfEq P3'_eq_ker).trans
    (RingHom.quotientKerEquivOfSurjective (evalHom_surjective _ _))

/-- The residue map at `(326 - 21√241)`: `ω ↦ 1` modulo `5`. -/
def res5 : 𝓞 B →+* ZMod 5 := evalHom (1 : ZMod 5) (by decide)

/-- The prime ideal `(326 - 21√241)` of norm `5`. -/
def P5 : Ideal (𝓞 B) := span {pi5}

theorem res5_pi5 : res5 pi5 = 0 := by
  rw [res5, pi5, evalHom_mk]; decide

theorem natAbs_norm_pi5 : (Algebra.norm ℤ pi5).natAbs = 5 := by
  rw [norm_pi5]; rfl

theorem prime_pi5 : Prime pi5 := prime_of_norm (by norm_num) natAbs_norm_pi5

theorem pi5_ne_zero : pi5 ≠ 0 := ne_zero_of_norm (by norm_num) natAbs_norm_pi5

theorem P5_eq_ker : P5 = RingHom.ker res5 :=
  span_eq_ker_of_norm natAbs_norm_pi5 res5 res5_pi5

theorem mem_P5 {x : 𝓞 B} : x ∈ P5 ↔ res5 x = 0 := by
  rw [P5_eq_ker, RingHom.mem_ker]

instance isMaximal_P5 : P5.IsMaximal := isMaximal_span_of_norm (by norm_num) natAbs_norm_pi5

instance isPrime_P5 : P5.IsPrime := isMaximal_P5.isPrime

theorem P5_ne_bot : P5 ≠ ⊥ := by
  rw [P5, Ne, span_singleton_eq_bot]; exact pi5_ne_zero

theorem absNorm_P5 : absNorm P5 = 5 := absNorm_span_eq natAbs_norm_pi5

theorem natCast_mem_P5 : ((5 : ℕ) : 𝓞 B) ∈ P5 := by
  rw [mem_P5, map_natCast]; decide

instance liesOver_P5 : P5.LiesOver (span {((5 : ℕ) : ℤ)}) :=
  liesOver_of_natCast_mem (by norm_num) natCast_mem_P5

theorem inertiaDeg_P5 : P5.inertiaDeg ℤ = 1 :=
  inertiaDeg_eq_of_absNorm 5 (by norm_num) (by rw [absNorm_P5]; norm_num)

/-- The residue field at `(326 - 21√241)` is `ZMod 5`. -/
def residueEquiv5 : 𝓞 B ⧸ P5 ≃+* ZMod 5 :=
  (quotEquivOfEq P5_eq_ker).trans
    (RingHom.quotientKerEquivOfSurjective (evalHom_surjective _ _))

/-- The residue map at `(326 + 21√241)`: `ω ↦ 0` modulo `5`. -/
def res5' : 𝓞 B →+* ZMod 5 := evalHom (0 : ZMod 5) (by decide)

/-- The prime ideal `(326 + 21√241)` of norm `5`. -/
def P5' : Ideal (𝓞 B) := span {pi5'}

theorem res5'_pi5' : res5' pi5' = 0 := by
  rw [res5', pi5', evalHom_mk]; decide

theorem natAbs_norm_pi5' : (Algebra.norm ℤ pi5').natAbs = 5 := by
  rw [norm_pi5']; rfl

theorem prime_pi5' : Prime pi5' := prime_of_norm (by norm_num) natAbs_norm_pi5'

theorem pi5'_ne_zero : pi5' ≠ 0 := ne_zero_of_norm (by norm_num) natAbs_norm_pi5'

theorem P5'_eq_ker : P5' = RingHom.ker res5' :=
  span_eq_ker_of_norm natAbs_norm_pi5' res5' res5'_pi5'

theorem mem_P5' {x : 𝓞 B} : x ∈ P5' ↔ res5' x = 0 := by
  rw [P5'_eq_ker, RingHom.mem_ker]

instance isMaximal_P5' : P5'.IsMaximal := isMaximal_span_of_norm (by norm_num) natAbs_norm_pi5'

instance isPrime_P5' : P5'.IsPrime := isMaximal_P5'.isPrime

theorem P5'_ne_bot : P5' ≠ ⊥ := by
  rw [P5', Ne, span_singleton_eq_bot]; exact pi5'_ne_zero

theorem absNorm_P5' : absNorm P5' = 5 := absNorm_span_eq natAbs_norm_pi5'

theorem natCast_mem_P5' : ((5 : ℕ) : 𝓞 B) ∈ P5' := by
  rw [mem_P5', map_natCast]; decide

instance liesOver_P5' : P5'.LiesOver (span {((5 : ℕ) : ℤ)}) :=
  liesOver_of_natCast_mem (by norm_num) natCast_mem_P5'

theorem inertiaDeg_P5' : P5'.inertiaDeg ℤ = 1 :=
  inertiaDeg_eq_of_absNorm 5 (by norm_num) (by rw [absNorm_P5']; norm_num)

/-- The residue field at `(326 + 21√241)` is `ZMod 5`. -/
def residueEquiv5' : 𝓞 B ⧸ P5' ≃+* ZMod 5 :=
  (quotEquivOfEq P5'_eq_ker).trans
    (RingHom.quotientKerEquivOfSurjective (evalHom_surjective _ _))

/-- The residue map at `(-14127 + 910√241)`: `ω ↦ 2` modulo `29`. -/
def res29 : 𝓞 B →+* ZMod 29 := evalHom (2 : ZMod 29) (by decide)

/-- The prime ideal `(-14127 + 910√241)` of norm `29`. -/
def P29 : Ideal (𝓞 B) := span {pi29}

theorem res29_pi29 : res29 pi29 = 0 := by
  rw [res29, pi29, evalHom_mk]; decide

theorem natAbs_norm_pi29 : (Algebra.norm ℤ pi29).natAbs = 29 := by
  rw [norm_pi29]; rfl

theorem prime_pi29 : Prime pi29 := prime_of_norm (by norm_num) natAbs_norm_pi29

theorem pi29_ne_zero : pi29 ≠ 0 := ne_zero_of_norm (by norm_num) natAbs_norm_pi29

theorem P29_eq_ker : P29 = RingHom.ker res29 :=
  span_eq_ker_of_norm natAbs_norm_pi29 res29 res29_pi29

theorem mem_P29 {x : 𝓞 B} : x ∈ P29 ↔ res29 x = 0 := by
  rw [P29_eq_ker, RingHom.mem_ker]

instance isMaximal_P29 : P29.IsMaximal := isMaximal_span_of_norm (by norm_num) natAbs_norm_pi29

instance isPrime_P29 : P29.IsPrime := isMaximal_P29.isPrime

theorem P29_ne_bot : P29 ≠ ⊥ := by
  rw [P29, Ne, span_singleton_eq_bot]; exact pi29_ne_zero

theorem absNorm_P29 : absNorm P29 = 29 := absNorm_span_eq natAbs_norm_pi29

theorem natCast_mem_P29 : ((29 : ℕ) : 𝓞 B) ∈ P29 := by
  rw [mem_P29, map_natCast]; decide

instance liesOver_P29 : P29.LiesOver (span {((29 : ℕ) : ℤ)}) :=
  liesOver_of_natCast_mem (by norm_num) natCast_mem_P29

theorem inertiaDeg_P29 : P29.inertiaDeg ℤ = 1 :=
  inertiaDeg_eq_of_absNorm 29 (by norm_num) (by rw [absNorm_P29]; norm_num)

/-- The residue field at `(-14127 + 910√241)` is `ZMod 29`. -/
def residueEquiv29 : 𝓞 B ⧸ P29 ≃+* ZMod 29 :=
  (quotEquivOfEq P29_eq_ker).trans
    (RingHom.quotientKerEquivOfSurjective (evalHom_surjective _ _))

/-- The residue map at `(-14127 - 910√241)`: `ω ↦ 28` modulo `29`. -/
def res29' : 𝓞 B →+* ZMod 29 := evalHom (28 : ZMod 29) (by decide)

/-- The prime ideal `(-14127 - 910√241)` of norm `29`. -/
def P29' : Ideal (𝓞 B) := span {pi29'}

theorem res29'_pi29' : res29' pi29' = 0 := by
  rw [res29', pi29', evalHom_mk]; decide

theorem natAbs_norm_pi29' : (Algebra.norm ℤ pi29').natAbs = 29 := by
  rw [norm_pi29']; rfl

theorem prime_pi29' : Prime pi29' := prime_of_norm (by norm_num) natAbs_norm_pi29'

theorem pi29'_ne_zero : pi29' ≠ 0 := ne_zero_of_norm (by norm_num) natAbs_norm_pi29'

theorem P29'_eq_ker : P29' = RingHom.ker res29' :=
  span_eq_ker_of_norm natAbs_norm_pi29' res29' res29'_pi29'

theorem mem_P29' {x : 𝓞 B} : x ∈ P29' ↔ res29' x = 0 := by
  rw [P29'_eq_ker, RingHom.mem_ker]

instance isMaximal_P29' : P29'.IsMaximal := isMaximal_span_of_norm (by norm_num) natAbs_norm_pi29'

instance isPrime_P29' : P29'.IsPrime := isMaximal_P29'.isPrime

theorem P29'_ne_bot : P29' ≠ ⊥ := by
  rw [P29', Ne, span_singleton_eq_bot]; exact pi29'_ne_zero

theorem absNorm_P29' : absNorm P29' = 29 := absNorm_span_eq natAbs_norm_pi29'

theorem natCast_mem_P29' : ((29 : ℕ) : 𝓞 B) ∈ P29' := by
  rw [mem_P29', map_natCast]; decide

instance liesOver_P29' : P29'.LiesOver (span {((29 : ℕ) : ℤ)}) :=
  liesOver_of_natCast_mem (by norm_num) natCast_mem_P29'

theorem inertiaDeg_P29' : P29'.inertiaDeg ℤ = 1 :=
  inertiaDeg_eq_of_absNorm 29 (by norm_num) (by rw [absNorm_P29']; norm_num)

/-- The residue field at `(-14127 - 910√241)` is `ZMod 29`. -/
def residueEquiv29' : 𝓞 B ⧸ P29' ≃+* ZMod 29 :=
  (quotEquivOfEq P29'_eq_ker).trans
    (RingHom.quotientKerEquivOfSurjective (evalHom_surjective _ _))

/-- The residue map at `(√241)`: `ω ↦ 121` modulo `241`. -/
def res241 : 𝓞 B →+* ZMod 241 := evalHom (121 : ZMod 241) (by decide)

/-- The prime ideal `(√241)` of norm `241`. -/
def P241 : Ideal (𝓞 B) := span {sqrt241Int}

theorem res241_sqrt241Int : res241 sqrt241Int = 0 := by
  rw [res241, sqrt241Int, evalHom_mk]; decide

theorem natAbs_norm_sqrt241Int : (Algebra.norm ℤ sqrt241Int).natAbs = 241 := by
  rw [norm_sqrt241Int]; rfl

theorem prime_sqrt241Int : Prime sqrt241Int := prime_of_norm (by norm_num) natAbs_norm_sqrt241Int

theorem sqrt241Int_ne_zero : sqrt241Int ≠ 0 := ne_zero_of_norm (by norm_num) natAbs_norm_sqrt241Int

theorem P241_eq_ker : P241 = RingHom.ker res241 :=
  span_eq_ker_of_norm natAbs_norm_sqrt241Int res241 res241_sqrt241Int

theorem mem_P241 {x : 𝓞 B} : x ∈ P241 ↔ res241 x = 0 := by
  rw [P241_eq_ker, RingHom.mem_ker]

instance isMaximal_P241 : P241.IsMaximal := isMaximal_span_of_norm (by norm_num) natAbs_norm_sqrt241Int

instance isPrime_P241 : P241.IsPrime := isMaximal_P241.isPrime

theorem P241_ne_bot : P241 ≠ ⊥ := by
  rw [P241, Ne, span_singleton_eq_bot]; exact sqrt241Int_ne_zero

theorem absNorm_P241 : absNorm P241 = 241 := absNorm_span_eq natAbs_norm_sqrt241Int

theorem natCast_mem_P241 : ((241 : ℕ) : 𝓞 B) ∈ P241 := by
  rw [mem_P241, map_natCast]; decide

instance liesOver_P241 : P241.LiesOver (span {((241 : ℕ) : ℤ)}) :=
  liesOver_of_natCast_mem (by norm_num) natCast_mem_P241

theorem inertiaDeg_P241 : P241.inertiaDeg ℤ = 1 :=
  inertiaDeg_eq_of_absNorm 241 (by norm_num) (by rw [absNorm_P241]; norm_num)

/-- The residue field at `(√241)` is `ZMod 241`. -/
def residueEquiv241 : 𝓞 B ⧸ P241 ≃+* ZMod 241 :=
  (quotEquivOfEq P241_eq_ker).trans
    (RingHom.quotientKerEquivOfSurjective (evalHom_surjective _ _))
-- END Generated by scripts/sqrt241/generate_base_tables.py primes.


/-! ## Factorizations of `2, 3, 5, 29, 241` -/

theorem span_two_eq : span {(2 : 𝓞 B)} = P2 * P2' := by
  rw [P2, P2', span_singleton_mul_span_singleton, pi2_mul_pi2']

theorem span_three_eq : span {(3 : 𝓞 B)} = P3 * P3' := by
  rw [P3, P3', span_singleton_mul_span_singleton, pi3_mul_pi3', span_singleton_neg]

theorem span_five_eq : span {(5 : 𝓞 B)} = P5 * P5' := by
  rw [P5, P5', span_singleton_mul_span_singleton, pi5_mul_pi5', span_singleton_neg]

theorem span_29_eq : span {(29 : 𝓞 B)} = P29 * P29' := by
  rw [P29, P29', span_singleton_mul_span_singleton, pi29_mul_pi29']

/-- `241` ramifies: `(241) = (√241)²`. -/
theorem span_241_eq : span {(241 : 𝓞 B)} = P241 ^ 2 := by
  rw [P241, span_singleton_pow, sq, sqrt241Int_mul_self]

theorem P2_ne_P2' : P2 ≠ P2' := by
  intro h
  have h1 : pi2' ∈ P2 := h ▸ mem_span_singleton_self _
  rw [mem_P2, res2, pi2', evalHom_mk] at h1
  revert h1; decide

theorem P3_ne_P3' : P3 ≠ P3' := by
  intro h
  have h1 : pi3' ∈ P3 := h ▸ mem_span_singleton_self _
  rw [mem_P3, res3, pi3', evalHom_mk] at h1
  revert h1; decide

theorem P5_ne_P5' : P5 ≠ P5' := by
  intro h
  have h1 : pi5' ∈ P5 := h ▸ mem_span_singleton_self _
  rw [mem_P5, res5, pi5', evalHom_mk] at h1
  revert h1; decide

theorem P29_ne_P29' : P29 ≠ P29' := by
  intro h
  have h1 : pi29' ∈ P29 := h ▸ mem_span_singleton_self _
  rw [mem_P29, res29, pi29', evalHom_mk] at h1
  revert h1; decide

/-- Every prime ideal containing `2` is `𝔭₂` or `𝔭₂'`. -/
theorem eq_P2_or_P2' {P : Ideal (𝓞 B)} [P.IsPrime] (h : (2 : 𝓞 B) ∈ P) :
    P = P2 ∨ P = P2' := by
  rw [← pi2_mul_pi2'] at h
  exact eq_span_or_eq_span_of_mul_mem isMaximal_P2 isMaximal_P2' h

/-- Every prime ideal containing `3` is `𝔭₃` or `𝔭₃'`. -/
theorem eq_P3_or_P3' {P : Ideal (𝓞 B)} [P.IsPrime] (h : (3 : 𝓞 B) ∈ P) :
    P = P3 ∨ P = P3' := by
  have h' : pi3 * pi3' ∈ P := by rw [pi3_mul_pi3']; exact P.neg_mem h
  exact eq_span_or_eq_span_of_mul_mem isMaximal_P3 isMaximal_P3' h'

/-- Every prime ideal containing `5` is `𝔭₅` or `𝔭₅'`. -/
theorem eq_P5_or_P5' {P : Ideal (𝓞 B)} [P.IsPrime] (h : (5 : 𝓞 B) ∈ P) :
    P = P5 ∨ P = P5' := by
  have h' : pi5 * pi5' ∈ P := by rw [pi5_mul_pi5']; exact P.neg_mem h
  exact eq_span_or_eq_span_of_mul_mem isMaximal_P5 isMaximal_P5' h'

/-- Every prime ideal containing `29` is `𝔭₂₉` or `𝔭₂₉'`. -/
theorem eq_P29_or_P29' {P : Ideal (𝓞 B)} [P.IsPrime] (h : (29 : 𝓞 B) ∈ P) :
    P = P29 ∨ P = P29' := by
  rw [← pi29_mul_pi29'] at h
  exact eq_span_or_eq_span_of_mul_mem isMaximal_P29 isMaximal_P29' h

/-- The only prime ideal containing `241` is `(√241)`. -/
theorem eq_P241 {P : Ideal (𝓞 B)} [P.IsPrime] (h : (241 : 𝓞 B) ∈ P) : P = P241 := by
  rw [← sqrt241Int_mul_self] at h
  exact (eq_span_or_eq_span_of_mul_mem isMaximal_P241 isMaximal_P241 h).elim id id

/-! ## The Galois action on the primes -/

theorem map_sigmaInt_span (x : 𝓞 B) : (span {x}).map sigmaInt = span {sigmaInt x} := by
  rw [Ideal.map_span, Set.image_singleton]

theorem map_sigmaInt_P2 : P2.map sigmaInt = P2' := by
  rw [P2, map_sigmaInt_span, sigmaInt_pi2, span_singleton_neg]; rfl

theorem map_sigmaInt_P2' : P2'.map sigmaInt = P2 := by
  rw [P2', map_sigmaInt_span, sigmaInt_pi2', span_singleton_neg]; rfl

theorem map_sigmaInt_P3 : P3.map sigmaInt = P3' := by
  rw [P3, map_sigmaInt_span, sigmaInt_pi3]; rfl

theorem map_sigmaInt_P3' : P3'.map sigmaInt = P3 := by
  rw [P3', map_sigmaInt_span, sigmaInt_pi3']; rfl

theorem map_sigmaInt_P5 : P5.map sigmaInt = P5' := by
  rw [P5, map_sigmaInt_span, sigmaInt_pi5]; rfl

theorem map_sigmaInt_P5' : P5'.map sigmaInt = P5 := by
  rw [P5', map_sigmaInt_span, sigmaInt_pi5']; rfl

theorem map_sigmaInt_P29 : P29.map sigmaInt = P29' := by
  rw [P29, map_sigmaInt_span, sigmaInt_pi29]; rfl

theorem map_sigmaInt_P29' : P29'.map sigmaInt = P29 := by
  rw [P29', map_sigmaInt_span, sigmaInt_pi29']; rfl

theorem sigmaInt_sqrt241Int : sigmaInt sqrt241Int = -sqrt241Int := by
  rw [sqrt241Int, sigmaInt_mk, mk_neg, mk_inj]; norm_num

theorem map_sigmaInt_P241 : P241.map sigmaInt = P241 := by
  rw [P241, map_sigmaInt_span, sigmaInt_sqrt241Int, span_singleton_neg]

/-! ## The inert prime `7` -/

theorem intCast_dvd_mk_iff {k : ℤ} {a b : ℤ} :
    (k : 𝓞 B) ∣ mk a b ↔ k ∣ a ∧ k ∣ b := by
  have hkmk : (k : 𝓞 B) = mk k 0 := (mk_intCast k).symm
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨c, d, rfl⟩ := exists_mk y
    rw [hkmk, mk_mul, mk_inj] at hy
    exact ⟨⟨c, by linarith [hy.1]⟩, ⟨d, by linarith [hy.2]⟩⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    refine ⟨mk c d, ?_⟩
    rw [hkmk, mk_mul, mk_inj]
    constructor <;> ring

theorem zmod7_no_zero_divisors : ∀ a b c d : ZMod 7, a * c + 60 * b * d = 0 →
    a * d + b * c + b * d = 0 → (a = 0 ∧ b = 0) ∨ (c = 0 ∧ d = 0) := by
  decide

theorem norm_seven : Algebra.norm ℤ (7 : 𝓞 B) = 49 := by
  rw [← mk_ofNat, norm_mk]; norm_num

/-- `7` stays prime in `B`. -/
theorem prime_seven : Prime (7 : 𝓞 B) := by
  have h7 : (7 : 𝓞 B) = ((7 : ℤ) : 𝓞 B) := by norm_cast
  refine ⟨?_, ?_, ?_⟩
  · rw [← mk_ofNat, Ne, ← mk_zero_zero, mk_inj]; norm_num
  · intro hu
    have h := hu.map (Algebra.norm ℤ)
    rw [norm_seven, Int.isUnit_iff] at h
    omega
  · intro x y hxy
    obtain ⟨a, b, rfl⟩ := exists_mk x
    obtain ⟨c, d, rfl⟩ := exists_mk y
    have key : ∀ z : ℤ, (7 : ℤ) ∣ z ↔ (z : ZMod 7) = 0 := fun z ↦ by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num
    rw [mk_mul, h7, intCast_dvd_mk_iff] at hxy
    rw [h7, intCast_dvd_mk_iff, intCast_dvd_mk_iff]
    simp only [key] at hxy ⊢
    push_cast at hxy ⊢
    exact zmod7_no_zero_divisors _ _ _ _ hxy.1 hxy.2

/-- The inert prime `(7)`, of norm `49`. -/
def P7 : Ideal (𝓞 B) := span {7}

instance isPrime_P7 : P7.IsPrime :=
  (span_singleton_prime prime_seven.ne_zero).mpr prime_seven

theorem P7_ne_bot : P7 ≠ ⊥ := by
  rw [P7, Ne, span_singleton_eq_bot]; exact prime_seven.ne_zero

instance isMaximal_P7 : P7.IsMaximal := isPrime_P7.isMaximal P7_ne_bot

theorem absNorm_P7 : absNorm P7 = 49 := by
  rw [P7, absNorm_span_singleton, norm_seven]; rfl

instance liesOver_P7 : P7.LiesOver (span {((7 : ℕ) : ℤ)}) :=
  liesOver_of_natCast_mem (by norm_num) (by rw [P7]; exact mem_span_singleton_self _)

theorem inertiaDeg_P7 : P7.inertiaDeg ℤ = 2 :=
  inertiaDeg_eq_of_absNorm 7 (by norm_num) (by rw [absNorm_P7]; norm_num)

/-- The only prime ideal containing `7` is `(7)`. -/
theorem eq_P7 {P : Ideal (𝓞 B)} [hP : P.IsPrime] (h : (7 : 𝓞 B) ∈ P) : P = P7 :=
  (isMaximal_P7.eq_of_le hP.ne_top (span_le.mpr (Set.singleton_subset_iff.mpr h))).symm

theorem map_sigmaInt_P7 : P7.map sigmaInt = P7 := by
  rw [P7, map_sigmaInt_span, map_ofNat]

theorem natCard_quotient_P7 : Nat.card (𝓞 B ⧸ P7) = 49 := by
  rw [← absNorm_P7, absNorm_apply, Submodule.cardQuot_apply]

instance finite_quotient_P7 : Finite (𝓞 B ⧸ P7) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_quotient_P7]; norm_num)

/-- The residue field at `7` is the field with `49` elements. -/
def residueEquiv7 : 𝓞 B ⧸ P7 ≃+* GaloisField 7 2 :=
  letI : Field (𝓞 B ⧸ P7) := Ideal.Quotient.field P7
  letI : Fintype (𝓞 B ⧸ P7) := Fintype.ofFinite _
  letI : Fintype (GaloisField 7 2) := Fintype.ofFinite _
  FiniteField.ringEquivOfCardEq (K := 𝓞 B ⧸ P7) (K' := GaloisField 7 2) (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, natCard_quotient_P7,
      GaloisField.card 7 2 (by norm_num)]
    norm_num)

end UnitDistance.Sqrt241.Base
