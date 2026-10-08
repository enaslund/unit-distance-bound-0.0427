module

public import UnitDistance.Sqrt241.Analytic.Fibers

@[expose] public section
set_option backward.privateInPublic true


/-!
# Interface: the local data of the wide field `E_W` used by the version-2 bridge

The version-2 analytic bridge (`Analytic.WideBridge`) compares `ζ_M` with `ζ_{E'}` for a
field `E' ⊆ M` of degree 8192 (the field `E_W = E(√γ₁₀, √γ₂₃, √γ₁₉, √γ₁₇)` of
`papers/0.043171`, Sections 8, 11b, 11c).  `E'` is Galois over `B = ℚ(√241)` but not
necessarily over `ℚ`, so its primes above one rational prime may have different types.
The bridge therefore uses only *lower bounds of normalized local contributions*:

`ContribLowerBound L p terms` says that for every nonnegative antitone weight `φ` the
normalized contribution of the primes of `L` above `p`,
`(∑_{P ∣ p} φ(N P)) / [L : ℚ]`, is at least `∑ (w, f) ∈ terms, w · φ(p^f)`.

If the primes of `L` above `p` contain disjoint sets `S_i` with `N P ≤ p^{f_i}` on `S_i` and
`#S_i ≥ w_i [L : ℚ]`, the bound holds (`contribLowerBound_of_classes`).  For `L` Galois over
`B`, the primes above a prime `𝔭` of `B` of degree one over `p` with `e(P|𝔭) = 1` and
`f(P|𝔭) ≤ f` number at least `[L : B]/f = [L : ℚ]/(2 f)`, each of norm at most `p^f`.

## The data (`WideLocalTypes`)

The radicand basis of `Genus` is used: index `i` is the radicand `α_i` of
`CanonicalGenus` (`−1`, `ε`, `π₂`, `π₂'`, `π₃`, `π₃'`, `π₅`, `π₅'`).  A prime of `B` of degree
one is named by `(p, r)` with `p ∣ r² − 241`: it is the prime above `p` containing
`√241 − r`.  Its *code* has bit `i` set iff `α_i` is a non-residue modulo that prime.
The residue degrees of `E_W/B` at these primes are those of the paper's rule `fW`
(`dihedral_ceiling3.py`, space `W4x`): `fW = 2` exactly at the places listed below
(norm ≤ 1000), `fW = 4` at the other places of norm ≤ 1000.

* `two`: above 2 (split in `B`), one prime of `B` has type `(e, f) = (8, 2)` in `E_W`,
  the other `(8, 4)`; so the contribution is at least `φ(2²)/32 + φ(2⁴)/64`.
* `censusOne p` (`p ∈ wideCensusOne`): the place `(p, r)` below has `e = 1`, `f ≤ 2`;
  contribution at least `φ(p²)/4`.
* `censusTwo p` (`p ∈ wideCensusTwo`): both places have `e = 1`, `f ≤ 2`; contribution at
  least `φ(p²)/2`.

| p | r | code | | p | r | code | | p | r | code |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 47 | 10 | 209 | | 59 | 8 | 105 | | 61 | 34 | 54 |
| 67 | 43 | 57 | | 83 | 18 | 43 | | 97 | 12 | 112 |
| 113 | 44 | 98 | | 181 | 153 | 6 | | 223 | 45 | 13 |
| 229 | 142 | 248 | | 257 | 193 | 172 | | 277 | 83 | 120 |
| 281 | 146 | 46 | | 331 | 127 | 117 | | 337 | 232 | 142 |
| 347 | 58 | 27 | | 401 | 38 | 226 | | 457 | 257 | 124 |
| 487 | 419 | 195 | | 509 | 196 | 234 | | 523 | 251 | 9 |
| 541 | 426 | 54 | | 563 | 233 | 219 | | 607 | 166 | 49 |
| 617 | 130 | 172 | | 673 | 75 | 190 | | 683 | 507 | 213 |
| 691 | 192 | 181 | | 719 | 509 | 175 | | 733 | 106 | 138 |
| 739 | 377 | 133 | | 773 | 342 | 86 | | 787 | 450 | 199 |
| 821 | 52 | 234 | | 823 | 66 | 13 | | 857 | 254 | 98 |
| 877 | 649 | 186 | | 881 | 765 | 46 | | 883 | 446 | 199 |
| 887 | 189 | 31 | | 937 | 581 | 142 | | 967 | 626 | 61 |

Both places (`censusTwo`): 151 (codes 177, 127), 191 (147, 109), 233 (82, 162),
421 (200, 196), 569 (238, 222), 743 (223, 225), 839 (147, 109), 991 (127, 177).
The inert prime 13 (code 204) and the ramified place above 241 (code 252) also have
`fW = 2`; they are not used.
-/

noncomputable section
open NumberField IsDedekindDomain
open scoped BigOperators

namespace UnitDistance.Sqrt241.Analytic

open UnitDistance.NumberFieldAnalysis

/-- The normalized contribution of the primes of `L` above `p` is at least
`∑ (w, f) ∈ terms, w · φ(p^f)` for every nonnegative antitone weight `φ`. -/
def ContribLowerBound (L : Type*) [Field L] [NumberField L] (p : Nat.Primes)
    (terms : List (ℚ × ℕ)) : Prop :=
  ∀ φ : ℕ → ℝ, IsNormWeight φ →
    (terms.map fun t => (t.1 : ℝ) * φ (p.val ^ t.2)).sum ≤
      normalizedRationalPrimeContribution L φ p

/-- Split census primes at which exactly one prime of `B` has `f_{E_W/B} = 2`. -/
def wideCensusOne : Finset ℕ :=
  {47, 59, 61, 67, 83, 97, 113, 181, 223, 229, 257, 277, 281, 331, 337, 347, 401, 457,
    487, 509, 523, 541, 563, 607, 617, 673, 683, 691, 719, 733, 739, 773, 787, 821, 823,
    857, 877, 881, 883, 887, 937, 967}

/-- Split census primes at which both primes of `B` have `f_{E_W/B} = 2`. -/
def wideCensusTwo : Finset ℕ := {151, 191, 233, 421, 569, 743, 839, 991}

/-- The local data of the wide field used by `Analytic.WideBridge`. -/
structure WideLocalTypes (E : Type*) [Field E] [NumberField E] : Prop where
  two : ContribLowerBound E ⟨2, Nat.prime_two⟩ [(1 / 32, 2), (1 / 64, 4)]
  censusOne : ∀ p : Nat.Primes, p.val ∈ wideCensusOne → ContribLowerBound E p [(1 / 4, 2)]
  censusTwo : ∀ p : Nat.Primes, p.val ∈ wideCensusTwo → ContribLowerBound E p [(1 / 2, 2)]

section Helper

variable (L : Type*) [Field L] [NumberField L]

/-- One class of primes: at least `w [L : ℚ]` primes above `p`, each of norm at most
`p^f`, contribute at least `w φ(p^f)` to the normalized contribution. -/
theorem sum_class_ge {φ : ℕ → ℝ} (hφ : IsNormWeight φ) (p : Nat.Primes)
    (S : Finset (PrimeFiber ℚ L (rationalPrimePlace p))) (w : ℝ) (f : ℕ) (hf : 0 < f)
    (hnorm : ∀ P ∈ S, Ideal.absNorm P.1.asIdeal ≤ p.val ^ f)
    (hcard : w * (Module.finrank ℚ L : ℝ) ≤ S.card) :
    w * (Module.finrank ℚ L : ℝ) * φ (p.val ^ f) ≤ ∑ P ∈ S, φ (Ideal.absNorm P.1.asIdeal) := by
  have hq : 1 < p.val ^ f := Nat.one_lt_pow hf.ne' p.property.one_lt
  have h0 : 0 ≤ φ (p.val ^ f) := hφ.nonneg _ hq
  calc w * (Module.finrank ℚ L : ℝ) * φ (p.val ^ f) ≤ (S.card : ℝ) * φ (p.val ^ f) :=
        mul_le_mul_of_nonneg_right hcard h0
    _ = ∑ _P ∈ S, φ (p.val ^ f) := by simp
    _ ≤ ∑ P ∈ S, φ (Ideal.absNorm P.1.asIdeal) := by
      apply Finset.sum_le_sum
      intro P hP
      exact hφ.anti _ _ (primeIdeal_absNorm_gt_one L P.1) (hnorm P hP)

/-- **Helper for `ContribLowerBound`.** Disjoint classes `S i` (`i ∈ I`) of primes above `p`,
with norms at most `p^{f i}` and at least `w i · [L : ℚ]` elements, give the bound with terms
`(w i, f i)`. -/
theorem contribLowerBound_of_classes (p : Nat.Primes) {ι : Type*} (I : List ι)
    (S : ι → Finset (PrimeFiber ℚ L (rationalPrimePlace p))) (w : ι → ℚ) (f : ι → ℕ)
    (hI : I.Nodup) (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j))
    (hf : ∀ i ∈ I, 0 < f i)
    (hnorm : ∀ i ∈ I, ∀ P ∈ S i, Ideal.absNorm P.1.asIdeal ≤ p.val ^ f i)
    (hcard : ∀ i ∈ I, ((w i : ℚ) : ℝ) * (Module.finrank ℚ L : ℝ) ≤ (S i).card) :
    ContribLowerBound L p (I.map fun i => (w i, f i)) := by
  intro φ hφ
  have hd : (0 : ℝ) < Module.finrank ℚ L := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := L)
  classical
  let U : Finset (PrimeFiber ℚ L (rationalPrimePlace p)) := I.toFinset.biUnion S
  have hdisjU : (I.toFinset : Set ι).PairwiseDisjoint S := by
    intro i hi j hj hij
    exact hdisj i (List.mem_toFinset.1 hi) j (List.mem_toFinset.1 hj) hij
  have hsumU : ∑ P ∈ U, φ (Ideal.absNorm P.1.asIdeal) =
      ∑ i ∈ I.toFinset, ∑ P ∈ S i, φ (Ideal.absNorm P.1.asIdeal) :=
    Finset.sum_biUnion hdisjU
  have hU : ∑ P ∈ U, φ (Ideal.absNorm P.1.asIdeal) ≤
      ∑ P : PrimeFiber ℚ L (rationalPrimePlace p), φ (Ideal.absNorm P.1.asIdeal) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro P _ _
    exact hφ.nonneg _ (primeIdeal_absNorm_gt_one L P.1)
  have hcls : ∀ i ∈ I.toFinset, ((w i : ℚ) : ℝ) * (Module.finrank ℚ L : ℝ) * φ (p.val ^ f i) ≤
      ∑ P ∈ S i, φ (Ideal.absNorm P.1.asIdeal) := by
    intro i hi
    have hi' := List.mem_toFinset.1 hi
    exact sum_class_ge L hφ p (S i) _ (f i) (hf i hi') (hnorm i hi') (hcard i hi')
  have hlist : ((I.map fun i => (w i, f i)).map fun t => (t.1 : ℝ) * φ (p.val ^ t.2)).sum =
      ∑ i ∈ I.toFinset, ((w i : ℚ) : ℝ) * φ (p.val ^ f i) := by
    rw [List.map_map, List.sum_toFinset _ hI]
    rfl
  rw [hlist]
  unfold normalizedRationalPrimeContribution
  rw [le_div_iff₀ hd, Finset.sum_mul]
  calc ∑ i ∈ I.toFinset, ((w i : ℚ) : ℝ) * φ (p.val ^ f i) * (Module.finrank ℚ L : ℝ)
      = ∑ i ∈ I.toFinset, ((w i : ℚ) : ℝ) * (Module.finrank ℚ L : ℝ) * φ (p.val ^ f i) := by
        apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ ∑ i ∈ I.toFinset, ∑ P ∈ S i, φ (Ideal.absNorm P.1.asIdeal) := Finset.sum_le_sum hcls
    _ = ∑ P ∈ U, φ (Ideal.absNorm P.1.asIdeal) := hsumU.symm
    _ ≤ _ := hU

end Helper

end UnitDistance.Sqrt241.Analytic
