module

public import UnitDistance.Sqrt241.Base.LocalRoots
public import UnitDistance.RationalLocalAbsoluteEmbedding

@[expose] public section
set_option backward.privateInPublic true

/-!
# The chosen places of the closure, restricted to `B = ℚ(√241)`

The ℚ package fixes, for every rational prime `p`, an embedding
`PrimeCompletion.absoluteEmbedding p : AlgebraicClosure ℚ →ₐ[ℚ] SeparableClosure (Base p)`
(the chosen place of the closure above `p`) and the decomposition group
`PrimeCompletion.AbsoluteDecomposition p` acting compatibly on both sides.
The choice is made by `Classical.choice`, so it is not known in advance
above which prime of `B` the chosen place lies.

When `241` is a square in `ℚ_p` (the split primes `2, 3, 5, 29`), the image of
`√241` is `±` a `p`-adic number (`placeRoot`), the restriction of the chosen
place to `B` is a `p`-adic embedding `placeEmb p : B →ₐ[ℚ] ℚ_p`, hence one of the
two named embeddings of `Base/LocalRoots.lean`, and every element of the chosen
decomposition group fixes `B` pointwise. At the inert prime `7` the image of
`√241` is not in the base field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Local

open NumberField CanonicalGenus Base UnitDistance.PrimeCompletion

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

section General

variable (p : Nat.Primes)

/-- The local value of `√241` at the chosen place, when `241` is a `p`-adic square. -/
theorem exists_placeRoot (h : IsSquare (241 : ℚ_[p.val])) :
    ∃ t : ℚ_[p.val], t ^ 2 = 241 ∧
      absoluteEmbedding p baseRoot =
        algebraMap (Base p) (SeparableClosure (Base p)) ((equiv p).symm t) := by
  obtain ⟨r, hr⟩ := h
  have hs : (absoluteEmbedding p baseRoot) ^ 2 =
      (algebraMap (Base p) (SeparableClosure (Base p)) ((equiv p).symm r)) ^ 2 := by
    rw [← map_pow, baseRoot_sq, ← map_pow, ← map_pow, sq r, ← hr, map_ofNat, map_ofNat,
      map_ofNat]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · exact ⟨r, by rw [sq, ← hr], h⟩
  · exact ⟨-r, by rw [neg_sq, sq, ← hr], by rw [h, map_neg, map_neg]⟩

/-- The `p`-adic number whose image is the image of `√241` under the chosen place. -/
def placeRoot (h : IsSquare (241 : ℚ_[p.val])) : ℚ_[p.val] := (exists_placeRoot p h).choose

theorem placeRoot_sq (h : IsSquare (241 : ℚ_[p.val])) : placeRoot p h ^ 2 = 241 :=
  (exists_placeRoot p h).choose_spec.1

theorem absoluteEmbedding_baseRoot (h : IsSquare (241 : ℚ_[p.val])) :
    absoluteEmbedding p baseRoot =
      algebraMap (Base p) (SeparableClosure (Base p)) ((equiv p).symm (placeRoot p h)) :=
  (exists_placeRoot p h).choose_spec.2

theorem aeval_placeRoot (h : IsSquare (241 : ℚ_[p.val])) :
    Polynomial.aeval (placeRoot p h) (minpoly ℚ powerBasis.gen) = 0 := by
  rw [powerBasis_gen, minpoly_sqrt241]
  simp [placeRoot_sq p h]

/-- The chosen place above `p`, restricted to `B`, as a `p`-adic embedding. -/
def placeEmb (h : IsSquare (241 : ℚ_[p.val])) : B →ₐ[ℚ] ℚ_[p.val] :=
  powerBasis.lift (placeRoot p h) (aeval_placeRoot p h)

@[simp] theorem placeEmb_sqrt241 (h : IsSquare (241 : ℚ_[p.val])) :
    placeEmb p h sqrt241 = placeRoot p h :=
  PowerBasis.lift_gen _ _ _

/-- The local embedding of `B` through `ℚ_p`. -/
def placeLocal (h : IsSquare (241 : ℚ_[p.val])) : B →ₐ[ℚ] SeparableClosure (Base p) :=
  (((algebraMap (Base p) (SeparableClosure (Base p))).comp
    ((equiv p).symm : ℚ_[p.val] →+* Base p)).comp (placeEmb p h : B →+* ℚ_[p.val])).toRatAlgHom

/-- On `B`, the chosen place is the `p`-adic embedding `placeEmb` followed by the
structure map of the local closure. -/
theorem absoluteEmbedding_coe (h : IsSquare (241 : ℚ_[p.val])) (x : B) :
    absoluteEmbedding p (x : Closure) =
      algebraMap (Base p) (SeparableClosure (Base p)) ((equiv p).symm (placeEmb p h x)) := by
  have hext : (absoluteEmbedding p).comp B.val = placeLocal p h := by
    apply algHom_ext
    change absoluteEmbedding p baseRoot = _
    rw [absoluteEmbedding_baseRoot p h]
    change _ = algebraMap (Base p) (SeparableClosure (Base p))
      ((equiv p).symm (placeEmb p h sqrt241))
    rw [placeEmb_sqrt241]
  exact congrArg (fun f : B →ₐ[ℚ] SeparableClosure (Base p) => f x) hext

/-- Every element of the chosen decomposition group fixes `B` when `241` is a
`p`-adic square. -/
theorem decomposition_fixes_B (h : IsSquare (241 : ℚ_[p.val]))
    (d : AbsoluteDecomposition p) (x : B) : d.val (x : Closure) = x := by
  apply (absoluteEmbedding p).injective
  change absoluteEmbedding p (d.val (x : Closure)) = absoluteEmbedding p (x : Closure)
  rw [← decomposition_commutes, absoluteEmbedding_coe p h x]
  exact AlgEquiv.commutes _ _

theorem decomposition_fixes_baseRoot (h : IsSquare (241 : ℚ_[p.val]))
    (d : AbsoluteDecomposition p) : d.val baseRoot = baseRoot :=
  decomposition_fixes_B p h d sqrt241

/-- The value of the chosen place on a radicand, in the root form of the Base tables. -/
theorem absoluteEmbedding_radicand (h : IsSquare (241 : ℚ_[p.val])) (i : Fin 8) :
    absoluteEmbedding p (radicand i) =
      algebraMap (Base p) (SeparableClosure (Base p)) ((equiv p).symm
        ((radicandA i : ℚ_[p.val]) + (radicandB i : ℚ_[p.val]) * placeRoot p h)) := by
  rw [← coe_alphaB, absoluteEmbedding_coe p h, algHom_alphaB, placeEmb_sqrt241]
  simp

end General

/-! ## The four split primes -/

/-- The split primes `2, 3, 5, 29` of `B`. -/
abbrev splitPrime : Fin 4 → Nat.Primes :=
  ![⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩, ⟨5, Nat.prime_five⟩, ⟨29, by norm_num⟩]

theorem isSquare_241_two : IsSquare (241 : ℚ_[2]) :=
  ⟨iota2 sqrt241, by rw [← sq]; exact (iota_sqrt241_sq root2 root2_mul_self).symm⟩

theorem isSquare_241_three : IsSquare (241 : ℚ_[3]) :=
  ⟨iota3 sqrt241, by rw [← sq]; exact (iota_sqrt241_sq root3 root3_mul_self).symm⟩

theorem isSquare_241_five : IsSquare (241 : ℚ_[5]) :=
  ⟨iota5 sqrt241, by rw [← sq]; exact (iota_sqrt241_sq root5 root5_mul_self).symm⟩

theorem isSquare_241_29 : IsSquare (241 : ℚ_[29]) :=
  ⟨iota29 sqrt241, by rw [← sq]; exact (iota_sqrt241_sq root29 root29_mul_self).symm⟩

theorem isSquare_241 (k : Fin 4) : IsSquare (241 : ℚ_[(splitPrime k).val]) := by
  fin_cases k
  · exact isSquare_241_two
  · exact isSquare_241_three
  · exact isSquare_241_five
  · exact isSquare_241_29

end UnitDistance.Sqrt241.Local
