module

public import UnitDistance.StudentProfiles
public import Mathlib.RingTheory.Polynomial.Bernstein

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact complex perturbation of a bicubic Bernstein polynomial

Finite mixed differences of the original coefficient table give the exact
Taylor expansion. The Bernstein partition of unity is reused from Mathlib.
This supplies the algebraic and norm-control foundation for the published
polynomial Student profile's zero-free complex tube.
-/

open scoped BigOperators

namespace UnitDistance.BernsteinTube

variable {R : Type*} [CommRing R]

/-- Evaluation of the ordinary Bernstein basis polynomial. -/
noncomputable def basis (n i : ℕ) (t : R) : R :=
  (n.choose i : R)*t^i*(1-t)^(n-i)

theorem basis_eq_eval (n i : ℕ) (t : R) :
    basis n i t = (bernsteinPolynomial R n i).eval t := by
  simp [basis, bernsteinPolynomial]

theorem basis_sum (n : ℕ) (t : R) : (∑ i ∈ Finset.range (n+1), basis n i t) = 1 := by
  have h := congrArg (Polynomial.eval t) (bernsteinPolynomial.sum R n)
  simpa only [← basis_eq_eval, Polynomial.eval_finsetSum, Polynomial.eval_one] using h

theorem basis_nonneg {n i : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ basis n i t := by unfold basis; positivity

/-- The actual bicubic polynomial represented by a coefficient array.
Only indices from zero through three occur. -/
noncomputable def patch (B : ℕ → ℕ → R) (t u : R) : R :=
  ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4, B i j*basis 3 i t*basis 3 j u

/-- Ordinary forward mixed differences; these are independently defined
from the coefficient table, not from the desired perturbation bound. -/
noncomputable def difference (B : ℕ → ℕ → R) (r s i j : ℕ) : R :=
  ∑ k ∈ Finset.range (r+1), ∑ l ∈ Finset.range (s+1),
    (-1:R)^(r-k+s-l)*(r.choose k : R)*(s.choose l : R)*B (i+k) (j+l)

/-- The `(r,s)` Taylor coefficient expressed in a lower-degree Bernstein
basis. The outside binomial factors account for division by `r!s!`. -/
noncomputable def taylorCoefficient (B : ℕ → ℕ → R) (r s : ℕ) (t u : R) : R :=
  (Nat.choose 3 r : R)*(Nat.choose 3 s : R)*
    ∑ i ∈ Finset.range (4-r), ∑ j ∈ Finset.range (4-s),
      difference B r s i j*basis (3-r) i t*basis (3-s) j u

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
/-- Exact finite Taylor expansion for a bicubic Bernstein polynomial over
any commutative ring, including complex perturbations of real arguments. -/
theorem patch_add (B : ℕ → ℕ → R) (t u h k : R) :
    patch B (t+h) (u+k) =
      ∑ r ∈ Finset.range 4, ∑ s ∈ Finset.range 4,
        taylorCoefficient B r s t u*h^r*k^s := by
  norm_num [patch, taylorCoefficient, difference, basis, Finset.sum_range_succ, Nat.choose]
  ring

end UnitDistance.BernsteinTube
