module

public import UnitDistance.Sqrt241.CanonicalWide
public import UnitDistance.Sqrt241.Wide.Identities

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Basic facts about the radicands of `E_W`

`rootA i ^ 2 = a_i` and `rootB i ^ 2 = b_i` with `a_i, b_i ∈ B` written as `c + d √241`
(products of Kummer radicands reduced by `√241² = 241`), and `wideRadicand i` is the polynomial
`Wide.betaO` of `Wide/Identities.lean` evaluated at `(√241, rootA i, rootB i)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Wide

open CanonicalGenus CanonicalWide

theorem rootA_sq_0 : rootA 0 ^ 2 = 837220446735 * baseRoot / 2 - 12997156474395 / 2 := by
  simp only [rootA, Fin.isValue, Matrix.cons_val_zero, mul_pow, genusRoot_sq]
  simp only [radicand, radicandA, radicandB, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  push_cast
  linear_combination (-1585545314850 * baseRoot ^ 4 + 49228562268018 * baseRoot ^ 3 -
    2414189254227 * baseRoot ^ 2 / 2 - 23653207875853669 * baseRoot / 2 +
    183598228765810533 / 2) * baseRoot_sq

theorem rootA_sq_1 : rootA 1 ^ 2 = -13722675 * baseRoot + 213033204 := by
  simp only [rootA, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, mul_pow, genusRoot_sq]
  simp only [radicand, radicandA, radicandB, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  push_cast
  linear_combination (284044272 - 18296900 * baseRoot) * baseRoot_sq

theorem rootA_sq_2 : rootA 2 ^ 2 = -144198668 * baseRoot + 2238565313 := by
  simp only [rootA, Fin.isValue, Matrix.cons_val, mul_pow, genusRoot_sq]
  simp only [radicand, radicandA, radicandB, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  push_cast
  linear_combination (2987039081 - 192117450 * baseRoot) * baseRoot_sq

theorem rootA_sq_3 : rootA 3 ^ 2 = -1303 * baseRoot + 20228 := by
  simp only [rootA, Fin.isValue, Matrix.cons_val, mul_pow, genusRoot_sq]
  simp only [radicand, radicandA, radicandB, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  push_cast
  linear_combination (42 : Closure) * baseRoot_sq

theorem rootB_sq_0 : rootB 0 ^ 2 = 24385 * baseRoot / 2 - 378557 / 2 := by
  simp only [rootB, Fin.isValue, Matrix.cons_val_zero, mul_pow, genusRoot_sq]
  simp only [radicand, radicandA, radicandB, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  push_cast
  linear_combination (-393 : Closure) * baseRoot_sq

theorem rootB_sq_1 : rootB 1 ^ 2 = -3 * baseRoot / 2 + 47 / 2 := by
  simp only [rootB, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, mul_pow, genusRoot_sq]
  simp only [radicand, radicandA, radicandB, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  push_cast
  linear_combination (8253 / 2 : Closure) * baseRoot_sq

theorem rootB_sq_2 : rootB 2 ^ 2 = 2 * baseRoot - 31 := by
  simp only [rootB, Fin.isValue, Matrix.cons_val, mul_pow, genusRoot_sq]
  simp only [radicand, radicandA, radicandB, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  push_cast
  ring

theorem rootB_sq_3 : rootB 3 ^ 2 = 221161 * baseRoot - 3433342 := by
  simp only [rootB, Fin.isValue, Matrix.cons_val, mul_pow, genusRoot_sq]
  simp only [radicand, radicandA, radicandB, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  push_cast
  linear_combination (-9148450 : Closure) * baseRoot_sq

theorem wideRadicand_0 : wideRadicand 0 = beta24 baseRoot (rootA 0) (rootB 0) := by
  simp only [wideRadicand, beta24, Fin.isValue, Matrix.cons_val_zero]
  ring

theorem wideRadicand_1 : wideRadicand 1 = beta20 baseRoot (rootA 1) (rootB 1) := by
  simp only [wideRadicand, beta20, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

theorem wideRadicand_2 : wideRadicand 2 = beta17 baseRoot (rootA 2) (rootB 2) := by
  simp only [wideRadicand, beta17, Fin.isValue, Matrix.cons_val]
  ring

theorem wideRadicand_3 : wideRadicand 3 = beta7 baseRoot (rootA 3) (rootB 3) := by
  simp only [wideRadicand, beta7, Fin.isValue, Matrix.cons_val]
  ring

end UnitDistance.Sqrt241.Wide
