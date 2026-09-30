module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The Golod–Shafarevich polynomial of the tower over `ℚ(√241)`

Port of `optimizedTowerPolynomial` (`FilteredOptimizedGolodShafarevich.lean`)
to the base `B = ℚ(√241)`. The design has eight generators and the local
blocks of `papers/0.04273/research/construction.md`:

* two real places, cost `c₁ = t²/(1+t)` each;
* four tame places above `3` and `5`, cut to `C₂ × C₂`,
  cost `c₂ = 2t - 1 + 1/(1+t)²` each;
* two dyadic places with local group `D` of order 32,
  cost `d_D = 3t - 1 + 1/P_D`, `P_D = (1+t)³(1+t²)²`, each;
* three `C₄` caps (the two primes above `29` and the inert prime `7`),
  cost `c₄ = t⁴/((1+t)(1+t²))` each;
* the single dyadic saving `s_D = t²(1 - t⁷/P_D)`.

The negative value at `t = 34/117` is an exact rational computation. The
arithmetic presentation that makes this polynomial an obstruction to finite
realizations is not formalized in this module.
-/

namespace UnitDistance.Sqrt241

/-- The block polynomial `1 - 8t + 2c₁ + 4c₂ + 2d_D - s_D + 3c₄`. -/
def towerPolynomial (t : ℚ) : ℚ :=
  1 - 8*t + 2*(t^2/(1+t)) + 4*(2*t-1+1/(1+t)^2) +
    2*(3*t-1+1/((1+t)^3*(1+t^2)^2)) -
    t^2*(1-t^7/((1+t)^3*(1+t^2)^2)) + 3*(t^4/((1+t)*(1+t^2)))

theorem towerPolynomial_value :
    towerPolynomial (34/117) = -187433948535241/88772225460489675 := by
  norm_num [towerPolynomial]

theorem towerPolynomial_negative : towerPolynomial (34/117) < 0 := by
  rw [towerPolynomial_value]
  norm_num

end UnitDistance.Sqrt241
