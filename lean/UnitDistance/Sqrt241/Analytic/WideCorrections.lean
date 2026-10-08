module

public import UnitDistance.Sqrt241.Analytic.WideTypes
public import UnitDistance.Sqrt241.Analytic.WideNumericsBasic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The local drops of the version-2 bridge

For each correction prime `p` the bridge subtracts a lower bound of the drop
`c_{E'}(p) - c_M(p)` of normalized local contributions, by the kind of `p`:

| kind | `E'` lower bound (`WideLocalTypes`) | `M` upper bound | drop |
| --- | --- | --- | --- |
| `dyadic` (`p = 2`) | `φ(2²)/32 + φ(2⁴)/64` | `φ(2⁴)/32` (type `(8,4)`) | `φ(2²)/32 - φ(2⁴)/64` |
| `one` | `φ(p²)/4` | `φ(p⁴)/4` (`f ≥ 4`) | `φ(p²)/4 - φ(p⁴)/4` |
| `two` | `φ(p²)/2` | `φ(p⁴)/4` (`f ≥ 4`) | `φ(p²)/2 - φ(p⁴)/4` |
-/

noncomputable section

namespace UnitDistance.Sqrt241.Analytic

open UnitDistance.NumberFieldAnalysis

/-- The kinds of correction primes of the version-2 bridge. -/
inductive WideKind
  | dyadic
  | one
  | two
  deriving DecidableEq

/-- Lower bound of the normalized contribution of `E'` at a prime of the given kind. -/
def kindLower : WideKind → (ℕ → ℝ) → ℕ → ℝ
  | .dyadic, φ, p => φ (p ^ 2) / 32 + φ (p ^ 4) / 64
  | .one, φ, p => φ (p ^ 2) / 4
  | .two, φ, p => φ (p ^ 2) / 2

/-- Upper bound of the normalized contribution of `M` at a prime of the given kind. -/
def kindUpper : WideKind → (ℕ → ℝ) → ℕ → ℝ
  | .dyadic, φ, p => φ (p ^ 4) / 32
  | .one, φ, p => φ (p ^ 4) / 4
  | .two, φ, p => φ (p ^ 4) / 4

/-- The certified drop at a prime of the given kind. -/
def lowerDropW (k : WideKind) (φ : ℕ → ℝ) (p : ℕ) : ℝ := kindLower k φ p - kindUpper k φ p

/-- The Euler-logarithm weight at `σ_W = 1 + 1/4411`. -/
def eulerWeightW : ℕ → ℝ := fun q => primeEulerLog q sigmaW

theorem eulerWeightW_isNormWeight : IsNormWeight eulerWeightW where
  nonneg q hq := primeEulerLog_nonneg hq (by norm_num [sigmaW])
  anti q Q hq hqQ := primeEulerLog_antitone hq hqQ (by norm_num [sigmaW])

end UnitDistance.Sqrt241.Analytic
