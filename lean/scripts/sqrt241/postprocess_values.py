#!/usr/bin/env python3
"""Value-specific edits of the generated `UnitDistance/Sqrt241/Geometry` copies.

Applied after `copy_geometry.py` (the `Fin 11 -> Fin 5` substitution is done
there):

* `69/32` (= Σ 1/(e f) over the eleven ℚ types) becomes `29/32` for the five
  types 2:(8,4), 3:(2,2), 5:(2,2), 29:(1,4), 7:(1,8);
* `WitnessPeriodSeparation`: the ℚ bound `24 ≤ periodLogDensity` fails for the
  new data (`periodLogDensity ≈ 15.69`); the separation is re-proved from
  comparisons with powers of two (`periodLogDensity ≥ (1579/70) log 2`,
  `logRD ≤ (33/4) log 2`).

Usage: postprocess_values.py GEOMETRY_DIR
"""
import os
import sys

TEXT_EDITS = [
    ('(69/32:ℝ)', '(29/32:ℝ)'),
    ('exactly 69/32 local blocks', 'exactly 29/32 local blocks'),
    ('prescribed eleven local degrees', 'prescribed five local degrees'),
    ('The eleven exact paired-prime', 'The five exact paired-prime'),
    ('The eleven independently specified', 'The five independently specified'),
    ('only on the eleven fixed sets', 'only on the five fixed sets'),
]

PERIOD_PROOFS = '''/-- Lower bound for a logarithm ratio from an integer power comparison. -/
private theorem log_mul_le_of_pow_le {x y : ℝ} (hx : 0 < x) (a b : ℕ) (h : x^a ≤ y^b) :
    (a : ℝ)*Real.log x ≤ (b : ℝ)*Real.log y := by
  rw [← Real.log_pow, ← Real.log_pow]
  exact Real.log_le_log (by positivity) h

/-- The ℚ lemma `24 ≤ periodLogDensity` fails for the five types
(`periodLogDensity ≈ 15.69`); comparisons with powers of two give the bound
in units of `log 2` that the separation below needs. -/
theorem periodLogDensity_lower : (1579/70 : ℝ)*Real.log 2 ≤ periodLogDensity := by
  have h3 := log_mul_le_of_pow_le (x := 2) (y := 3) (by norm_num) 19 12 (by norm_num)
  have h5 := log_mul_le_of_pow_le (x := 2) (y := 5) (by norm_num) 23 10 (by norm_num)
  have h29 := log_mul_le_of_pow_le (x := 2) (y := 29) (by norm_num) 34 7 (by norm_num)
  have h7 := log_mul_le_of_pow_le (x := 2) (y := 7) (by norm_num) 14 5 (by norm_num)
  push_cast at h3 h5 h29 h7
  norm_num [periodLogDensity, Fin.sum_univ_succ, periodPower, primes, ramification]
  linarith

theorem logRD_le : logRD ≤ (33/4 : ℝ)*Real.log 2 := by
  have h := log_mul_le_of_pow_le (x := 3615) (y := 2) (by norm_num) 1 12 (by norm_num)
  push_cast at h
  unfold logRD
  linarith

theorem logRD_le_seven : logRD ≤ 7 := by
  have h2 := log_two_precise.2
  norm_num only [div_one] at h2
  have h := logRD_le
  linarith

/-- The exact published finite periods satisfy the scalar condition with
the proved common Fourier constants `M = 2`, `sigma = 1`. -/
theorem period_fourier_separation :
    Real.log 2+2*Real.log 5+2 ≤ 2*Real.exp (periodLogDensity/2-logRD) := by
  have hH := periodLogDensity_lower
  have hL := logRD_le
  have h5 := log_mul_le_of_pow_le (x := 5) (y := 2) (by norm_num) 3 7 (by norm_num)
  push_cast at h5
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he := Real.add_one_le_exp (periodLogDensity/2-logRD)
  linarith

'''


def main():
    base = sys.argv[1]
    for fn in sorted(os.listdir(base)):
        if not fn.endswith('.lean'):
            continue
        path = os.path.join(base, fn)
        text = open(path).read()
        new = text
        for a, b in TEXT_EDITS:
            new = new.replace(a, b)
        if fn == 'WitnessPeriodSeparation.lean' and 'log_mul_le_of_pow_le' not in new:
            start = new.index('theorem periodLogDensity_lower')
            end = new.index('end UnitDistance.Sqrt241.Witness')
            new = new[:start] + PERIOD_PROOFS + new[end:]
        if new != text:
            open(path, 'w').write(new)
            print('edited', fn)


if __name__ == '__main__':
    main()
