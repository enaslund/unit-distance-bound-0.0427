# Quartic-field trace check for one mixed quadratic row

`quartic_field_trace_check.py` checks the selected mixed quadratic Hecke row
(H6 mask 1586, twist `-1`, `N=981`) from the defining field polynomial,
independently of the row's quadratic-character coefficient recurrence. Its
guarded research-checkout run exited 0, admitted with 13.6 GiB host memory
available. The exact result is in `quartic_field_trace_check.json`.

The pinned sector has quadratic base `F = Q(√-35)` and radicand
`η = 17 + 2√-35`. For `u² = -η`, direct elimination gives

```text
F:          X² + 35
quartic K:  X⁴ + 34X² + 429.
```

The norm of `-η` from `F` to `Q` is 429, which is not a rational square;
thus `-η` is not a square in `F`, and the quartic has degree four.
The monic quartic has polynomial discriminant
`16 * 429 * 560² = 2152550400`, with prime divisors only
`2, 3, 5, 7, 11, 13`. At every other prime through 981, Dedekind's
factorization theorem identifies roots of these two polynomials modulo `p`
with their degree-one prime counts. The difference of those counts is the
Frobenius trace of the two-dimensional induction attached to the quadratic
extension `K/F`. The checker enumerates roots directly modulo each prime and
compares that trace with the independently regenerated `a_p` from the selected
Hecke row. All 159 eligible primes match, including 17, which is deleted from
the global certificate for a separate local reason but is unramified here.
The trace distribution is `-2: 15`, `0: 122`, `2: 22`.

For every good prime with `p² ≤ 981`, the checker also counts polynomial
roots over `F_(p²) = F_p[w]/(w²-d)` for a tested quadratic nonsquare `d`.
The root-count difference gives `tr(Frob_p²)` for the same induced
two-dimensional representation, so the Euler coefficient is
`a_(p²) = (tr(Frob_p)² + tr(Frob_p²))/2`. All five eligible
prime-square coefficients match the source-bound row:

| `p` | `tr(Frob_p)` | `tr(Frob_p²)` | `a_(p²)` |
| ---: | ---: | ---: | ---: |
| 17 | 2 | 2 | 3 |
| 19 | 0 | 2 | 1 |
| 23 | 0 | -2 | -1 |
| 29 | 2 | 2 | 3 |
| 31 | 0 | -2 | -1 |

The compact fixture SHA-256 is
`5fd9c83deb0fcdef56d314657ae8e1c7408c5508e652834e32cdabc3de234200`.
The imported coefficient helper is separately pinned at SHA-256
`3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329`.
The regenerated full 981-coefficient vector matches the source-bound hash
`baec4879c9e60ab3f2e657ff9f4d9cac64a39eebc3aa123495844f19e3ef654c`.
In the research checkout, every copied field in the compact sector and row
was compared with the pinned full arithmetic and moment tables; the
standalone package pins their hashes and checks the compact fixture. Python
assertions are required: the script refuses `-O`.

This is a finite field-side trace and prime-square cross-check of **one**
selected row. It does not identify all Artin/Hecke factors globally, verify
the ramified-prime factors, or
validate the approximate-functional-equation moment bounds. It is external
arithmetic evidence and does not discharge the Lean hypothesis (H).
