# A tower over Q(√241): exponent 1.04273 (research result, reviewed)

This directory records a new construction found on 2026-09-29. It builds the
manuscript's pro-2 tower over the real quadratic base B = Q(√241) instead of
over Q. The finite computations give u(n) ≥ n^{1.04273} for arbitrarily
large n, against 1.0418235 in the [manuscript](../0.0418235/README.md).
The mathematics transfers the manuscript's proofs to the base B, as described
in [research/construction.md](research/construction.md) §6. Three independent
fresh-context referee reviews (tower, analytic ceiling, geometric transfer)
found no mathematical error; their findings and the fixes are in
[research/review-20260929.md](research/review-20260929.md). **It is not yet a
self-contained manuscript.** Lean proves the exponent 1.0427 for this tower,
conditional on one explicit inequality H for the degree-512 genus field; the
formalization's account is `docs/sqrt241/SUBMISSION.md` in its Lean project.

## Idea in one paragraph

The Golod–Shafarevich criterion P(t) = 1 − dt + Σ(local costs) < 0 pays its
constant term once per tower. Over a totally real base in which every design
prime splits, generators and local blocks are replicated while the constant
is not, so the budget for local cuts grows. Q(√241) is the smallest real
quadratic field in which 2, 3 and 5 all split. Over it, the design uses only
2, 3 and 5, doubled, plus C₄ caps at the primes above 29 and at the inert
prime 7. It needs no ramification at 7, 11 and 13. The root discriminant
falls from 583 to √241·2^{9/4}·√15 ≈ 286. That outweighs the loss of the
selected primes 7–31 and the larger analytic slack.

## Contents

| Path | Contents |
| --- | --- |
| [research/construction.md](research/construction.md) | Statement, tower over B, analytic ceiling, geometric margin, and the list of transfer assumptions |
| [research/review-20260929.md](research/review-20260929.md) | Independent review record and resulting fixes |
| [research/design-search.md](research/design-search.md) | Calibrated design model; negative results (split-real places, other bases, variations over Q) |
| [research/design-model/](research/design-model/) | Model and optimizer code |
| [certificates/](certificates/) | Finite computations and the replay driver `reproduce241.py` |

## Key numbers

| Quantity | Value |
| --- | --- |
| rd(K) = rd(F) | √241·2^{9/4}·√15 ≈ 286.0 |
| Golod–Shafarevich | P_B(34/117) = −187433948535241/88772225460489675 |
| retained quotient | order 2⁴⁹, L₂=15, L₃=26; class of c₁ of size 2¹⁵, θ ≥ 65535/131072 |
| analytic ceiling | C = 0.04871285 (σ=301/300, from 255 rigorously evaluated quadratic Hecke L-functions of B) |
| certified margin | ≥ 0.000176 at δ = 0.04273 (≥ 0.000906 at δ = 0.0427) |

## Reproduce

```sh
cd certificates
python3 reproduce241.py        # needs PARI/GP and ../requirements.txt (or PYLIB)
```

The replay unpacks the manuscript's supplementary archive with the
manuscript's own hash-checked routine. It reuses the certified profile,
shell-window and degree-two AFE modules unchanged.

The individual steps, from `certificates/` (Python ≥3.11, mpmath 1.3.0,
python-flint 0.9.0, PARI/GP and a C compiler; set PYLIB if the Python packages
are not installed):

```sh
gp -q < kummer241.gp          # Kummer basis and local vectors
gp -q < cup241.gp             # cup-product invariants (rank 7)
python3 lie241.py; python3 lie241c.py   # layers L2, L3, retention, ad(c1)
python3 gs241.py              # P_B(34/117) < 0
python3 lfun241.py            # 255 L-function data rows (lrows241.json)
gp -q < lcheck.gp             # conductor/gamma/coefficient checks vs PARI
python3 afe241.py 301/300     # rigorous (1/512) log zeta_{E_B}
python3 ceiling241.py afe241_301_300.json   # C = 0.04871285
python3 geom241.py 0.04273 0.04871285 shells241_0.04273.json
gcc -O2 -fopenmp -o census241 census241.c -lm && ./census241 1e9 8   # census statistics
```
