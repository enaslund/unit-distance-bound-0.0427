# Why 41: cap-candidate search for the 241 tower

Date: 2026-10-03. The Golod-Shafarevich budget of the 241 tower admits no
additional C4 cap (3 caps: P_B=-0.00211; 4 caps: min P_B=+0.00288 over
t in (0,1)), so any new cap must displace an existing one. This note records
the search that selects the swap (drop inert 7, cap one prime above 41).

## Split primes and single-cap profits

A C4 cap at an unramified B-prime of norm N with relative (e,f)=(1,4) costs
c4(t)=t^4/((1+t)(1+t^2)) in P_B regardless of N. Its geometric value depends
on N and on how many of the B-primes above the rational prime are capped:

* both B-primes above a split rational p capped: absolute (e,f)=(1,4),
  contribution logF(Q=p^4,k)/(1*4);
* one of two B-primes above a split p capped: half the F-primes above p,
  effective absolute (e,f)=(2,4), contribution logF/(2*4);
* the inert prime (p) of norm p^2 capped: absolute (e,f)=(1,8),
  contribution logF(Q=p^8)/(1*8).

Rational primes and their splitting in B=Q(sqrt 241) ((p/241) by reciprocity,
241 = 1 mod 4):

| p       | splitting | cheapest useful cap                    | hard profit at delta=0.0429 |
|---------|-----------|----------------------------------------|-----------------------------|
| 2,3,5   | split     | ramified (design primes, kept)         | (ramified blocks)           |
| 7       | inert     | capped in 241 design: (1,8), k=1       | 0.0035                      |
| 11-23   | inert     | (1,8): negative at k=1                 | <0 (not useful)             |
| 29      | split     | capped (both): (1,4), k=1              | 0.0294 (kept)               |
| 31,37   | inert     | (1,8): negative                        | <0                          |
| 41      | split     | single: effective (2,4), k=1           | 0.0073                      |
| 47      | split     | single: effective (2,4), k=1           | 0.0041                      |
| 53      | split     | single: effective (2,4), k=1           | 0.0015                      |
| 59+     | split     | single: nonpositive                    | <=0                         |

41 is the smallest split prime after 29, hence the most profitable single
cap. Both its B-primes have Frobenius squares outside R2 and avoid c1
(`check41.py`), so either supports a C4 cap with relative f=4 and K/F
splitting. The design caps P41[1] and leaves P41[2] to the census (f_min=4).

## Considered alternatives (all worse)

* Keep 7 and add a 41 single cap (4 caps total): P_B>0 everywhere; fails.
* Cap both 41 primes (2 caps) and drop 7 (net +1 cap, 4 total): fails.
* Cap both 41 primes and drop one 29 prime (net 0 caps: 29-single + 41-full):
  profit 0.0144+0.0145=0.0289 < 0.0294+0.0073=0.0367 of the chosen design.
* 47-single instead of 41-single: profit 0.0041 < 0.0073.
* Change a ramified C2 block (3/5) to C4 to fund more caps: saves ~0.053-0.106
  of GS budget but loses ~0.21 of finite profit per rational prime; the freed
  budget funds only low-profit large-prime singles. Net negative in the model.
* f=2 (order-2) caps at large split primes: better profit/cost ratio per cap
  but absolute cost ~0.065 each, far beyond the 0.0021 slack; funding one
  requires dropping the entire profitable cap set. Net negative.

## Non-cap refinements tried (negligible)

* Fresh archimedean (degree-3, beta=2.2) at the new delta: included in the
  witness (this is headroom accounting, not extra gain beyond the swap).
* Degree-5 archimedean: +4.1e-7 in J_D (~9e-9 exponent). Skipped.
* 8-10 finite shells for 2,3,5: +5e-8 margin (~2e-9 exponent). Skipped.
* Analytic abscissa scan (12 values around 301/300): best 289/288 improves C
  by 1.75e-6 (~7e-8 exponent). Kept 301/300 for input reuse.
* Census beyond 10^6: tail below ~5e-7 in C (~2e-8 exponent). Kept 10^6.
* Other beta values (2.12-2.30): all below beta=2.2 in J0.
