# Source-only feasibility: PARI maximal-order replay for all 32 H6 quadratic rows

No new all32 checker or numerical run is included in this note. It records
the feasibility of extending the completed mask-1586, twist-`+1` check.

## Frozen row inventory and workload

The pinned H6 arithmetic table
`publication/nonabelian-dyadic-lower-bound/research/h6-low-degree-arithmetic.json`
(SHA-256
`b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771`)
contains 32 quadratic rows for mask 1586. Their twist parameters are

`-130,-110,-65,-55,-30,-26,-22,-15,-13,-11,-10,-6,-5,-3,-2,-1,`
`1,2,3,5,6,10,11,13,15,22,26,30,55,65,110,130`.

The exact sizes from that table are:

| Row cutoff `N` | Rows | conductor in those rows |
|---:|---:|---:|
| 981 | 8 | 15,015 |
| 3,922 | 8 | 240,240 |
| 7,843 | 16 | 960,960 |

Thus the maximum field prime bound is 7,843, the sum of row cutoffs is
164,712, and a simple per-row implementation needs 21,520 quartic
`idealprimedec` calls across rational primes. The base quadratic field can be
decomposed once through 7,843 (991 primes) and reused. If decompositions are
computed separately for each row's quartic and base field, there are at most
43,040 field/prime decomposition calls. These counts include only primes
`p<=N_row`, as required for `a_1,...,a_{N_row}`.

Each row's relative quartic field is represented by

`K_D = Q[x]/(x^4 - 34 D x^2 + 429 D^2)`,

with base `B=Q[x]/(x^2+35)`. This follows by setting
`beta^2=-35`, `alpha=17+2 beta`, and `u^2=D alpha`; eliminating `beta` gives
the displayed polynomial. The row twist is `D`; it is squarefree for the
listed representatives. A batch checker can form the local quotient
`D_B(T)/D_{K_D}(T)` from PARI maximal-order e/f profiles, multiply local
series multiplicatively, and compare all coefficients with the pinned row
recurrence. It should call `nfcertify` for every `K_D` and once for `B`, and
check each row's seven bad polynomials by `D_{K_D}=E_{D,p} D_B`.

The largest arrays have 7,844 Python integers for one row; all row vectors
total 164,712 coefficients. Profiles contain at most 21,520 quartic
prime-decomposition records plus 991 shared base records. Expected memory is
well under 1 GiB; a 400 MB PARI stack is ample based on the successful single
row job. Estimated runtime is seconds to a few minutes, with 900 seconds a
generous guarded timeout. These are source-size/resource estimates, not
measurements. The finite workload is comfortably below the configured 4 GiB
and 150% CPU policy, subject to actual guard admission.

## Coverage and analytic boundary

This would extend only finite arithmetic coverage from one to all 32 row
cutoffs. It would use the actual twisted polynomial per row and exact bad
Euler tables. The existing H6 inventory receipt already records PARI
`lfun`-based coefficient checks for all 32 rows through 10,000, but it does
not use this direct maximal-order prime-decomposition route. The new route
would therefore add method diversity and rowwise local-order evidence,
although its twist formula and row table are inherited from the same pinned
arithmetic inventory.

No finite coefficient agreement, even for all 32 prefixes, proves the
untruncated all-prime equality or supplies the AFE's conductor, gamma factor,
root number, functional equation, contour-growth premises, or tail bound.
The generic splitting derivation and the exact seven exceptions remain
conditional on the stated `K_D/B` field identification. Each row receipt
should keep these limits explicit.

## Portable extracted-package replay

The existing one-row checker derives its repository root relative to its own
path, then reads pinned sources in the sibling `publication/...` tree and
writes beside itself. The selected conditional package curates a manuscript
subset, **not** this full research tree, so the current checker cannot
regenerate its reference vector from that extracted package alone. Its
source, exact finite result, and input hashes remain inspectable there;
rerunning it requires the pinned research checkout. A future portable replay
would have to ship its needed research-source closure or a separately reviewed
pure-Python reference recurrence. The generated GP source and executable
should be hashed again in any replay; an old receipt hash is not proof the
replay files match.
The only external import is the python-flint package transitively required
when loading the inherited recurrence module; it performs no arithmetic in
the replay. For portability, either provide a path to the pinned package
tree via `PYTHONPATH` and verify its installation-tree hash, or put the
reference coefficient recurrence in a pure-Python adapter which avoids
loading its unrelated AFE imports. The latter is a source change and should be
independently reviewed before presenting it as the same checker.
