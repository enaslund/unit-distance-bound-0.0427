# H6 mask-1586 all-32 maximal-order quotient: guarded result

## Result

The [second guarded run](h6_all32_quartic_zeta_quotient.json) passed. The raw
JSON SHA-256 is
`7002e21b55dc09dd42a306ecc6a5742be5bbf88d0fd1059813cbb06fae044496`.
The [executed checker](h6_all32_quartic_zeta_quotient_attempt2.source) has
SHA-256
`cf9970fe1386f89c147c7212f2f51e8e6607f47547195535e4b2f1a787738dc7`.
The checked [working checker](h6_all32_quartic_zeta_quotient.py) had the
same digest at execution. The generated GP source digest is
`b78ae023b7b542a16cd230b6e56d3478c3d0e015f57714e3c8825d2b484231f0`.

For the 32 distinct pinned twists, the checker used quartic fields
`K_D = Q[x]/(x^4 - 34 D x^2 + 429 D^2)` and the shared quadratic base
`B = Q[x]/(x^2 + 35)`. PARI verified irreducibility and certified the
maximal orders, then `idealprimedec` supplied e/f data for the local quotient
`ζ_{K_D}/ζ_B`. It computed 21,520 quartic prime decompositions at the
row-specific cutoffs and 991 shared base-prime decompositions. Exact
multiplicative reconstruction matched all **164,712** pinned integer
coefficient positions, including complete vector SHA-256 matches for each
row. All **224** bad-prime denominator cross-products (seven per row, primes
2, 3, 5, 7, 11, 13, 17) passed. There were zero mismatches. The cutoffs were
981 for eight rows, 3,922 for eight, and 7,843 for sixteen.

The master guarded helper admitted the run with 16.1 GiB host available and
1.20 GiB cgroup headroom; the command exited zero. The checker reports 1.46
seconds for its numerical core. Peak RSS was not recorded. The result pins
PARI/GP 2.17.2, the GP executable digest, the Python-flint 0.9.0 tree digest,
all 12 inherited research input digests, and generated GP stdout digest.
Python-flint was an import-only dependency for the inherited recurrence.
The checker does not alter the inherited `h6-low-degree-arithmetic.json`.

The [first guarded attempt](h6_all32_quartic_zeta_quotient_attempt1.json)
failed at generated GP syntax before any coefficient comparison. Its raw
result SHA-256 is
`1ca153f12c6207742417377fc47cfc661bbae706f72271d062abf52039964270`;
its [source](h6_all32_quartic_zeta_quotient_attempt1.source) has SHA-256
`156376e831f7987e9233241a6e0c02e23bfde0acd33285479cecac65eb1165f3`.
The second revision fixed GP vector/function rendering; `py_compile` passed
before the guarded retry. The [source review](h6-all32-quartic-zeta-quotient-source-review.md)
was written before the completed replay and reviews the finite algorithm.

## Scope and remaining obligations

The result is a fresh finite check through the pinned cutoffs using explicit
maximal-order prime decompositions. It does not prove the all-prime quotient
identity, the match to the intended degree-16384 completed-field factor
inside the degree-524288 retained field,
conductor or gamma data, root number, functional equation, contour growth,
AFE tail, or the scalar inequality H. The [all-32 good-prime derivation](h6-all32-good-prime-derivation.md)
is paper-level, and the [relative Hecke corollary](h6-all32-relative-hecke-corollary.md)
invokes standard analytic theorems outside Lean. The historical all-32
`lfun`/`lfunan` record independently reaches coefficient prefix 10,000 but
lacks raw GP output and run-provenance pins; see the
[inherited audit](../numerical-audit/h6-all32-inherited-pari-audit.md).

This direct result is checkout-side post-seal evidence. Its checker and JSON
are outside the broad research-script selection of sealed candidate 17, so
an extracted candidate-17 package does not reproduce it. Candidate 17 itself
retains byte-identical selected proof inputs to verifier-passed archive 07,
but no current-policy full verifier run passed.
