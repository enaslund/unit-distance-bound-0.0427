# External proof of the remaining zeta inequality

The selected Lean theorem leaves its fixed-field zeta inequality as a
hypothesis. Outside Lean, the [manuscript](../../../publication/unit-distance-1.0418235/README.md) supplies a computer-assisted
argument for that same inequality. The missing Lean proof is distinct from
the existence and review status of this conventional argument.

This note records a September 21 examination of that distinction. It does
not replace the manuscript's analytic proof or its coefficient algorithms,
and it does not claim a new complete replay of their finite computations.

## Matching the mathematical expression

Write `M` for the manuscript's degree-524288 field; it is the field called
`CanonicalRetained.Carrier` in the independent Challenge. Its seven genus
radicands, seventeen catalog entries and twelve retained word masks match
the manuscript's list `B` in `sections/retained-field.tex`. The smaller field
`N`, of degree 16384, is a subfield used to make the analytic computation
tractable; it is not substituted for `M` in the theorem's hypothesis.

At `sigma = 12001/12000`, put

```text
Y = log(zeta_N with the S' Euler factors removed at sigma)/16384,
S' = {2, 3, 5, 7, 11, 13, 17}.
```

The manuscript's complete Hecke-factor calculation bounds `Y`. Restoring
the actual exceptional Euler factors for `M` contributes `B_D`. The two
disjoint finite prime corrections give savings `S4` and `Scen`. Their local
conditions are already detected in `M = G/D3G`, rather than only later
tower fields. Primewise comparison therefore gives

```text
log(zeta_M(sigma))/524288 <= Y + B_D - S4 - Scen.
```

The absolutely convergent logarithmic derivative at two satisfies

```text
-(zeta'_M/zeta_M)(2)/524288
  = sum_p log(p)/(e_M(p)*(p^(2*f_M(p)) - 1)) <= R.
```

Here `R` uses the local floors through 10000 and the proved integer-sum
tail bound in `sections/analytic.tex`, equations `an:R` and `an:slope`.
The zeta values on this real half-plane are positive and real. Consequently
the exact left-hand side `H` in `SolutionZeta.lean` is bounded by

```text
H <= Y + B_D - S4 - Scen
       + (1/12000)*((ell - gamma - log(4*pi))/4 + R).
```

This is a direct finite-field comparison. The eventual tower-residue
conclusion by itself would not prove the displayed fixed-field hypothesis.

## Numerical bound and evidence

The five conservative rational allowances printed in
`sections/analytic.tex:733-895` give

```text
  0.000445355407103547
+ 0.041727023150898786
- 0.00003724741189544274807446
- 0.00004201663320373563276702
+ 0.00006870442657779491222606
= 0.04216181893948094953138458
< 0.042165819.
```

The gap to the currently selected Lean threshold is exactly
`0.00000400006051905046861542`. This is slack in an upper-bound certificate,
not a measurement of the true value of `H` or an improvement in the exponent.

The [September 19 analytic review](../../reviews/adversarial-20260919/analytic.md)
records a fresh evaluation of the analytic factors, actual-field checks,
and an independent derivation of this fixed-field comparison. Its companion
reviews record full regeneration of all 126 stored sector moment tables,
the directly generated remaining sector, and the full prime census through
`10^12` with 2,220,060 complement primes. Maximal-order checks and independent
coefficient comparisons have their specific scopes in those records.

On September 21 we freshly reran the independent finite-prime and outward
summation program against the preserved full census. The
[result](finite-ceiling.json) exactly reproduces the earlier receipt and
gives the upper enclosure `0.042161818939480948744852245316750337...`.
This rerun uses the manuscript's factor-sum allowances; it does not freshly
prove those allowances or regenerate the census. The
[integrity record](source-and-recheck.json) also checks all eleven reviewed
manuscript/bibliography files and all 24 preserved analytic-evidence artifacts.
No differences were found.

A separate review with fresh context during this session checked the literal
fixed-field implication without relying on earlier review verdicts. It
rechecked all seventeen catalog norm identities, the displayed form masks,
the ranks seven and twelve and their containment, and the local-index and
logarithmic-derivative bridge. It found no mismatch in field, normalization
or derivative sign. Its conclusion depends on the manuscript's numerical
enclosures; it did not repeat their full computation.

## Trust and remaining formal work

This is a conventional computer-assisted proof argument: it depends on the
mathematical identification of actual fields and Hecke characters, the
proved analytic tails, exact finite algorithms, and their software execution.
The interval calculations use rigorous ball arithmetic as described by
[FLINT](https://flintlib.org/doc/arb.html). The meaning of the successful
maximal-order checks is documented by
[PARI's nfcertify reference](https://pari.math.u-bordeaux.fr/dochtml/html/General_number_fields.html#nfcertify).
Neither software documentation nor a hash comparison proves the repository's
mathematical identifications or the correctness of its entire implementation.

The earlier reviews report no remaining demonstrated defect in this
argument, with their coverage limits stated. They were agent reviews;
independent human review and a Lean proof of the full numerical inequality
remain separate work. The conditional submission does not incorporate this
external computation as a proved Lean lemma or a custom axiom. Frozen source
and review packages are unchanged.
