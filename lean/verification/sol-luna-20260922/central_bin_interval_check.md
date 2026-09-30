# Independent full stored-census interval assembly

`central_bin_interval_check.py` independently combines the 13,825 nonempty
bins in the pinned full H7 census table through `10^12`. The table's SHA-256
is `43669734971ae82bdf2980bbacd869a65224fe3cececb121cf2fbc14936813f2`.
The program does not use the manuscript's census producer or replay code.
Two executions through the shared resource guard passed; the second wrote
`central_bin_interval_check.json` as a durable receipt.

The checker reconstructs all 21,299 allowed geometric bins, verifies the
stored nonempty bins' endpoints and exact integer partitions, and recombines
the header totals: 293,705,608 full-field hits, 291,485,548 completed-field
hits and 2,220,060 complement hits. It checks each stored floor reciprocal
sum against its bin's elementary bounds. All 2,307 complete nonempty prefix
bin rows below `10^7` equal the separately pinned prefix table entry for entry;
the separate `numerics_h7_prefix_check.py` regenerated that prefix from primes.
The terminal truncated prefix bin is omitted from this row identity check.

For each complement bin `l < p ≤ h`, with count `n` and integer reciprocal
sum `u=Σ floor(10^30/p)`, it applies the manuscript's mathematical enclosure

```text
h^(-1/12000) u/10^30
  ≤ Σ atanh(p^(-12001/12000))
  ≤ l^(-1/12000) (u+n)/10^30 · 1/(1-l^(-2)).
```

It obtains directed rational `log l`/`log h` bounds with 35 terms of the
`atanh` series and a geometric tail. Odd/even Taylor polynomials of degrees
nine/eight bound the exponentials, and each bin is rounded outward on a
`10^-37` grid. The resulting exact interval is

```text
0.0000420166332037356346271115723633453
  ≤ S_cen ≤
0.0000420166367036339729679676101666689.
```

This lies strictly inside the manuscript's printed interval
`(0.00004201663320373563276702,
0.00004201663670363397482805)`; both strict margins are about
`1.86×10^-21` and appear exactly in the JSON receipt.

The result audits the **stored full bin table**, its elementary arithmetic,
and its connection to the independently regenerated `10^7` prefix. It does
not regenerate the remaining primes to `10^12` or prove that the table's
quadratic predicates are the required splitting conditions. Those and the
analytic Hecke factor estimates remain external to Lean, so the fixed-field
zeta inequality remains unproved there.
