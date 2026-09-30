# H6 mask 1586: symbolic bad-prime factors at 3, 11, and 13

Let (B=\mathbb Q(\sqrt{-35})), (\eta=17+2\sqrt{-35}), and
\(K_D=B(\sqrt{D\eta})\), for the 32 squarefree twists in mask 1586.
For each (p\in\{3,11,13\}), the base prime splits in (B), and the
relative local denominator has exactly one surviving unramified base-prime
contribution. Write (E_{D,p}(T)=D_{K_D,p}(T)/D_{B,p}(T)), where
\(D_{L,p}(T)=\prod_{\mathfrak q\mid p}(1-T^{f(\mathfrak q/p)})\).

The explicit unit whose Legendre sign selects split/inert behavior is

\[
u_{p,D}=\begin{cases}
34D\pmod p,&p\nmid D,\\[2pt]
\displaystyle \frac Dp\,\frac{429/p}{34}\pmod p,&p\mid D.
\end{cases}
\qquad
E_{D,p}(T)=1-\left(\frac{u_{p,D}}p\right)T.
\]

In the second branch (D/p) is the signed integer quotient and (429/p)
is an integer. The fractions in the residue expression mean multiplication
by the inverse of (34\pmod p), not rational division before reduction.

## Symbolic local derivation

The roots of (X^2+35) modulo (p) exist and are nonzero:

| (p) | (-35\pmod p) | roots (r\pmod p) | (34\pmod p) | ((429/p)34^{-1}\pmod p) |
|---:|---:|---:|---:|---:|
| 3 | 1 | (\pm1) | 1 | 2 |
| 11 | 9 | (\pm3) | 1 | 6 |
| 13 | 4 | (\pm2) | 8 | 9 |

Since (p\nmid35), each root lifts by Hensel to (\mathbb Q_p), so
\(p\mathcal O_B=\mathfrak p_0\mathfrak p_1\) with both residue fields
\(\mathbb F_p\). Choose (r\equiv-17/2\pmod p) for \(\mathfrak p_0\).
Then \(\eta=17+2\sqrt{-35}\) has residue zero there, while its conjugate
has residue \(17-2r\equiv34\pmod p\) and is a unit. The exact norm is
\(N_{B/\mathbb Q}(\eta)=429=3\cdot11\cdot13\); consequently
\(v_{\mathfrak p_0}(\eta)=1\) and
\(\overline\eta=429/\eta\) has residue 34 at \(\mathfrak p_0\).
At the conjugate prime \(\mathfrak p_1\), \(\eta\) itself has residue
34 and is a unit.

For an odd-residue-characteristic local field, adjoining a square root of a
unit gives a split algebra if the residue is square and the unramified
quadratic extension if it is nonsquare: the first case follows by Hensel
lifting a simple root, and in the second (X^2-u) has irreducible separable
reduction. A radicand of odd valuation instead gives a ramified quadratic
extension (valuation parity is invariant under multiplication by squares).
Every relative ramified prime here has residue degree one, so its
\((1-T)\) denominator cancels against that of the corresponding base prime.
The split base prime has (D_{B,p}(T)=(1-T)^2); after that cancellation,
only the other, unramified base prime contributes to (E_{D,p}).

* If (p\nmid D), then (D\eta) has valuation one at \(\mathfrak p_0\),
  so that relative prime is ramified. At \(\mathfrak p_1\), its unit residue
  is (34D); this is the unique unramified base prime, with split/inert sign
  \((34D/p)\).
* If (p\mid D), the twists are squarefree, so (v_p(D)=1). At
  \(\mathfrak p_1\), (D\eta) has valuation one and the relative prime is
  ramified. At \(\mathfrak p_0\), it has valuation two; divide by the square
  (p^2). Using (\eta\overline\eta=429) and
  \(\overline\eta\equiv34\pmod{\mathfrak p_0}\), the resulting unit
  residue is
  \((D/p)(429/p)34^{-1}\pmod p\). This is the unique unramified base
  prime. Its unit is square exactly when the relative quadratic algebra
  splits.

At the unramified base prime, a square unit gives two primes of relative
residue degree one, changing the denominator from (1-T) to
\((1-T)^2) and contributing (1-T). A nonsquare unit gives one prime of
relative residue degree two, contributing
\((1-T^2)/(1-T)=1+T). This proves the displayed formula for both branches.

For compact row checking, put
\(c_p=34\pmod p\) when (p\nmid D), and
\(r_p=(429/p)34^{-1}\pmod p\) when (p\mid D). The constants are

| (p) | (c_p) | (r_p) |
|---:|---:|---:|
| 3 | 1 | 2 |
| 11 | 1 | 6 |
| 13 | 8 | 9 |

Thus the branch-specific Legendre signs are \((c_pD/p)\) for (p\nmid D)
and \((r_p(D/p)/p)\) for (p\mid D). In all cases the residue argument
uses a unit, including the valuation-two branch.

## Exact comparison with the pinned table

The source table is the mask-1586 sector in
`publication/nonabelian-dyadic-lower-bound/research/h6-low-degree-arithmetic.json`
(SHA-256
`b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771`).
The pinned row generator is
`publication/six-dimensional-lower-bound/research/next-dyadic-h5-single.py`
(SHA-256
`f9a97f5c41485914e9700a5efcebb9df0ffdbc834a56a666b994d397ab3a3ba6`).
The following exact modular calculation checked the entire complex-pair
`bad_euler_denominators[p]` vector for all 32 rows (and equivalently its real
coefficient vector):

```python
for p in (3, 11, 13):
    c = 34 % p
    r = ((429 // p) * pow(c, -1, p)) % p
    for row in mask1586_rows:
        d = row["twist"]
        if d % p:
            u = c * d % p
        else:
            u = r * (d // p) % p
        symbol = 1 if pow(u, (p - 1) // 2, p) == 1 else -1
        expected = [[1, 0], [-symbol, 0], [0, 0], [0, 0], [0, 0]]
        assert row["bad_euler_denominators"][str(p)] == expected
```

Each prime has 16 rows with denominator (1+T) and 16 with (1-T).
This check uses exact integers/modular exponentiation only. The symbolic
derivation explains the local factors; the pinned table comparison is a
separate finite check. No Lean, PARI, or numerical replay was run. The
argument uses the standard local quadratic-extension criteria just stated;
it makes no claim about the global Artin row identity or analytic factors.
