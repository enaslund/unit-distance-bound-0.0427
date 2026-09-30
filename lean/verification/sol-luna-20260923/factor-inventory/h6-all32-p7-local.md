# H6 mask 1586: the (p=7) local denominator for all twists

For (B=\mathbb Q(\sqrt{-35})), (\eta=17+2\sqrt{-35}), and
\(K_D=B(\sqrt{D\eta})\), the local relative zeta denominator at 7 is

\[
E_{D,7}(T)=\begin{cases}1+T,& (D/7)=1,\\1-T,& (D/7)=-1.\end{cases}
\]

Equivalently, (E_{D,7}(T)=1+(D/7)T). Here (D) ranges over the 32
mask-1586 twists
\(\pm1,\pm2,\pm3,\pm5,\pm6,\pm10,\pm11,\pm13,\pm15,\pm22,\pm26,\pm30,\pm55,\pm65,\pm110,\pm130\);
none is divisible by 7.

## Local residue calculation

The squarefree radicand (-35\equiv1\pmod4) gives
\(\mathcal O_B=\mathbb Z[\omega]\), with
\(\omega=(1+\sqrt{-35})/2\), minimal polynomial
\(X^2-X+9\), and discriminant (-35). Modulo 7 this polynomial is
\(X^2-X+2=(X-4)^2). Thus 7 is ramified in (B/\mathbb Q), with one
prime (\mathfrak p\) over 7, residue field \(\mathbb F_7\), and
\(\sqrt{-35}=2\omega-1\equiv0\pmod{\mathfrak p}\). Hence
\(\eta\equiv17\equiv3\pmod{\mathfrak p}\), and
\(D\eta\equiv3D\pmod{\mathfrak p}\). This is a unit because 7 does not
divide (D).

The relative quadratic algebra is obtained by adjoining a root of
\(X^2-D\eta\). Its discriminant (4D\eta) is a local unit at
\(\mathfrak p\), since the residue characteristic is odd and (D\eta)
is a unit. The algebra is therefore finite etale there: the relative
extension is either split or unramified inert. More explicitly, if (3D)
is a square in \(\mathbb F_7\), its nonzero square root lifts by Hensel's
lemma, so the local algebra splits into two copies of (B_{\mathfrak p}).
If (3D) is a nonsquare, the reduced polynomial is irreducible and
separable; adjoining its root gives the unramified quadratic extension,
with residue degree 2 over \(\mathbb F_7\). This applies to the global
quadratic field (K_D/B); it is nontrivial since
\(N_{B/\mathbb Q}(D\eta)=429D^2\), and a square in (B) would force
429 to be a rational square.

For a number field (L), put
\(D_{L,7}(T)=\prod_{\mathfrak q\mid7}(1-T^{f(\mathfrak q/7)})\).
The base field has one prime of residue degree 1, so
\(D_{B,7}(T)=1-T\). In the split relative case, (K_D) has two primes
over \(\mathfrak p\), each still of absolute residue degree 1; hence
\(D_{K_D,7}(T)=(1-T)^2\) and (E_{D,7}=D_{K_D,7}/D_{B,7}=1-T\).
In the inert case there is one prime with absolute residue degree 2; hence
\(D_{K_D,7}(T)=1-T^2\) and (E_{D,7}=1+T\).

The nonzero squares modulo 7 are \(1,2,4\), and 3 is a nonsquare.
Therefore \((3D/7)=-(D/7)\). The split case occurs exactly when
\((D/7)=-1\), giving (1-T); the inert case occurs exactly when
\((D/7)=1\), giving (1+T).

## Exact comparison with the pinned table

I read mask 1586 from
`publication/nonabelian-dyadic-lower-bound/research/h6-low-degree-arithmetic.json`
(SHA-256
`b0335a1a87f8c3261d4be0bff2108a520964651c8884207f54194923378b7771`).
Its pinned generator source is
`publication/six-dimensional-lower-bound/research/next-dyadic-h5-single.py`
(SHA-256
`f9a97f5c41485914e9700a5efcebb9df0ffdbc834a56a666b994d397ab3a3ba6`).
For every row, exact integer reduction modulo 7 determined the Legendre sign
and I compared the predicted coefficient vector with the table's full
`bad_euler_denominators["7"]` complex-pair array. All 32 comparisons pass;
the real table entries agree as well.

The read-only check was the exact finite calculation

```python
squares = {1, 2, 4}
for row in mask1586_rows:
    d = row["twist"]
    chi_d = 1 if d % 7 in squares else -1
    assert d % 7 != 0
    assert row["bad_euler_denominators"]["7"] == [
        [1, 0], [chi_d, 0], [0, 0], [0, 0], [0, 0]
    ]
```

Since (E_{D,7}=1+(D/7)T), the table's linear coefficient is exactly
`chi_d`.

| Predicted denominator | Twists (D) | Count |
|---|---|---:|
| (1+T) | (1,2,-3,-5,-6,-10,11,-13,15,22,-26,30,-55,65,-110,130) | 16 |
| (1-T) | (-1,-2,3,5,6,10,-11,13,-15,-22,26,-30,55,-65,110,-130) | 16 |

This is an exact local-field derivation plus a read-only comparison against
the pinned table; no Lean, PARI, or new numerical replay was run. The H6
arithmetic receipt separately records its independent PARI local-factor
checks. The argument here assumes the standard local facts stated above
(Hensel lifting and the unramified criterion for an irreducible separable
reduction); it does not prove global Artin-row identification or any analytic
claim.
