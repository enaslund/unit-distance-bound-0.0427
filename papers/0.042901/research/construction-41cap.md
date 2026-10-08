# The 41-cap variation: exponent 1.042901

Date: 2026-10-03. Status: **research result; finite replay passes**
(`certificates/reproduce41.py`). Not yet independently reviewed or
Lean-formalized. It varies the [Q(sqrt 241) construction](../../0.04273/research/construction.md)
(itself a research result at 1.04273), reusing that tower, genus field, and
analytic value with one swapped cap. Section 5 lists exactly what the swap
requires; everything else is inherited by hash-checked reference.

## 1. Result claimed

With the base field B=Q(sqrt 241) and the cap set below (two C4 caps above
29, one C4 cap above 41, no cap at 7), the construction gives finite planar
sets U_j with |U_j|->oo and u(U_j)/|U_j|^{1+delta}->oo for

    delta = 0.042901   (exponent 1.042901; the 241 design has 1.04273).

The certified geometric lower margin at delta=0.042901, after the
concentration allowance, is >= 5.77e-6, using the rigorous analytic ceiling
C = 0.04871285 of section 4 (same threshold as the 241 design; the recomputed
upper endpoint is bit-identical). At delta=0.04290 the margin is >= 2.97e-5.

## 2. Idea: a GS-neutral cap swap toward a smaller split norm

The 241 design caps the inert prime (7) of norm 49 (one C4 cap, absolute
(e,f)=(1,8), finite profit ~0.0035). The rational prime 41 splits in B
((41/241)=1; the next split prime after 29), with both B-primes having
Frobenius squares outside R2 (section 3). Capping one of the two B-primes
above 41 costs one C4 cap -- the same Golod-Shafarevich cost c4 as the 7-cap
-- while its absolute type (e,f)=(1,4) on half the F-primes above 41
(effective (2,4)) gives finite profit ~0.0073, more than twice the 7-cap.
Dropping the 7-cap and capping one 41-prime keeps the cap count at 3, so the
Golod-Shafarevich polynomial P_B(t)=1-8t+2c1+4c2+2d_D-s_D+3c4 and its
negative value P_B(34/117) are unchanged, and the retained Lie layers
(L2=15, L3=26, |G/D4|=2^49, class(c1)=2^15) are unchanged because
fourth-power caps have no quadratic or cubic initials.

The analytic ceiling is exactly unchanged: the 7-term moves from the selected
excess to the census (same f=4 formula), and one 41-term moves from the
census to the selected excess (same formula), so Y_* and R are identical.
The geometric margin gains the full finite-profit difference (~0.0038),
which at slope ~-24 buys ~0.00017 of exponent. Fresh archimedean and shell
profiles at the new delta (section 5 of the 241 construction, re-optimized)
supply the rest of the headroom accounting; the swap itself is the gain.

## 3. Tower compatibility of the new cap

41 splits in B (idealprimedec gives two primes; `kummer41.gp`). Their
Frobenius vectors (Hilbert symbols against the 241 Kummer basis) are

    P41[1]: [0,0,1,1,1,0,0,0],   P41[2]: [0,0,1,1,0,1,0,0],

agreeing between PARI (`kummer41.gp`) and the Legendre-symbol computation
(`check41.py`). The capped prime is P41[1]. Both vectors are nonzero (degree
one) and satisfy:

* S(v) is independent of R2 mod the quadratic relations (`check41.py`, using
  the R2 span of `lie241.py`, which is unchanged). Hence each Frobenius has
  order divisible by 4 in the D3 quotient G_B/D3G_B. The imposed relation
  Frob^4=1 lies in D4 (in characteristic 2, (g-1)^4=g^4-1), so it does not
  change G_B/D3: in every layer K retaining D3 (all our K contain the fixed
  field of D4G_B, as in 241 construction section 3.6), the capped Frobenius
  has order exactly 4. This gives K/B relative f=4 at the capped prime.
* v != c1 = [1,0,1,1,1,0,1,0], so c1 lies outside each cyclic decomposition
  span {0,v}. If c1 = Frob^k, then mod Frattini c1 = 0 (k even) or v
  (k odd), both excluded; hence <c1> cap <Frob> = {1}. All decomposition
  groups above the capped prime are conjugate in Gal(K/B) (K/B Galois) with
  the same vector v (V is abelian) and conjugate squares still in the normal
  Frattini subgroup, so the intersection is trivial above every such prime:
  every F-prime above the capped B-prime splits in K/F (same shape as 241
  construction section 3.6). With K/B unramified (e=1), the used F-primes
  have true absolute type (e,f)=(1,4).

The uncapped B-prime above 41 and the now-uncapped inert prime 7 have
Frobenius squares outside R2 (41: `check41.py`; 7: 241 `lie241.py` output
"cap f7 S(frob) independent: 1"), so the census correctly uses f_min=4 for
both (section 4).

B is totally real, so c1 (complex conjugation at v1) restricts to the
identity on B; hence B is contained in F=K^{<c1>} and [F:B]=d/2. The d/8
F-primes above the capped B-prime ([F:B]/(1*4) with relative
(e,f)=(1,4); d=[F:Q] is a large power of 2 since [K:B]=d runs over
2-powers retaining D4, so 8 divides d) have residue cardinality 41^4 and
carry the windows of section 5. The F-primes above the uncapped B-prime
have residue degree only lower-bounded (f>=4 from S(v) outside R2, not
uniformly 4), so they carry no windows and are left to the census. The
used primes contribute logF/8 to the per-degree finite sum with H-term
k*log(41)/2; the margin encodes this as effective absolute (e,f)=(2,4)
(contribution logF/(e*f), H-term k*log(p)/e), a counting device for using
half the primes above 41 -- the true absolute type on used primes is
(e,f)=(1,4) with e=1 unramified, and the windows use Q=41^4.

## 4. Analytic ceiling (recomputed, identical value)

Y_E = (1/512) log zeta_{E_B}(301/300) is inherited from the 241 certificate
(`afe241_301_300.json`, hash-checked in `ceiling41.py`): E_B depends only on
the Kummer group V, not on the caps. With the swapped selected set:

* selected excess: dyadic x2, 29 x2 (as in 241), plus ONE B-prime above 41
  (a(41^2)/(4)-a(41^4)/(8)); the 7-term is removed;
* census (N<=10^6): the inert prime 7 is now included (f_min=4); for p=41
  the capped B-prime is excluded and the uncapped one included (f_min=4);
* R_sel: dyadic/3/5/29 terms as in 241, plus one 41-term
  log(41)/(2*(41^8-1)); the 7-term is removed.

Because the moved terms use the same f=4 formulas on both sides, the totals
are bit-identical to the 241 values: Y_* and R agree, and
C_upper = 0.04871284289033... < 0.04871285 as before (`ceiling41.py` output).
B_sel(1) moves by +2.3e-8 (41 vs 7 floor terms), negligible and reported only.

## 5. Geometric margin (fresh profiles at the new delta)

Propositions `geo:transfer`/`fw:transfer` apply as in the 241 construction
section 5 (quadratic K/F unramified at finite places, K totally imaginary,
F with a real place, uniform types per used prime, root discriminant
lambda = sqrt(241)*2^{9/4}*sqrt(15)). The witness
(`certificates/witness41_0.042901.json`) uses:

* delta = 0.042901, C = 0.04871285, theta_min = 65535/131072;
* a fresh degree-3 Bernstein-Student complex-pair profile (beta=2.2,
  s=1.147191100000, a=0.0000170095011570) optimizing the renormalized
  functional at the new delta (J_D = 1.3514546797...);
* six-shell finite windows re-optimized at the new delta for 2,3,5
  (ks 7,9,6) and truncated windows for 29 (3 shells, k=1) and 41
  (3 shells, k=1, Q=41^4, effective (e,f)=(2,4)).

`geom41.py` reuses the 241 `mass_certificate`, `overlap_certificate`,
`tube_certificate`, and `local_window` routines unchanged (via `geom241.py`
with the EF table patched to {2:(8,4),3:(2,2),5:(2,2),29:(1,4),41:(2,4)}).
Results:

| delta   | J_D     | mu    | margin after concentration |
|---------|---------|-------|----------------------------|
| 0.042901| 1.35145 | 17.09 | +5.779e-6 (claimed)        |
| 0.042902| 1.35143 | 17.09 | -1.814e-5 (fails)          |

The Fourier checks (sigma_D>1, logK<2log2, mu>10) and the positive
theta-slope hold. The discovery optimizers (archimedean BFGS over Jacobi
coordinates, Nelder-Mead shell searches over k=0..39) are floating-point
search only; the certificate consumes only the exact saved witness.

## 6. What the swap assumes, beyond the 241 construction

1. The capped-41 quotient (same generator/relation counts as the 241
   quotient, one relation moved from 7 to a 41-prime) inherits the 241
   complete presentation, Fox-block costs, and infinitude value: the C4-cap
   cost c4 is prime-independent (both Frobenius vectors are nonzero, so
   degree one with g^4 in degree 4), and fourth powers lie in D4 so they do
   not enter L1/L2/L3 or G/D3.
2. K/F splitting above the capped 41-prime follows from the cyclic-span
   separation in section 3 (same shape as the 241 separation lemma).
3. The per-prime-of-B analytic transfer (241 construction section 4.1)
   applies with the swapped selected set; the census soundness needs R2
   complete (241 section 4.2, unchanged) and the f_min=4 facts of section 3.
4. The geometric propositions use only K/F and its local data (section 5).

## 7. Reproduction

From `certificates/` (Python >=3.11, mpmath 1.3.0, python-flint 0.9.0,
PARI/GP):

```sh
python3 reproduce41.py
```

This hash-checks the shared 241 inputs, replays PARI Kummer vectors for 41,
the cap-compatibility checks, the Lie/GS steps, the recomputed ceiling, and
the geometric margin, writing `replay41.json`. It replays in seconds because
the genus-field AFE value is inherited (not recomputed) and the census runs
only to 10^6.
