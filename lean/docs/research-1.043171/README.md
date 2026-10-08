# D4 refinements of the 41-cap tower: exponent 1.043171 (research result)

> **Manuscript.** The self-contained paper for this result is [main.pdf](main.pdf) (source [main.tex](main.tex),
> [sections/](sections/)), "An Exponent of 1.043 for the Unit Distance Problem". This README is the research
> record behind it. Reviews of the manuscript's revision of October 8, 2026 are in [reviews/](reviews/): a
> fresh-context readability review, which found no change to the mathematics, and an audit of the floating-point
> arithmetic of the L-value, kernel and receipt programs, which found no non-rigorous bound.

Date: 2026-10-05. Status: **research result; finite replays pass**
(`certificates/dihedral/reproduce_w3.py` for 1.043171 and 1.043152, `certificates/dihedral/reproduce_dihedral.py`
for 1.043124 and earlier, and for the intermediate results `certificates/reproduce_census.py` and
`certificates/reproduce_adaptive.py`). Ten independent reviews. Eight are listed here; the ninth (the assembly of
the 1.043152 certificate) is below, and the tenth (the fourth form and general shell weights) is in Section 11c:

* Lemma 1 and Propositions A and B (Sections 6-7): no error affecting
  validity.
* Lemma 2 and the census (Sections 4-5): no error affecting validity.
* The dihedral part (Sections 8-10): one material error. The 13 vector-0
  primes inert over Q had their E_W reduction counted twice, once in Y_W and
  once in the adaptive sum. It is fixed below (`inertv0.py`), which halves the
  margin but keeps the exponent.
* Proposition D, the refined TV step (Section 11): no error affecting
  validity.
* The assembly of the 1.043118 certificate (Sections 1 and 11: kernel check,
  census provenance with three bins recounted by `census_d3k.c`, ceiling with
  several prefixes, replay, margin): no error affecting the bound. Its minor
  points are fixed: stale figures, a dead branch, two unpinned files, files
  regenerated in place now asserted unchanged, and wording.
* Proposition E and `signed.py` (Section 11a): no error affecting validity.
  It found two implementation defects and four minor points, all fixed. The
  kernel check started at x = 0.93 instead of log q_min, which is
  conservative but invalidated the remainder radius there. The census term
  suffered interval dependency, which cost 6.6e-5 in C before the centred
  form. The minor points were the q_min assertion, the pin of the Y_E rows,
  the wording of the limit step, and sanity assertions. The reviewer also
  checked the floors, q_min = 41^4, the exactness of F, the series against
  mpmath, and perturbed kernels, all of which were rejected.
* The census programs `census_kw.c` and `census_kv.c` (Section 5), against
  `census_d3k.c` as specification: no error that changes any output. This
  includes no way to exceed `census_d3k.c` counts. The reviewer also ran
  comparisons on seven further ranges, among them (1000, 4e10] and a range
  just below 2^50, plus 39 primes with v2(p-1) = 24..38, and unit tests of the
  arithmetic.
* The third D4 form (Section 11b): Lemma 4', the Mackey identity, the residue degrees, `gkernel.py`,
  `octcoef.c`, `dcoef4.c`, `leval.py`, `dihedral_ceiling3.py` and `census_kv3.c`. It found no mathematical
  error. It found four formal gaps in the certified numerics, all fixed before the final certification (Section
  11b); none was likely to change a number. It reproduced the Euler-factor identity at many primes, all 160
  conductors, the degree-8 coefficient rule at 500 primes up to 2^40, and the ker-W' census bins.

The 1.043152 certificate (Section 11b) was assembled after that review: final L-values, census to 4e13 relative
to E_W', `signed3.py certify`, witness. Its default replay passes in 61 minutes; it hash-checks every file the
certification reads and recomputes the L-values at sampled abscissae (`--full` and `--full-lv` recompute all).

A ninth review, of the assembly of this certificate, found no error affecting the bound. It recomputed all 144 hp3
files bit-identically and checked orbit 20 against PARI's lfun. It also reproduced the census bins by an independent
classification, the Euler-factor identity at all primes up to 1000, and C_eff and the margin. It found gaps in
`reproduce_w3.py`, all now closed:

* it sampled only one abscissa that is actually used;
* it had no independent check of the ker-W' bins;
* it did not assert that every file read is pinned;
* it ran the Euler-product test only with `--full`;
* two data files were unpinned.

The 1.043124 step (Section 11a) adds twelve abscissae and census data to 8.5e14; its replay passes in 50 minutes,
but its assembly has not had a review of its own.

The 1.043119 step adds only census data from the reviewed `census_kv.c` (four
bins recounted by `census_d3k.c`) and new kernel parameters. Otherwise it is
assembled like 1.043118, and its replay passes. It has not had a review of
its own. Likewise, the 1.043123 certificate was replayed in full, but no
independent reviewer has run its end-to-end certification on the final
long-AFE data. That data was still being computed during the review of
Proposition E.

Their minor issues are also fixed. Following the fourth review, (*) is now
verified for every q >= 2 and has a closed-form cross-check, and sigma is
recorded in the L-value files. The double-count fix has not been re-reviewed,
but the third reviewer's own patched computation gives the same
C_eff <= 0.04364945 at sigma = 1101/1100. Not Lean-formalized.

This directory refines the [41-cap variation](../0.042901/README.md)
(exponent 1.042901), itself a variation of the
[Q(sqrt 241) construction](../0.04273/README.md) (exponent 1.04273). The
following are those of the 41-cap variation and are not changed:

* the tower, the field family and the Golod-Shafarevich count;
* the genus field E and its zeta value;
* the ceiling argument.

The archimedean and selected shell profiles are re-optimized at each delta.
What changes is how the ceiling C bounds the contribution of the primes of B
whose behaviour in the tower field K is not fixed by the construction.

## 1. Result claimed

For delta = 0.043171 the construction gives finite planar sets U_j with
|U_j| -> oo and u(U_j)/|U_j|^{1+delta} -> oo (exponent **1.043171**). The
certified margin is >= 1.05e-5 after the concentration allowance. It uses the
effective constant C_eff = 0.0422764 in place of C = 0.04871285, through
Proposition E over the field E_W'' of four D4 forms, together with general shell
weights at the finite places 2, 3, 5 (Section 11c).

| step | effective constant | exponent |
| --- | --- | --- |
| 41-cap variation (base) | 0.04871285 | 1.042901 |
| + adaptive dichotomy (Props. A, B) | 0.048134265 | 1.042925 |
| + D4 census to 10^12 (Lemma 2) | 0.0471692613 | 1.042965 |
| + dihedral ceiling over E_W at sigma = 1101/1100, census to 10^13 relative to E_W (Sections 8-10) | 0.0436495 | 1.043113 |
| + refined Tsfasman-Vladut step at sigma = 801/800 (Proposition D, Section 11) | 0.0435763 | 1.043116 |
| + census relative to E_W extended to 4e13 (`census_kw.c`, Section 11) | 0.0435534 | 1.043117 |
| + census relative to E_W extended to 1.5e14 (`census_kv.c`, Section 11) | 0.043533 | 1.043118 |
| + census relative to E_W extended to 7e14 (`census_kv.c`, Section 11) | 0.0435103 | 1.043119 |
| + signed kernel over 24 abscissae (Proposition E, Section 11a) | 0.0433928 | 1.043123 |
| + 12 more abscissae, census relative to E_W to 8.5e14 (Section 11a) | 0.0433891 | 1.043124 |
| + third D4 form: ceiling over E_W' with 32 degree-8 L-functions, census relative to E_W' to 4e13 (Section 11b) | 0.0427163 | 1.043152 |
| + fourth D4 form: ceiling over E_W'' with 128 degree-8 L-functions, census relative to E_W'' to 4e13 (Section 11c) | 0.0422764 | 1.043170 |
| + general shell weights at 2, 3, 5 (margin +1.53e-5, Section 11c) | 0.0422764 | **1.043171** |

## 2. Idea

The ceiling bounds (1/d) log L_F(1) prime by prime, through the termwise bound
log zeta_K(sigma)/[K:Q] <= Y_*, which compares K with the Kummer field E. A
prime of B that splits completely in E (**Frobenius vector 0**) is charged as
if it split completely in K. These primes carry about 0.005 of C. Three
independent mechanisms recover most of it.

* **D4 fields inside the tower (Lemma 2).** The degree-two layer
  gr_2 G_B = D_2 G_B / D_3 G_B has dimension 15. Exactly 27 of its nonzero
  linear forms are of D4 type (Section 4), and they span its dual. Each is
  realized by an explicit field M = F0(sqrt beta), with F0 biquadratic over B
  inside E and beta an S-unit, and every tower field contains M. At a vector-0
  prime, beta is a nonsquare exactly when the form is nonzero on its
  Frobenius, and then f_K(p) >= 2 for every K.
* **Census.** Fifteen of these fields with independent forms test every
  vector-0 prime of degree one up to norm 10^13. All are detected except those
  whose Frobenius lies in D_3 G_B (36,210 of 1.35 * 10^9). The
  detected primes lose their charge.
* **Dihedral ceiling (Sections 8-10).** A census cannot reach the infinite tail.
  Two of the D4 forms, psi_10 and psi_23, have a sum psi_24 that is again of D4
  type. So E_W = E M_10 M_23 is a central extension of E by C2 x C2, all of
  whose nonlinear irreducible representations are two-dimensional and
  dihedral. Then zeta_{E_W} is zeta_E times 192 squared Hecke L-functions of
  degree 4. Each of these is a quotient of two Dedekind zeta functions, so its
  root number is 1. Conductors are at most 2.7e10, and the certified
  degree-four kernels of the 1.0418235 archive evaluate them near
  sigma = 1 in about a second each. Replacing E by E_W in the ceiling
  takes three quarters of the vector-0 primes, at all norms, from residue
  degree 1 to 2. The census then applies to the remaining quarter.
* **A third D4 form (Section 11b).** A third form psi_19 doubles the field again: E_W' = E M_10 M_23 M_19 has
  [E_W':Q] = 4096, and zeta_{E_W'} needs, besides 128 more dihedral twists, 32 L-functions of degree 8 over Q,
  L(rho_19 (x) rho_o (x) lambda_w) = zeta(F')/zeta(F_L), with conductors up to 1.8e20. Their certified values come
  from new kernels (Gamma_C(s)^4) and a C program that sieves the primes up to 5.3e10. Half of the remaining
  ker-W vector-0 primes, at all norms, then move from residue degree 1 to 2.
* **Adaptive dichotomy (Propositions A, B).** Where the residue degree in K
  stays unknown, an adversary cannot both keep it small and avoid a reduction
  of the ceiling. If the degree is small, the split places of F above p carry
  shell profiles. If it is large, or if the places of F above p are inert in
  K, the Euler factor of L_F is smaller. Alone this gives exponent 1.042925.
  After the other two mechanisms it adds about 4e-7 to the margin.

## 3. Setting and notation

Notation of [papers/0.04273](../0.04273/main.tex) (Sections tw, gf, an, geo, fw,
cert):

* B = Q(sqrt 241); S the six primes above 2, 3, 5.
* G_B = G_S/N (Definition tw:GB) and B_G; the Zassenhaus filtration D_n G_B;
  gr_n G_B = L_n/R_n (Definition tw:relation-space).
* E the Kummer field (fixed field of D_2 G_B, [E:Q] = 512); the Kummer basis
  alpha_0, ..., alpha_7 of (tw:alpha).
* Frobenius vectors in F_2^8: bit i is set iff alpha_i is a nonsquare at the
  prime.
* Sigma_2 and P_4 (Definition an:P4); g_s(q) = -log(1 - q^-s);
  sigma = 1 + epsilon = 301/300; Y_*, D, kappa_oo of Section an.

The 41-cap variation ([construction-41cap.md](../0.042901/research/construction-41cap.md))
caps the two primes t1, t2 above 29 and the prime P41[1] above 41 (vector
[0,0,1,1,1,0,0,0]); 7 O_B is not capped. Its family K is defined as in
Definition an:family. Every K in K has these properties:

* K is Galois over B and unramified over B outside S;
* K contains the fixed field of D_4 G_B, hence E and the fixed field of
  D_3 G_B;
* K/F, with F = K^<iota_1>, satisfies (G1)-(G3), with d = [F:Q] = [K:B] and
  theta_* <= theta < 1/2.

The ceiling (Theorem an:ceiling, recomputed in `ceiling41.py`) holds with
C = 0.04871285 > Y_* + epsilon (kappa_oo + D).

A prime p of B is **free** if it is not in S and is not t1, t2 or P41[1]. Its
**floor** f0(p) is the residue degree that the termwise bound behind
Proposition an:Ystar uses for p: f0 = 1 if the vector of p is 0, f0 = 4 if
p is in P_4, and f0 = 2 otherwise. So p contributes g_sigma(N^f0)/(2 f0) to
Y_* (N = Np), and f0 divides f_K(p) for every K. The census below raises
floors, and the dihedral ceiling replaces E-terms by E_W-terms; Propositions
A and B use whatever termwise bound is in force.

Throughout, for a vector-0 prime of norm N,

    T(N) = g_sigma(N)/2 - g_sigma(N^2)/4 = (1/2) artanh(N^-sigma),

which is decreasing in N. It is the reduction of the term of p when its floor
rises from 1 to 2.

## 4. Lemma 2 (detection by D4 fields)

*Data.* Let r1, r2 in F_2^8 be independent rows, phi_1: v -> (r1.v, r2.v), and
rho in F_2^2 \ {0}. Let psi be the linear form on L_2 with

    psi(v^[2]) = [phi_1(v) = rho],   psi([v, w]) = det(phi_1 v, phi_1 w),

and suppose psi vanishes on R_2 (the 22 elements tw:initials-list). Let
a = prod alpha_i^{r1_i}, b = prod alpha_i^{r2_i}, F0 = B(sqrt a, sqrt b), and let
beta in F0^* be an S-unit such that for each sigma != 1 in Gal(F0/B):

* sigma(beta)/beta = u_sigma^2 with u_sigma in F0^*;
* t_sigma = u_sigma sigma(u_sigma), which is +1 or -1, equals -1 exactly
  when sigma acts on (sqrt a, sqrt b) by the signs (-1)^rho.

*Statement.* M = F0(sqrt beta) is Galois over B with group D4 and is
contained in every K in K. If a free prime p of B splits completely in F0 and
beta is a nonsquare in the residue field of a prime of F0 above p, then
f_K(p) >= 2 for every K in K.

*Proof.*

*M is a D4 field.* Since sigma(beta)/beta is a square for every sigma, M/B is
Galois. Its group is an extension of Gal(F0/B) = V4 by the central subgroup
Gal(M/F0) = C2. A lift of sigma sends sqrt beta to +-u_sigma sqrt beta, so its
square acts on sqrt beta by t_sigma, and the lift has order 4 exactly when
t_sigma = -1. Among the central extensions of V4 by C2, only D4 has exactly one
nonidentity class lifting to elements of order 4: C2^3 has none, C4 x C2 two
and Q8 three. So the group is D4, with rotation class rho.

*M lies in the tower.* M/B is unramified outside S: F0 lies in E, beta is an
S-unit, and S contains the dyadic primes. Let phi: G_S -> D4 be the quotient
map. In D4 an element squares to the central involution z iff its image in V4
is rho, and two elements have commutator z iff their images are independent.
So phi(g^2) = z^{psi(v^[2])} and phi([g, h]) = z^{psi([v, w])} for elements with
elementary images v, w. Hence phi kills the generators of N (Lemma
tw:GB-presentation):

* the dyadic kernel generators x^2, [x,y], [x,z], whose classes lie in R_2,
  and [[y,z],z], z^4, [y,z]^2, which die in D4 (class 2, exponent 4);
* tau_nu^2 and phi_nu^2 above 3 and 5, whose classes lie in R_2;
* the cap relations Frob^4.

So phi factors through G_B. As D_3(D4) = 1, it factors through G_B/D_3 G_B,
and M lies in the fixed field of D_3 G_B, which every K contains.

*Detection.* If p is free and splits completely in F0, and beta is a
nonsquare at the prime P of F0 above p, then P (unramified, as p is outside S)
is inert in M/F0. So f_M(p) = 2, which divides f_K(p). The test does not
depend on P: the primes of F0 above p are conjugate, and sigma(beta)/beta is a
square. QED

*Remarks.* For a vector-0 prime with Frobenius g in D_2 G_B, phi(g) =
z^{psi(g mod D_3)}. So the test evaluates psi on the class of g in gr_2 G_B,
and forms in the span of tested ones are evaluated by linearity.

*Which forms occur.* A form psi on gr_2 G_B determines a quadratic form
q(v) = psi(v^[2]) on F_2^8 with polar form B_psi. `d4search.py` and
`dihedral/plane.py` classify all 2^15 - 1 nonzero forms. Exactly 27 have
rank B_psi = 2 (all of D4 type, q vanishing on the radical); all others have
rank 4, 6 or 8 (irreducible representations of dimension >= 4). The 27 span
the dual of gr_2 (rank 15).

## 5. The census

*The fifteen fields* (`certificates/d4fields15.json`). Fifteen of the 27
classes with independent forms and small beta. `d4beta.gp` found beta: it
computes the S-units of F0 modulo squares (bnfunits), the Gal(F0/B)-invariants
and the linear map beta -> (t_sigma), then solves for the pattern of rho and
minimizes size over the solutions. `vd4.gp` (using `vd4lib.gp`) re-verifies
each beta in an independently built model of F0:

* beta is an S-unit;
* the squares sigma(beta)/beta, and the t-pattern;
* the relative discriminant of F0(sqrt beta)/F0 has norm involving only 2, 3
  and 5.

`rootcheck.py` compares the Legendre test with root counts of the degree-16
fields.

*Programs.* The test runs at the degree-one primes (p, sqrt 241 - r):

* square roots of the Kummer residues give an embedding of F0_i into F_p, and
  beta_i is evaluated from its coordinates;
* necessary conditions for vector 0 are p = 1, 49 mod 120 and (241/p) = 1,
  since E contains sqrt -1, sqrt 2, sqrt 3, sqrt 5 and sqrt 241.

The implementations:

* `census_gain.py` (Python) treats norms <= 1.2e7;
* `census_d3.c` produced the stored bins on (1.2e7, 1e12];
* `census_d3w.c` sieves only the two progressions;
* `dihedral/census_d3k.c` additionally classifies each prime by the 15-bit
  pattern and produced the stored bins on (1.2e7, 1e13];
* `dihedral/census_kw.c` is a faster version of `census_d3k.c` (about 4x in
  its mode W) and produced the stored bins on (1e13, 4e13] (prefix `kw4e13`);
* `dihedral/census_kv.c` is mode W of `census_kw.c` in AVX-512 IFMA (about
  3.5x faster again) and produced the stored bins on (4e13, 1.5e14]
  (prefixes `kv*`).

`census_kw.c` uses Montgomery arithmetic modulo p and a nonresidue found by
reciprocity. For p = 1, 49 mod 120 with (241/p) = 1, the Legendre symbols of
-1, 2, 3, 5 are all 1, and the Kummer elements satisfy
alpha_2 alpha_3 = 2, alpha_4 alpha_5 = -3, alpha_6 alpha_7 = -5,
N(alpha_1) = -1, alpha_2' = -alpha_3, alpha_4' = alpha_5, alpha_6' = alpha_7.
So a degree-one prime P has vector 0 iff alpha_1, alpha_2, alpha_4, alpha_6
are squares mod P, and then so has its conjugate. The other square roots, on
both sides, are formed from these four and sqrt -1, sqrt 2, sqrt 3, sqrt 5;
each is checked by squaring. It takes the Jacobi symbol of 120 beta (as
(120/p) = 1) and of Montgomery representatives (as (2^64/p) = 1). Mode W
decides the four fields of the W masks first. Only for sides with Frobenius
in ker W does it go on to the other fields, until one detects; it writes only
`.binsBW`. A beta divisible by the prime in a W field would exclude the side.
None can occur: the norms N_{F0_i/Q}(beta_i) are 2500, 2500, 64, 9, 9, 8100,
9, 9, 225, 5184, 74649600, 16, 16, 36, 36, all of the form 2^a 3^b 5^c. They
were computed in the fifth review by iterated resultants and reproduced
numerically from the conjugates. Since beta_i, sqrt a_i and sqrt b_i are
integral at p >= 7, beta_i is a unit at every prime above P. Every run
reports zero = 0. In mode check it also runs the eight-element test on both
sides for every candidate. On (6e4, 1.2e7], (1e13, 1.0004e13] and
(5e13, 5.0004e13], all outputs of modes check and W equal those of
`census_d3k.c`: the bins, the summary and the undetected lists (replay
step 7). The Jacobi routine was also compared with the division-based one on
2.1e7 random and exhaustive pairs.

`census_kv.c` runs the same computation on eight primes at a time:
Montgomery arithmetic in radix 2^52 with the IFMA instructions, and
Euler's criterion for the Legendre symbols. The four vector-0 rounds compact
their survivors between rounds. For the vector-0 primes it computes the same
square roots and D4 fields as `census_kw.c` mode W. All sixteen roots of each
such prime are checked by squaring, which re-proves vector 0. About one in
sixteen of these primes (all of them in mode Wcheck) is also recomputed by
the scalar code of `census_kw.c`, and the outcomes must agree. The sieve is a
bit array: periodic word patterns mark the multiples of 7..31 and the
nonresidues mod 241. On (1e8, 3e8], (1e12, 1.002e12], (1e13, 1.0004e13] and
(5e13, 5.0004e13], its `.binsBW`, summary and undetected list equal those of
`census_kw.c` mode W, in both modes. Replay step 7 repeats this on three
ranges when the processor has IFMA. Otherwise `census_kv.c` is not exercised,
and `--rerun` recomputes the `kv` ranges with `census_kw.c`, which gives the
same bins.

All C programs reproduce the Python test prime by prime and field by field on
the 2924 vector-0 primes of degree one with norm 6e4..1.2e7, and agree with
each other on overlapping ranges. A second independent PARI implementation
(review) matched bits, bins and undetected lists on eight sample ranges up to
10^12.

The detected primes are recorded in geometric bins
[XLO (1+2^-16)^j, XLO (1+2^-16)^(j+1)). The sum of T is bounded from below at
the bin edge one step higher, which absorbs a floating-point misassignment by
one bin.

| range of norms (degree-one primes) | vector-0 primes | detected | sum of T (lower) |
| --- | --- | --- | --- |
| 65809 .. 1.2e7 | 2924 | 2924 | 0.000589695 |
| (1.2e7, 1e10] | 1,768,122 | 1,768,110 | 0.000621195 |
| (1e10, 1e12] | 145,096,446 | 145,093,184 | 0.000327149 |
| (1.2e7, 1e13] (`census_d3k.c`, all classes) | 1,351,669,408 | 1,351,633,198 | (see Section 10) |

The 13 vector-0 primes inert in B/Q with norm <= 1.2e7 are not tested by the
census. Over E they keep floor 1 and enter only the adaptive sum. Over E_W
their residue degree is read from the Euler factors at p (Section 8). The undetected primes are listed
in `certificates/census/*.txt` and `certificates/dihedral/census/*.txt`. They
are fewer than equidistribution predicts, as are vector-0 primes of small
norm; this is a Chebyshev-type bias and is not used.

## 6. Lemma 1 (inert places in the relative Euler product)

Let K be in K and s > 1 real. Then

    (1/d) log L_F(s) = (1/[K:Q]) log zeta_K(s) - (1/d) sum_q artanh(Nq^{-s}),

the sum over the primes q of F that are inert in K. For a free prime p of B
with f = f_K(p), let rho = rho_K(p) be the proportion of the primes P of K
above p with iota_1 P = P.

* The primes of F above p that are inert in K are the q = P cap F with
  iota_1 P = P. There are rho d/f of them, each of norm N^{f/2}, and rho > 0
  only if f is even.
* The primes of F above p that split in K number (1 - rho) d/(2f), each of
  norm N^f.

*Proof.* The Euler factor of L_F at q is (1 - x)^-1 if q splits in K and
(1 + x)^-1 if q is inert, x = Nq^-s; no finite prime of F ramifies in K (G2).
The zeta_K factor is (1 - x)^-2, respectively (1 - x^2)^-1, and
-(1/2) log(1 - x^2) + log(1 + x) = artanh x. Since [K:Q] = 2d this gives the
identity. K/B is Galois with [K:B] = d and p is unramified, so there are d/f
primes P above p, with cyclic decomposition groups of order f. The primes of
K above q = P cap F are P and iota_1 P. If iota_1 P = P, then q is inert,
Nq = N^{f/2}, and iota_1 lies in the cyclic decomposition group of P, so f is
even. If iota_1 P != P, then q splits and Nq = N^f. QED

(Moreover iota_1 = Frob_P^{f/2} then has elementary image 0 if f >= 4, so
rho > 0 only if f = 2 and the vector of p is that of iota_1. This is not used.)

With f in f0 2^N and N = Np, put

    R_p(f) = g_sigma(N^f0)/(2 f0) - g_sigma(N^f)/(2 f)   (>= 0, increasing in f),
    I_p(f) = artanh(N^{-f/2})/f  for f even,   I_p(f) = 0 for f odd,
    S_p(f) = max(0, max_{k>=1} [log(k+1) - delta k f log N]) / (2 f),

with R_p(oo) = g_sigma(N^f0)/(2 f0), I_p(oo) = S_p(oo) = 0, and

    G_p = inf { R_p(f) + rho I_p(f) + (1 - rho) S_p(f) :
                f in f0 2^N or f = oo, rho in [0,1], rho = 0 if f is odd } >= 0.

## 7. Propositions A and B (adaptive dichotomy)

Proposition A uses only two facts about the floors f0 and the bound Y_* in
force:

* the termwise bound log zeta_K(sigma)/[K:Q] <= Y_*, with term
  g_sigma(N^f0)/(2 f0) at each free prime, valid for every K;
* C > Y_* + epsilon (kappa_oo + D), or, by Proposition D (Section 11),
  C > Z_sel(1) + a (Y_*(sigma) - Z_sel(sigma)) + b (2 kappa_oo - T_sel) for
  some a >= 1 and b >= 0 satisfying the kernel inequality (*) there.

**Proposition A (adaptive ceiling).** Let A be a finite set of free primes of B.
There is m_0 such that every K in K with [K:B] >= m_0 satisfies

    (1/d) log L_F(1) < C - sum_{p in A} [ R_p(f_K(p)) + rho_K(p) I_p(f_K(p)) ].

*Proof.* Suppose not.

*Choice of a subsequence.* There are K_j in K with [K_j:B] strictly increasing
that violate the inequality. As A is finite and the f_j(p) are powers of 2,
pass to a subsequence along which, for each p in A, either f_j(p) = f_oo(p) is
constant or f_j(p) -> oo =: f_oo(p), and rho_j(p) -> rho_oo(p). Then
R_p(f_j) -> R_p(f_oo), and rho_j I_p(f_j) -> rho_oo I_p(f_oo). Pass to a further
subsequence so that the limits beta_q of the proof of Proposition
an:prime-budget exist, and put Z(s) = sum_q beta_q g_s(q).

(i) Fix s in (1, 2]. By Lemma an:monotonicity and the proof of Lemma an:shift,
(1/d) log L_F(1) <= (1/d) log L_F(s) + Upsilon(s - 1, theta). By Lemma 1, and
since artanh > 0 on (0,1),

    (1/d) log L_F(s) <= (1/[K:Q]) log zeta_K(s) - sum_{p in A} rho_K(p) artanh(Np^{-f_K(p) s/2})/f_K(p).

Along the subsequence the right side tends to Z(s) - I_oo(s), where
I_oo(s) = sum_p rho_oo artanh(Np^{-f_oo s/2})/f_oo. Hence

    C - sum_p [R_p(f_oo) + rho_oo I_p(f_oo)] <= Z(s) - I_oo(s) + sup_theta Upsilon(s-1, theta).

Let s decrease to 1. Then Z(s) increases to Z(1) < oo, I_oo(s) tends to
sum_p rho_oo I_p(f_oo), and the supremum tends to 0. So
C - sum_p R_p(f_oo) <= Z(1).

(ii) As in Proposition an:prime-budget, Z(1) <= Z(1 + epsilon) + epsilon (kappa_oo + D);
the debit D uses only lower bounds for the types.

(iii) Keeping the exact term g_sigma(N^{f_K})/(2 f_K) for p in A in the
termwise bound gives (1/[K:Q]) log zeta_K(sigma) <= Y_* - sum_{p in A} R_p(f_K(p))
for every K. Hence Z(1 + epsilon) <= Y_* - sum_p R_p(f_oo).

Together, C - sum R <= Y_* + epsilon (kappa_oo + D) - sum R < C - sum R, a
contradiction. QED

**Lemma 3 (transfer with field-dependent constants).** Proposition fw:transfer
remains true if its hypothesis log L_{F_j}(1) <= d_j C is replaced by
log L_{F_j}(1) <= d_j C_j, and C by C_j in the margin (fw:margin). In its proof
the hypothesis enters only once, for the field at hand: in the lower bound for
the first factor via (geo:mass-density). The choice of eta and the Chebyshev
step depend only on inf_j of the margins and on the finite parameter set.

**Proposition B (margin).** Let 0 < delta < 1 and let A be a finite set of
free primes. Take the base data of the 41-cap certificate at delta: the shell
profiles above 2, 3, 5, 29 and P41[1], and an admissible archimedean pair with
Fourier constants (2, 1). Let M_*(theta) be their margin computed with a
constant C' for which the hypotheses of Proposition A hold. Suppose that:

* the Fourier condition holds for the base data;
* the theta-slope of M_* is positive;
* M_*(theta_*) + sum_{p in A} G_p > 0.

Then there are finite sets U_j in R^2 with |U_j| -> oo and
u(U_j)/|U_j|^{1+delta} -> oo.

*Proof.* Choose K_j in K with [K_j:B] -> oo and [K_j:B] >= m_0 of
Proposition A, and put C_j = C' - sum_{p in A} [R_p(f_j) + rho_j I_p(f_j)].

*The places.* P_j consists of the base places and, for each p in A with
S_p(f_j(p)) > 0, of the places of F_j above p that split in K_j. These carry
the unweighted shell profile (Np^{f_j}, k), with k maximizing in S_p
(Lemma fw:shell-lemma). By Lemma 1 they add (1 - rho_j(p)) S_p(f_j(p)) to
(1/d_j) sum log F_delta. Their parameters lie in a finite set, and they lie
over primes of B other than those of the base places.

*Applying the transfer.* Apply Lemma 3. The Fourier condition holds because
H_f and mu_f only increase. The margin of K_j/F_j is at least
M_*(theta_*) + sum_p G_p > 0. QED

## 8. Lemma 4 (the field E_W)

Let psi_10, psi_23 be the forms of the D4 classes 10 and 23 of
`dihedral/d4all27.json`. Then psi_24 = psi_10 + psi_23 is again of D4 type
(`plane.py`). Twelve such planes exist and no three-dimensional subspace has
the property, so W = {0, psi_10, psi_23, psi_24} is maximal. For each
o in {10, 23, 24}, let M_o = F0_o(sqrt beta_o) be the D4 field of `vd4_data27.gp`,
verified as in Lemma 2 by `vplane.gp`. Let W^perp in gr_2 G_B be the common
kernel of W, and let E_W be the fixed field of the preimage of W^perp in
D_2 G_B.

(a) E_W = E M_10 M_23 contains each M_o, lies in every K in K, and
Gal(E_W/B) = G_W is a central extension of Gal(E/B) = F_2^8 by Z = F_2^2.
[E_W:Q] = 2048.

(b) The irreducible representations of G_W are the 256 characters of
Gal(E/B), and for each o the 64 two-dimensional representations
rho_o (x) lambda_w. Here rho_o is the dihedral representation of Gal(M_o/B),
lambda_w is the character of Gal(E/B) of w in F_2^8, and w runs over a
complement of span(r1, r2) of the form o.

(c) zeta_{E_W}(s) = zeta_E(s) prod_o prod_w L(s, rho_o (x) lambda_w)^2, and

    L(s, rho_o (x) lambda_w) = zeta_{K_{o,w}}(s) / zeta_{Bc_o}(s).

Here:

* Bc_o = B(sqrt c) is the fixed field in F0_o of a non-rotation element tau
  of Gal(F0_o/B);
* K_{o,w} = Bc_o(sqrt(gamma_o alpha^w)), with gamma_o = (1 + u_tau)^2 beta_o.

L(s, rho_o (x) lambda_w) is the L-function of a quadratic Hecke character of
the quartic field Bc_o. It is entire and of degree 4 over Q. When
r_1(K) = r_1(Bc) (checked for all 192) its completed function is
Q^{s/2} Gamma_C(s)^2 L(s), with Q = |d(K)|/|d(Bc)|, and it satisfies
Lambda(s) = Lambda(1 - s): the root number is 1.

*Proof.*

(a) For g in D_2 G_B with class gbar, the quotient map phi_o of M_o sends g to
z^{psi_o(gbar)}. This is trivial on the preimage of W^perp, so each M_o lies
in E_W; and E lies in E_W. By Lemma 2, M_o lies in the fixed field of
D_3 G_B, hence in every K. G_W/Z = Gal(E/B), and Z = gr_2/W^perp is central
because [G_B, D_2] lies in D_3. E M_10 M_23 has degree 4 over E, since
psi_10 != psi_23, and |G_W| = 2^10.

(b) The commutator pairing composed with zeta in W \ {0} is the polar form of
zeta, which is nonzero. So [G_W, G_W] = Z, and the linear characters are those
of Gal(E/B). The irreducibles with central character zeta factor through
G_W/ker zeta = Gal(E M_zeta/B). This is the fiber product of Gal(E/B) and D4
over V4, and its representations with nontrivial central character are the 64
twists rho_zeta (x) lambda. Two twists agree iff lambda factors through V4,
that is, iff w lies in span(r1, r2). Counting, 256 + 3 * 64 * 4 = 1024 = |G_W|.

(c) The first formula is the Artin factorization of zeta_{E_W}. For the
second, rho_o (x) lambda_w is the representation of the twisted D4 field
F0(sqrt(beta alpha^w)). Since u_tau tau(u_tau) = 1, the lift s of tau with
s(sqrt beta) = u_tau sqrt beta is a reflection, and (1 + u_tau) sqrt beta is
fixed by s. So K = Bc(sqrt((1 + u_tau)^2 beta)) is the fixed field of <s>
(after twisting, of beta alpha^w), and Bc is the fixed field of the V4
containing s. From Ind_{<s>}^{D4} 1 = 1 + chi + rho one gets
zeta_K = zeta_B L(chi) L(rho) and zeta_Bc = zeta_B L(chi). The completed
Dedekind zeta functions satisfy Lambda(s) = Lambda(1-s); their quotient gives
the root number and the conductor. Its gamma factor is
Gamma_R^{r1(K) - r1(Bc)} Gamma_C^{r2(K) - r2(Bc)} = Gamma_C^2. QED

**Proposition C (ceiling over E_W).** Replace in the ceiling:

* Y_* by Y_W - Delta'_sel - Delta'_P4, where
  Y_W = (1/2048) log zeta_{E_W}(sigma) = Y_E/4 + (1/1024) sum_{o,w} log L_{o,w}(sigma);
* the corrections by the differences between E_W-terms and K-terms at the
  selected primes, and at the P_4 primes whose residue degree in E_W is 2.

Then Theorem an:ceiling and Propositions A and B hold with
C_W = Y_W - Delta'_sel - Delta'_P4 + epsilon (kappa_oo + D) and with floors
taken in E_W.

*Proof.* E_W lies in every K and is Galois over B, so Lemma an:local-contribution
gives the termwise comparison of K with E_W. This is the proof of Proposition
an:Ystar with E_W in place of E. Proposition an:prime-budget is unchanged, and
D still uses only lower bounds for the types. QED

*Residue degrees in E_W.* G_W embeds in Gal(E/B) x Gal(M_10/B) x Gal(M_23/B).
So an unramified prime has residue degree lcm(f_E, f_{M_10}, f_{M_23}), as
follows:

* nonzero vector v: 4 iff phi_1(v) = rho for o = 10, 23 or 24, else 2;
* vector 0: 2 iff its Frobenius is off ker psi_10 cap ker psi_23, else 1. For
  degree-one primes this is read from the 15 census bits through
  `wmasks.json`. For the 13 primes inert over Q (norm p^2 <= 1.2e7) it is
  read from the Euler factors at p of the twist-0 L-functions:
  (1 -+ p^-2s)^-2 for Frobenius 1 or z (`inertv0.py`). Twelve are off ker W;
  2521^2 is in it.

Above 2, the E_W-term is computed exactly from the Euler factors at 2 of the
192 L-functions. These factors come from PARI prime decompositions in K and
Bc. Above 3 and 5 the same factors reproduce the E-terms, as they must
(asserted).

## 9. The 192 L-values

`dihedral/export.gp` builds, for each of the three D4 fields and each of the
64 twists, the following data (`ddata_orb*.json`):

* Bc, gamma_o and K_{o,w};
* the conductor Q = |d(K)|/|d(Bc)|, which ranges over 4.2e8 .. 2.7e10;
* the Euler factors at 2, 3, 5 and at 7 <= p <= 1000.

`dcoeffs.py` computes the Dirichlet coefficients up to N = floor(4 sqrt Q) + 1.
For p > 1000 it uses quadratic residue symbols of gamma_w at the primes of Bc.
Only degree-one primes of B matter there, since N < 10^6.

`dafe.py` evaluates each L_{o,w}(301/300) with the certified kernels of
`nonpositive-afe.py` (kind 'quartic', Gamma_R(s)^2 Gamma_R(s+1)^2) and root
number 1. The result is a ball of radius about 2e-6, at about one second per
L-function.

`dcheck.py` cross-checks in two ways:

* the coefficients of all 192 twists agree with PARI's Dirichlet series
  zeta_K/zeta_Bc (dirzetak) up to 20000;
* for sample twists, PARI's lfun with the same data satisfies the functional
  equation to 2^-41 .. 2^-127, and its value lies inside the certified
  enclosure.

| family (orbit) | conductors | sum log L at 301/300 | sum log L at 1101/1100 |
| --- | --- | --- | --- |
| 10 | 4.2e8 .. 2.7e10 | 19.2708 | 19.371 |
| 23 | 1.7e9 .. 2.7e10 | 14.8444 | 14.929 |
| 24 | 1.7e9 .. 2.7e10 | 14.9113 | 14.997 |

At sigma = 301/300, Y_W = Y_E/4 + 49.0265/1024 = 0.068538 (radius 6.4e-7),
against Y_E = 0.0826446.

*Abscissa.* In Proposition an:prime-budget the shift from 1 + epsilon to 1
costs epsilon (kappa_oo + D), while the pole of the zeta function used in Y_*
grows like (1/degree) log(1/epsilon). For E the degree is 512 and epsilon = 1/300
is near optimal. For E_W it is 2048, which moves the optimum to about 1/1300.
A scan of sigma = 1 + 1/n for n = 300, 600, 900, 1000, 1100, 1200, 1300, 1500
gives the smallest C_eff at n = 1100. Y_E(1101/1100) = 0.0855583 is recomputed
by `afe241.py`, and the 192 L-values by `dafe.py`. The census sums and the
adaptive terms are evaluated at the same sigma.

## 10. Total gain and certified margin

All terms are at sigma = 1101/1100 (`dihedral/dihedral_ceiling.py`):

| quantity | value |
| --- | --- |
| Y_E | 0.0855583 |
| Y_W = Y_E/4 + 49.297/1024 | 0.069531 (radius 7.7e-7) |
| dyadic E_W-term / E-term / K-term | 0.0269308 / 0.0359078 / 0.0020116 (one dyadic prime has type (8,2) in E_W) |
| Delta'_sel (dyadic, and t1; t2 and P41[1] already have residue degree 4 in E_W, a rotation in M_10 and M_23) | 0.0252147 |
| Delta'_P4 | 0.000868301 |
| C_W = Y_W - Delta'_sel - Delta'_P4 + epsilon (kappa_oo + R) | <= 0.044035533 |

The gains relative to E_W:

| part | lower bound |
| --- | --- |
| census of vector-0 primes with Frobenius in ker W, norms <= 1.2e7 (606 primes) | 0.000100040 |
| adaptive dichotomy, norms <= 1.2e7 (11 terms) | 0.000000398 |
| census bins (1.2e7, 1e13], class binsBW (337,835,097 primes) | 0.000285640 |

Hence C_eff <= 0.043649455 < 0.0436495. The witness is
`certificates/dihedral/witness_0.043113.json`, with archimedean and shell
profiles re-optimized at delta = 0.043113:

    M_*(theta_*) - 4e-9 >= 5.084e-6 > 0,  Fourier condition OK,  slope > 0.

At delta = 0.043114 the same data give about -1.9e-5.

An earlier version of `dihedral_ceiling.py` left the 13 inert vector-0 primes
at floor 1. Since Y_W already uses their E_W-terms (residue degree 2 for 12 of
them), their adaptive terms T(N) were counted twice, 5.3e-6 in total. That
version claimed C_eff <= 0.043644124 and margin 1.04e-5. The third review found
this, and the numbers above are corrected.

Of the 1,351,669,408 vector-0 primes of degree one in (1.2e7, 1e13]:

* 1,351,633,198 are detected;
* their 15-bit patterns split into ker W and its complement in the expected
  proportions (337,835,097, that is 0.24995 of the detected);
* the undetected primes up to 10^12 coincide with those of the earlier
  programs.

## 11. Proposition D (a refined Tsfasman-Vladut step)

The proof of Proposition an:prime-budget bounds Z(1) - Z(1 + epsilon) by
epsilon (kappa_oo + D) through the TV inequality, uniformly in q. Two facts are
not used there:

* the selected primes (the dyadic primes, those above 3 and 5, t1, t2 and
  P41[1]) have known types, so their contributions to Z and to the TV sum are
  known exactly, the same for every K;
* the step from Z(1 + epsilon) to Z(1) can use the TV inequality through any
  kernel inequality between g_1, g_sigma and w, not only through the uniform
  bound used there.

Write beta_q = beta^sel_q + beta^rest_q, and
Z_sel(s) = sum_q beta^sel_q g_s(q), T_sel = sum_q beta^sel_q w(q). The values
are beta^sel_16 = 1/32, beta^sel_9 = beta^sel_25 = beta^sel_{29^4} = 1/4 and
beta^sel_{41^4} = 1/8.

**Proposition D.** Let a >= 1 and b >= 0 satisfy

    g_1(q) <= a g_sigma(q) + b w(q)    for every real q >= 2.              (*)

Then Theorem an:ceiling, Proposition C and Proposition A hold with any constant

    C > Z_sel(1) + a (Y_*(sigma) - Z_sel(sigma)) + b (2 kappa_oo - T_sel)

in place of Y_*(sigma) + epsilon (kappa_oo + D). Here Y_*(sigma) is the
termwise bound in force: E_W with the selected, P_4 and census corrections.

*Proof.* In the proof of Proposition an:prime-budget, or of Proposition A,
keep everything up to "C' <= Z(1)", or "C' - sum R_p(f_oo) <= Z(1)". Along the
sequence, N^sel_q(K)/(2d) is the same for every K, so beta^rest = beta - beta^sel
is a limit of nonnegative quantities, supported on q >= 2. By (*) and the TV
inequality sum_q beta_q w(q) <= 2 kappa_oo:

    Z(1) = Z_sel(1) + sum beta^rest_q g_1(q)
         <= Z_sel(1) + a sum beta^rest_q g_sigma(q) + b sum beta^rest_q w(q)
         <= Z_sel(1) + a (Z(sigma) - Z_sel(sigma)) + b (2 kappa_oo - T_sel).

Termwise, Z(sigma) <= Y_*(sigma) - sum_p R_p(f_oo). Since a >= 1 and R >= 0,
a sum R >= sum R. So the credits of Proposition A survive, and the contradiction
is as before. The debit D is no longer needed. QED

*Verification of (*)* (`dihedral/lptv.py`). For q >= 2,

* g_1(q) <= 1/(q-1) and g_sigma(q) >= q^-sigma;
* w(q) >= 2 log q/(q+1);
* q/(q+1) >= 1 - 1/q and q/(q-1) <= 1 + 2/q.

So, for q >= q_min = 41^4, (*) follows from h(x) >= 0 for x = log q, where

    h(x) = a e^{-epsilon x} + 2 b x (1 - e^{-x}) - 1 - 2 e^{-x}.

This is checked in two ways, both in Arb:

* on cells of width 1/64, up to x = 1/b + 1, using a bound for |h'| on each
  cell. A cell whose lower bound is not positive is bisected, down to width
  2^-18. Beyond x = 1/b + 1, 2 b x (1 - e^{-x}) - 1 - 2 e^{-x} is positive and
  increasing in x;
* in closed form: h(x) = phi(x) - (2 b x + 2) e^{-x} with
  phi(x) = a e^{-epsilon x} + 2 b x - 1 convex, and
  min phi = (2b/epsilon)(1 + log(a epsilon/(2b))) - 1. The second term
  decreases for x >= 1.

On [2, 2 q_min], (*) is checked directly on 5,950 geometric cells
[q0, q1 = (401/400) q0]. Since g_1 and g_sigma decrease in q and
w(q) >= 2 log q/(q+1), it suffices that
a g_sigma(q1) + 2 b log(q0)/(q1 + 1) > g_1(q0). So (*) holds for every
q >= 2. Proposition D needs only the exact types of the selected primes, not
the floors of the others.

Each replay record lists the figures for its witness:

| witness | a, b | cells (evaluations) | closed-form h >= | min of h | min q0 (RHS - LHS) on [2, 2 q_min] |
| --- | --- | --- | --- | --- | --- |
| 0.043116 | 2103/2000, 463/1e6 | 137,343 | 2.587e-4 | | 0.0430 |
| 0.043118 | 4215/4000, 2299/5e6 | 138,305 (139,565; 630 bisections) | 2.034e-5 | 2.106e-5 at x = 287.45 | 0.0452 |

The second row is from the assembly review, which also recomputed the minimum
of h independently.

*Choice of parameters.* A linear-programming study over sigma = 1 + 1/n,
n = 600 .. 5000, and over combinations of several sigma, gave a single sigma as
optimal: n = 800, a = 1.0515, b = 4.63e-4. At sigma = 801/800, where all
components are recomputed (Y_E by afe241.py, the 192 L-values, the census
sums, the adaptive terms):

| quantity | value |
| --- | --- |
| Z_sel(1) | 0.0416685 |
| Y_r = Y_*(801/800) - Z_sel(801/800) | 0.001342 (radius 6e-7) |
| B_r = 2 kappa_oo - T_sel | 1.0734269 |
| Z_sel(1) + a Y_r + b B_r - (adaptive terms) | <= 0.043576230 |
| same data with the old step | <= 0.043682198 |

The witness is `certificates/dihedral/witness_0.043116.json`, with profiles
re-optimized at delta = 0.043116 and C_eff = 0.0435763:

    M_*(theta_*) - 4e-9 >= 6.725e-6 > 0,  Fourier condition OK,  slope > 0.

At delta = 0.043117 the margin with this C_eff is about -1.7e-5.

*Census to 4e13.* `census_kw.c` extends the census relative to E_W to
(1e13, 4e13] (prefix `census/kw4e13`): 30,460,733,488 candidates and
3,807,510,358 vector-0 sides. Of these, 951,849,738 have Frobenius in ker W
and 951,741,144 of those are detected. No W-field symbol is 0 (zeroW = 0);
the norm argument of Section 5 excludes zeros in every field. In Y this gains
(1/2048) int e^{-u/800} du/u over that range of log N, to 0.03%. In C the
gain is a times that, about 2.24e-5. The optimal sigma stays at 801/800, and
the kernel moves to a = 4211/4000, b = 461/1000000. The kernel check now
bisects the cells near the minimum of h, at x = 278 for these parameters.

| quantity | value |
| --- | --- |
| Y_r = Y_*(801/800) - Z_sel(801/800) | 0.001320 (radius 8e-7) |
| Z_sel(1) + a Y_r + b B_r - (adaptive terms) | <= 0.0435533667 |

The witness is `certificates/dihedral/witness_0.043117.json`, with profiles
re-optimized at delta = 0.043117 and C_eff = 0.0435534:

    M_*(theta_*) - 4e-9 >= 5.773e-6 > 0,  Fourier condition OK,  slope > 0.

The full replay passes in 12 minutes.

*Census to 1.5e14.* `census_kv.c` extends the census to (4e13, 1.5e14]
(prefix `census/kv15e13`): 107,026,642,809 candidates and 13,378,137,262
vector-0 sides. Of these, 3,344,482,459 have Frobenius in ker W and
3,344,086,275 of those are detected, with zeroW = 0. Six bins chosen at
random from `kw4e13` and `kv15e13` were recounted with `census_d3k.c` and
agree exactly. The optimal sigma is still 801/800, now with a = 4215/4000 and
b = 2299/5000000.

| quantity | value |
| --- | --- |
| Y_r = Y_*(801/800) - Z_sel(801/800) | 0.001301 (radius 4e-7) |
| Z_sel(1) + a Y_r + b B_r - (adaptive terms) | <= 0.0435329680 |

The witness is `certificates/dihedral/witness_0.043118.json`, with profiles
re-optimized at delta = 0.043118 and C_eff = 0.043533:

    M_*(theta_*) - 4e-9 >= 2.321e-6 > 0,  Fourier condition OK,  slope > 0.

The full replay passes in 11 minutes.

*Census to 7e14.* `census_kv.c` extends the census to (1.5e14, 7e14] in four
chunks:

| prefix | range | candidates | ker W sides | detected |
| --- | --- | --- | --- | --- |
| `census/kv29e13` | (1.5e14, 2.9e14] | 132,550,827,042 | 4,142,006,999 | 4,141,512,153 |
| `census/kv43e13` | (2.9e14, 4.3e14] | 130,556,518,440 | 4,079,816,522 | 4,079,326,346 |
| `census/kv56e13` | (4.3e14, 5.6e14] | 120,076,868,429 | 3,752,342,478 | 3,751,890,226 |
| `census/kv70e13` | (5.6e14, 7e14] | 128,394,979,091 | 4,012,314,343 | 4,011,830,629 |

All have zeroW = 0. They took about 38 CPU-hours. One random bin of each was
recounted with `census_d3k.c` (interior run plus the edge slivers, binned by
the same formula) and agrees exactly. The optimal sigma is still 801/800,
now with a = 211/200 and b = 4583/10000000.

| quantity | value |
| --- | --- |
| Y_r = Y_*(801/800) - Z_sel(801/800) | 0.001279 (radius 8e-7) |
| Z_sel(1) + a Y_r + b B_r - (adaptive terms) | <= 0.0435102055 |

The witness is `certificates/dihedral/witness_0.043119.json`, with profiles
re-optimized at delta = 0.043119 and C_eff = 0.0435103:

    M_*(theta_*) - 4e-9 >= 1.169e-6 > 0,  Fourier condition OK,  slope > 0.

The full replay passes in 6 minutes (without --rerun).

## 11a. Proposition E (a signed kernel over several abscissae)

Proposition D bounds the rest of Z(1) through one kernel a g_sigma + b w with
a >= 1. Its proof only uses two facts:

* each non-selected prime's mass in K is at most its floor mass;
* the kernel is nonnegative and non-increasing.

A kernel combining several abscissae with coefficients of either sign
satisfies the same two facts. It can follow the ideal kernel
(g_1 - b w)_+ much more closely than one exponential.

Notation. For a non-selected prime P of B, let f_P be its floor and
nu_P = 1/(2 f_P) its floor mass. The floor is the residue degree in E_W,
raised by the census to 2 for detected primes and by the P_4 corrections.
The floor sum is

    F(sigma) = sum_P nu_P g_sigma(N_P^(f_P)) = Y_*(sigma) - Z_sel(sigma),

with Y_* the termwise bound of Sections 9-10 (census bins included).

**Proposition E.** Let 1 < sigma_1 < ... < sigma_m < 101/100, let
c_1, ..., c_m be real numbers of any sign, and let b >= 0. Suppose that
lambda = sum_j c_j g_{sigma_j} satisfies, for every real q >= q_min = 41^4:

    (i) lambda(q) >= g_1(q) - b w(q),   (ii) lambda(q) >= 0,   (iii) lambda is non-increasing.

Then Theorem an:ceiling and Proposition C hold with any constant

    C > Z_sel(1) + sum_j c_j F(sigma_j) + b (2 kappa_oo - T_sel).

*Proof.* Keep the proof of an:prime-budget up to C' <= Z(1); the credits of
Proposition A are not used.

*A fixed field K_j of the sequence.* Let P be a non-selected prime with
K_j-residue degree f.

* Every K_j contains E_W and the D4 fields, so f is a multiple of f_P.
  (For P_4 primes, f >= 4 and Gal(K_j/B) is a 2-group.)
* The K_j-primes above P carry mass 1/(2f) <= nu_P at the norm
  N_P^f >= N_P^(f_P) >= q_min.
* By (ii) and (iii), its contribution to sum_q mu_j(q) lambda(q) is at most
  nu_P lambda(N_P^(f_P)), where mu_j is the normalized prime count of K_j
  restricted to non-selected primes.

Hence

    sum_q mu_j(q) lambda(q) <= Lambda := sum_P nu_P lambda(N_P^(f_P)) = sum_j' c_j' F(sigma_j'),

where the last sum converges absolutely.

*The limit.* Since lambda >= 0, Fatou's lemma gives
sum_q beta^rest_q lambda(q) <= Lambda for the limit measure beta^rest, which
is supported on [q_min, oo). Apply (i) termwise to beta^rest and the TV
inequality with the selected primes removed, as in Proposition D, using
b >= 0:

    Z(1) = Z_sel(1) + sum_q beta^rest_q g_1(q) <= Z_sel(1) + Lambda + b (2 kappa_oo - T_sel).

QED. (Condition (ii) follows from (iii) and lambda -> 0; it is kept as a
check.)

With m = 1 and c_1 = a this is Proposition D without the adaptive credits.

*Computation* (`dihedral/signed.py`).

* **Enclosing F(sigma_j) on both sides.** The sign of each c_j decides which
  side is used. The approximate functional equations are longer than in
  Section 9:
  * the 192 L-values use N = 999999 terms for every twist (`dafe.py`
    option M), with errors <= 3.3e-9;
  * Y_E uses N = 8 sqrt(q) (`ye_hp.py`, which calls the unmodified 0.04273
    scripts), with radius ~1e-17;
  * the data are in `dihedral/hp/`.
* **Census bins.** They enter through tau(N) = sum_j c_j T_{sigma_j}(N). On
  each group of at most 8 consecutive bins, N ranges over
  [lo, hi] = [XLO (1+2^-16)^(j0-1), XLO (1+2^-16)^(j1+2)]. There tau is
  enclosed by tau(mid) + tau'([lo, hi]) [-r, r], the mean value theorem in
  centred form, so the large signed coefficients only multiply the
  derivative term. The prefixes must tile their range.
* **Checking (i)-(iii) on [log q_min, X_big].** The variable is x = log q.
  * Each condition is written in the scaled, cancellation-free form
    e^x g_s(e^x) = e^{-(s-1)x} sum_k y^{k-1}/k with y = e^{-s x}, the
    remainder entering as a 1e-55 radius; terms of w are only dropped.
  * Cells of width 1/20 (x < 60) and x/100 beyond are bounded by their Taylor
    coefficients of order 0-2 at the midpoint, plus an enclosure of the third
    derivative over the cell (power series over a ball). A failing cell is
    bisected.
* **The tail x >= X_big.** The term of the smallest abscissa has a positive
  coefficient and dominates all the others explicitly, and g_1 - b w < 0
  there.
* **Choosing the coefficients.** A linear programme over a grid picks the
  c_j and b, with margins proportional to e^{-(sigma_1 - 1) x} and column
  scaling. Its output is only a candidate; the checks above certify it.

*Result.* The abscissae are sigma = (n+1)/n for the 24 values

    n = 101, 132, 173, 227, 297, 389, 510, 667, 874, 1145, 1499, 1964, 2572,
        3368, 4411, 5777, 7566, 9909, 12977, 16996, 22258, 29151, 38178, 50000

(`hp/sigma_set.txt`). With the census to 7e14, `signed.py choose` gives
c_j with sum |c_j| ~ 1.6e3 and b = 37930860325/85099002560707 ~ 4.457e-4.
They are stored in the witness. `signed.py certify` then gives:

| quantity | value |
| --- | --- |
| kernel cells (x in [log q_min, 2e6]) | 1,972, all passing; tail dominance for x >= 2e6 |
| sum_j c_j E(sigma_j) (F without the census bins) | 0.001596 +/- 5.1e-7 |
| census term sum tau(N) | 0.0003507 +/- 6.0e-8 |
| rest + TV = sum_j c_j F(sigma_j) + b B_r | <= 0.0017242464 |
| C_eff = Z_sel(1) + rest + TV | <= 0.0433927305 |

Proposition D on the same data gives 0.0435103, so the signed kernel gains
1.18e-4 in C. The ideal ramp kernel (Section 13) would give about 0.04338.

The witness is `certificates/dihedral/witness_0.043123.json`, with profiles
re-optimized at delta = 0.043123 and C_eff = 0.0433928:

    M_*(theta_*) - 4e-9 >= 2.327e-5 > 0,  Fourier condition OK,  slope > 0.

The full replay passes in 39 minutes. It hash-checks all 117 data files,
recomputes the long-AFE data at the two extreme abscissae, and recertifies.
At delta = 0.043124 the margin with this C_eff is about -5.5e-7.

*Exponent 1.043124.* Twelve more abscissae, n = 115, 198, 340, 583, 1000, 1716, 2943, 5048, 8659, 14851, 25472,
43691 (36 in all, `hp/sigma_set.txt`), and the census relative to E_W extended to 8.5e14 (`census/kv85e13`,
`census_kv.c`) give C_eff <= 0.0433890641:

* sum_j c_j E = 0.00161 +/- 4.3e-6, with sum |c_j| ~ 5.3e3;
* the census term is 0.0003516 +/- 6.8e-8;
* 1,978 kernel cells.

The linear programme leaves the coefficient of the smallest abscissa at 0. `certify` drops abscissae with
c_j = 0 before its checks; they do not enter lambda. The witness is `witness_0.043124.json`, with margin
>= 3.12e-6. The replay passes in 50 minutes.

## 11b. A third D4 form: the field E_W' (Lemma 4', Proposition C')

This section replaces E_W by a field twice as large. It needs L-functions of degree 8, which are computed here
with new certified kernels and a C coefficient program (`certificates/dihedral/deg8/`, with its own README).

**The space W'.** Let W' = span(psi_10, psi_23, psi_19) (`plane3.py`). Its seven nonzero elements are:

* the D4 classes psi_10, psi_23, psi_24 = psi_10 + psi_23, psi_19 and psi_20 = psi_10 + psi_19, each of
  alternating rank 2;
* psi_19 + psi_23 and psi_19 + psi_24, which are not D4 classes and have alternating rank 4.

`vplane3.gp` verifies the five D4 fields as in Lemma 2. In the census basis psi_19 = 0x88 and psi_20 = 0x800
(`wmasks3.json`).

**Lemma 4'.** Let E_W' = E M_10 M_23 M_19, the fixed field of the preimage in D_2 G_B of the common kernel of W'.

(a) E_W' lies in every K. It is Galois over B, and Gal(E_W'/B) is a central extension of F_2^8 by Z' = F_2^3,
so [E_W':Q] = 4096.

(b) Its irreducible representations are:

* the 256 characters of Gal(E/B);
* for each of the five D4 classes o, the 64 two-dimensional rho_o (x) lambda_w;
* for o = 23 and 24, the 16 four-dimensional rho_19 (x) rho_o (x) lambda_w, with w over a complement of
  span(r1_19, r2_19, r1_o, r2_o).

Counting: 256 + 5 * 64 * 4 + 2 * 16 * 16 = 2048.

(c) zeta_{E_W'} = zeta_E * prod L(rho_o (x) lambda_w)^2 * prod L(rho_19 (x) rho_o (x) lambda_w)^4. Hence

    Y_W' = Y_E/8 + (1/2048) sum log L(degree 4) + (1/1024) sum log L(degree 8).

By Mackey's formula, L(s, rho_19 (x) rho_o (x) lambda_w) = zeta(F'_w)/zeta(F_L), where:

* F_L = B(sqrt c_19, sqrt c_o);
* F'_w = F_L(sqrt(gamma_19 gamma_o alpha^w)).

F_L and every F'_w are totally complex. So each of these functions has gamma factor Gamma_C(s)^4, root number 1,
conductor |d(F')|/|d(F_L)| (6.995e17 for 8 twists of each family, 1.791e20 for the other 8), and is entire, being a
Hecke L-function of a nontrivial quadratic character of F_L.

The 64 twists of orbit 19 have gamma factor Gamma_C(s)^2. For orbit 20, Bc is totally real and
r1(K_w) = 6 or 2 (32 each), which gives gamma factor Gamma_R(s)^3 Gamma_R(s+1) or Gamma_R(s) Gamma_R(s+1)^3.

*Proof.* The proof of Lemma 4 applies with W' in place of W.

* For a nonzero zeta in W', the commutator pairing composed with zeta is the polar form of zeta, of rank r(zeta).
  The irreducible representations with central character zeta therefore have dimension 2^(r/2), and there are
  256/2^r of them.
* For zeta = psi_19 + psi_o, rho_19 (x) rho_o has central character zeta and dimension 4, hence is irreducible;
  its twists by lambda_w give the 16 classes.
* Write rho_19 = Ind_{H_19} chi_19 and rho_o = Ind_{H_o} chi_o, where H is the fixed group of Bc and chi
  the character of K_{.,0}/Bc. Since H_19 != H_o, Mackey's formula gives
  rho_19 (x) rho_o = Ind_{H_19 cap H_o}(chi_19 chi_o), and H_19 cap H_o is the fixed group of F_L.
* The gamma factor of zeta(F')/zeta(F_L) is Gamma_R^(r1(F') - r1(F_L)) Gamma_C^(r2(F') - r2(F_L)); for orbit 20
  it is that of Lemma 4 (c) with the recorded r1(K_w). QED

**Residue degrees in E_W'.** Let P be an unramified prime of B.

* If P has nonzero vector v, its residue degree is 4 when phi_o(v) = rho_o for some of the five classes o, and 2
  otherwise.
* If P has vector 0, its residue degree is 1 when parity(b & m) = 0 for m = 0x888, 0x2888 and 0x88, and 2
  otherwise. Here b is the census pattern.
* For the 13 inert vector-0 primes, the residue degree is read from `inertv0_3.json`. Twelve are off ker W'; 2521
  is in it.

**Proposition C'** is Proposition C with E_W' in place of E_W (`dihedral_ceiling3.py`):

* the dyadic E_W'-term comes from the Euler factors at 2 of all 352 L-functions;
* above 3 and 5 the E_W'-terms equal the E-terms (asserted);
* the census credit counts the detected vector-0 primes with Frobenius in ker W'. These are the bins binsBW3 of
  `census_kv4.c`, which is `census_kv.c` with two more functionals, psi_19 and psi_17. Its ker-W bins are
  byte-identical to the stored `census_d3k.c` and `census_kw.c` outputs on (1.2e7, 1e13] and (1e13, 4e13].

Proposition E carries over word for word (`signed3.py W3`), with floors taken in E_W'.

**The 160 new L-values.** At the 36 abscissae of Section 11a they are computed as follows.

* Orbits 19 and 20 (conductors 1.7e8 .. 2.7e11):
  * `exportg.gp` gives the data with Euler factors to 3000;
  * `dcoef4.c` gives the coefficients to N <= 6.7e6 and the kernel moments;
  * `gkernel.py` gives the kernels: 'quartic' Gamma_C(s)^2; 'mixed31' and 'mixed13' for orbit 20;
  * `leval.py` gives the values. Relative radii are <= 6.4e-13.
* The degree-8 functions:
  * `export8.gp` gives the data with Euler factors at every p <= 2^18.
  * `octcoef.c` gives the coefficients for n <= N = 5.28e10 (AFE cut at x = 6144) and the moments. Per family it
    sieves 2.23e9 primes in (2^18, N]; 1.33e8 of them have a_q != 0, giving 4.6e8 terms m q. It finds 8e6 smooth
    n and no exceptional prime.
  * `leval.py` gives the values, with Rankin's tail bound from the Euler product of |a_n|. Relative radii are
    <= 5.1e-10.

The degree-8 data are checked in three ways:

* *The trace rule.* For p > 2^18 the rule a_P = 4 eps_19 eps_o lambda_w(P) (Frob_P central in both D4
  quotients) equals PARI's Euler factors at all 22,832 unramified primes in (1000, 2^18], for all 16 twists. These
  include 1395 central sides and 21 primes with both sides central.
* *The Euler product.* `octtest.py` compares the AFE at s = 19/10 (radius about 1e-14) with the absolutely
  convergent Euler product (radius about 3e-10). All 32 functions agree, the midpoints to 8e-16. A wrong conductor,
  gamma factor, root number or coefficient would show here.
* *Independent implementations.* The kernels reproduce PARI `lfun` values of quadratic Dirichlet products of all
  four gamma types. `dcoef4.c` + `leval.py` reproduce the reviewed `dafe.py` values: orbit 19 at 801/800, and
  4736 values of orbits 10, 23 and 24 at the 36 abscissae, where all balls overlap and the midpoints agree to
  3.4e-16.

**Result.** With the census relative to E_W' to 4e13 (`census/w4_1e13`, `census/w4_4e13`), `signed3.py W3`
gives the following. Its linear programme uses 21 of the 36 abscissae, with b = 17434576364/77978037883473 and
sum |c_j| ~ 3.9e3.

| quantity | value |
| --- | --- |
| kernel cells (x in [log q_min, 2e6]) | 1,976, all passing; tail dominance for x >= 2e6 |
| sum_j c_j E(sigma_j) | 0.000960 +/- 5.4e-7 (printed by Arb as 0.00096 +/- 1.02e-6) |
| census term sum tau(N) | 0.0001533 +/- 5.3e-8 |
| rest + TV | <= 0.0010477709 |
| C_eff = Z_sel(1) + rest + TV | <= 0.0427162549 |

For comparison, Proposition C' alone, at sigma = 1001/1000 with the census to 1e13, gives C_eff <= 0.0429298.

The witness is `certificates/dihedral/witness_0.043152.json`, with the profiles re-optimized at
delta = 0.043150 and C_eff = 0.0427163:

    M_*(theta_*) - 4e-9 >= 8.24e-6 > 0,  Fourier condition OK,  slope > 0.

At delta = 0.043153 the margin is -1.56e-5. The replay is `reproduce_w3.py` (Section 12).

**Review.** A fresh-context review of the steps above found no mathematical error. It reproduced:

* the representation theory and the Euler-factor identity of (c) at all primes 7 <= p <= 1000, at 2, 3 and 5,
  and at vector-0 primes;
* all 160 conductors;
* the trace rule against PARI at 500 primes in (2^18, 2^40];
* the census bins against an independent GP computation.

It found four formal gaps in the numerics, all fixed before the certification:

* t entered at 53-bit precision; leval.py now bounds |t_d/t - 1| in Arb;
* a ratio-monotonicity claim in one tail bound;
* float underflow of tail bounds;
* a weak assertion.

It also suggested a check that the census prefixes start at 1.2e7, now in `signed.py`. The assembly of the
1.043152 certificate (final data, `signed3.py certify`, witness) has not been reviewed separately.

## 11c. A fourth D4 form (E_W'') and general shell weights

**The space W''.** Let W'' = W' + span(psi_17) (`plane4.py`). Its 15 nonzero elements are:

* seven D4 classes, 10, 23, 24, 19, 20, 17 and 7 = 17 + 19, verified by `vplane4.gp`;
* eight forms of alternating rank 4. Each is a sum of two D4 classes, with the pairs (19,23), (19,24), (7,10),
  (17,10), (17,24), (7,24), (7,23) and (17,23).

`plane4.py` also checks that W'' is maximal for this method. Adding any of the 2^15 functionals outside W'' would
create an element of alternating rank >= 6, whose irreducible representations have dimension >= 8.

**Lemma 4''.** This is Lemma 4' with W'' in place of W'. The proof is the same.

* E_W'' = E M_10 M_23 M_19 M_17, and [E_W'':Q] = 8192.
* The irreducible representations are:
  * the 256 characters;
  * 7 * 64 two-dimensional ones;
  * 8 * 16 four-dimensional ones, rho_a (x) rho_b (x) lambda_w for the pairs above.

  Counting: 256 + 1792 + 2048 = 4096.
* The ceiling uses Y_W'' = Y_E/16 + (1/4096) sum log L(degree 4) + (1/2048) sum log L(degree 8).

The six new pairs have F_L totally complex: at each real place of B one of c_a, c_b is negative. So all 128
degree-8 functions have gamma factor Gamma_C(s)^4 and root number 1. The 128 twists of orbits 17 and 7 all have
gamma factor Gamma_C(s)^2.

* An unramified prime of nonzero vector v has residue degree 4 when phi_o(v) = rho_o for some of the seven
  classes, and 2 otherwise.
* A vector-0 prime has residue degree 1 when its census pattern has even parity against 0x888, 0x2888, 0x88 and
  0x8 (`wmasks4.json`).
* All 13 inert vector-0 primes, 2521 included, are off ker W'' (`inertv0_4.json`).

`dihedral_ceiling3.py W4` and `signed3.py W4` implement this. The census bins are the ker-W'' bins binsBW4 of
`census_kv4.c`.

**The new L-values.**

* *Orbits 17 and 7.* Conductors are at most 2.7e11. They are computed as in Section 11b, with relative radii
  <= 2.2e-13.
* *The six new degree-8 families.* The conductors are 2.8e18, 4.5e19 and 7.2e20, so N = 1.055e11. Euler factors
  come from PARI at every p <= 2^19.
  * Per family the trace rule equals PARI at all 43,222 unramified primes in (1000, 2^19], including 2674 to 2722
    central sides.
  * The sieve covers 4.34e9 primes q, of which 2.5e8 have a_q != 0, giving 4.3e8 to 6.0e8 terms m q.
  * No exceptional prime occurs.
  * Relative radii of the values are <= 5.1e-10.
  * `octtest.py` agrees with the Euler product at s = 19/10 for every family, the midpoints to <= 7.4e-16.
* *Run time.* `octcoef.c` now uses the census's binary Jacobi symbol and an extended-Euclid inverse. It reproduces
  the earlier moments byte for byte and takes about 35 minutes per family on this machine.

**Ceiling.** With the census relative to E_W'' to 4e13, `signed3.py W4` gives the following. Its linear programme
uses 21 of the 36 abscissae, with b = 8687735449/76582443134581 and sum |c_j| ~ 3.8e3.

| quantity | value |
| --- | --- |
| kernel cells | 1,976, all passing; tail dominance for x >= 2e6 |
| sum_j c_j E(sigma_j) | 0.000562 +/- 7.9e-7 (Arb display) |
| census term | 0.0000757 +/- 5.4e-8 |
| rest + TV | <= 0.0006078361 |
| C_eff | <= 0.0422763201 |

With the product shell profiles re-optimized at delta = 0.043170 (computed during the search; this is not part
of the certificate), the margin is >= 1.905e-5 at delta = 0.043170 and -4.78e-6 at 0.043171.

**General shell weights.** In the 0.04273 paper, Definition fw:shell-profile and Lemma fw:shell-lemma
(`sections/finite-windows.tex`) allow any finitely supported nonnegative weights w_ij with w_00 > 0, not only
products x_i x_j. The certificates had used only the product case (Corollary fw:product-weights). Here:

* `general_windows.py` evaluates the lemma's exact formulas: A' = sum m_i m_j w_ij^p and Z' = w^T G w with the
  shell Gram matrix G.
* The overlap Z' is checked against an independent expansion into products of balls.
* For a product matrix the routine reproduces `finite_windows.local_window` exactly.
* A brute-force model of the local field reproduces the formulas exactly (`general_windows_check.py`, 48 cases
  with random non-monotone, non-symmetric weights; 16 seconds).
* `margin_general.py` runs the unchanged `geom241.margin` with these windows at the places given as matrices.

With 10 x 10 weight matrices at 2, 3 and 5 (exact rationals, optimized at delta = 0.043171; 29 and 41 keep their
product lists), the margin rises by 1.532e-5. The witness `certificates/dihedral/witness_0.043171.json` has C_eff
= 0.0422764 and gives:

    M_*(theta_*) - 4e-9 >= 1.0538e-5 > 0,  Fourier condition OK,  slope > 0.

At delta = 0.043172 the margin is -1.33e-5. The Fourier condition depends only on the k's, which are unchanged.

The replay is `reproduce_w3.py witness_0.043171.json`. It passes in 1.9 to 2.4 hours. It:

* regenerates all exports;
* checks that the 617 pinned files cover all 353 files the certification reads;
* recomputes the L-values of the four new orbits and eight degree-8 families at three used abscissae;
* runs `plane4.py`, `general_windows_check.py`, `octtest.py` on every family and the census checks;
* recertifies C_eff and finds a margin >= 1.0538e-5.

**The next step, 0.043172, is out of reach with this toolbox.** With general weights and profiles optimized at
0.043172 the threshold is C <= 0.0422631. The following data are stored in the tree but used by no witness:

* the census relative to E_W'' extended to the 2^50 limit of `census_kv4.c` (prefixes `census/w4_15e13` to
  `census/w4_112e13`; the ker-W bins of each chunk equal the earlier census data where those exist);
* 35 further abscissae (`hp3/sigma_set3x.txt`, 71 in all; the extra Y_E files are in `hp/`);
* orbits 10, 23 and 24 through the new pipeline, with radii about 1e-13 (space `W4x` of `dihedral_ceiling3.py`).

The results:

* With the census to 8.5e14 and the 36 abscissae, `signed3.py W4 certify` gives C_eff <= 0.04226506.
* Adding the census to 2^50 and the 71 abscissae, the linear programme reaches C ~ 0.0422638. This includes the
  value of its radius floor.

This is about 7e-7 short of the threshold. What remains of C - Z_sel(1) is the undetected ker-W'' tail beyond the
census, which shrinks only like the logarithm of the census bound.

**Review.** A fresh-context review of W'' and of the general shell weights found no error affecting the bound. It
read the proofs of Proposition fw:transfer and Corollary fw:uniform-types line by line. They use only properties that
general weights have: unit invariance in each coordinate, the period, compact support, Z > 0 and finitely many
parameter values.

It also reproduced:

* the shell formulas with its own brute-force model (140 cases);
* the structure and maximality of W'';
* the Euler-factor identity of zeta_{E_W''} at all primes up to 1000 and at 2, 3, 5;
* the degree-8 Euler factors at 57 vector-0 primes;
* all degree-8 conductors, by a different route;
* PARI lfun values of orbits 17 and 7 inside the stored balls;
* the inert bits, by a different method;
* census bins by an independent recount;
* the certification and the margin.

Its minor points are fixed: a rounding direction in the margin above, `plane4.py` in the replay, the brute-force
script now in the tree, and two wordings. It did not recompute degree-8 L-values: PARI cannot reach these
conductors. They rest on the pipeline of Section 11b.

## 12. Reproduce

```sh
cd certificates/dihedral
python3 reproduce_w3.py witness_0.043171.json           # E_W'' and general shell weights (Section 11c); several hours (eight export8.gp runs)
python3 reproduce_w3.py witness_0.043152.json           # E_W' (Section 11b); --full reruns octcoef.c (about 1 CPU-hour per family), --full-lv all abscissae
python3 reproduce_dihedral.py witness_0.043124.json     # about 50 minutes (Proposition E, 36 abscissae, census to 8.5e14)
python3 reproduce_dihedral.py witness_0.043123.json     # about 40 minutes (Proposition E); --full-lv recomputes all long-AFE data
python3 reproduce_dihedral.py witness_0.043119.json     # about 10 minutes; --rerun recomputes the census (about 70 CPU-hours)
python3 reproduce_dihedral.py witness_0.043118.json     # census to 1.5e14
python3 reproduce_dihedral.py witness_0.043117.json     # census to 4e13
python3 reproduce_dihedral.py witness_0.043116.json     # census to 1e13 only
python3 reproduce_dihedral.py witness_0.043113.json     # sigma = 1101/1100, without Proposition D
cd ..
python3 reproduce_census.py witness_0.042965.json        # census to 10^12 over E (exponent 1.042965)
python3 reproduce_adaptive.py witness_0.042925.json      # adaptive dichotomy alone (exponent 1.042925)
```

Needs gcc with OpenMP, PARI/GP and the Python packages of `requirements.txt` (mpmath 1.3.0, python-flint 0.9.0,
numpy and scipy, pinned at the versions the replays were run with); `make venv` at the repository root installs them
into `.venv`. `reproduce_w3.py` also needs an x86-64 processor with AVX-512 IFMA, since it compiles and
compares `census_kv.c` and `census_kv4.c`; `reproduce_dihedral.py` skips that comparison without it.

## 13. Further room, and what is known about the limits

The certified exponent is the delta at which the margin changes sign. The
margin falls by 1 per unit of C and by about 23.8 per unit of delta, so
2.38e-5 in C equals 1e-6 in delta.

C bounds Z(1) = sum beta_q log(q/(q-1)). This is the Brauer-Siegel defect of
the family: an identity in the limit, not a bound. The selected primes'
types are forced, so Z(1) >= Z_sel(1) = 0.0416685 in every case.

Each ceiling below holds only under its stated assumptions, and the evidence
behind it differs.

| What is held fixed | Ceiling on delta | Evidence |
| --- | --- | --- |
| The toolbox of Sections 9-11a over E_W: real-sigma L-values, floor domination, the TV inequality, census to X | ~0.0431245 at X = 7e14; ~0.04313 at X = 1e20; 0.04318 would need X ~ e^1000 | LP duality, exact for that constraint set: the best kernel is the ramp (g_1 - b w)_+; tail from the Chebotarev density (0.03%) |
| The same toolbox over E_W' (Section 11b) and E_W'' (Section 11c) | 0.043152 certified at X = 4e13 (E_W'); 0.043170 at X = 4e13 (E_W''), 0.043171 with general shell weights. With the census to its 2^50 limit and 71 abscissae the estimate is just short of 0.043172 | the tail density of undetected vector-0 primes halves with each form; W'' is maximal for L-functions of degree <= 8 (`plane4.py`); the rest of C - Z_sel is the undetected ker-W'' tail beyond the census, which shrinks only like log of the census bound |
| This design (B = Q(sqrt 241), caps, local types) with the current geometric margin formula | 0.043196 (margin at C = Z_sel(1): +3.9e-4 at 0.04318, -8.8e-5 at 0.04320) | rigorous given the margin formula, since no valid C is below Z(1) >= Z_sel(1); assumes the profile optimizer is near-optimal |
| Other caps, local types or base fields | unknown; one more C4 cap ~+2.9e-4 | the Golod-Shafarevich function goes from -0.00211 to +0.00288 with a fourth cap: a limit of the present argument (and of its weighted generalization), not an impossibility |
| The geometric construction itself | about +9e-7 from convenience choices (general shell weights +6.5e-7, certain); the class-selection pigeonhole is open | audit 2026-10-04 (below) |

Earlier limits stated during this work were limits of one argument. For
example:

* "D is tight; several abscissae do not help" assumed positive coefficients,
  and Proposition E removes that assumption.
* "The census is the only lever, at 10x compute per decade" was an
  engineering estimate, and faster programs changed it.
* "The fourth cap is blocked" refers to the present Golod-Shafarevich
  argument only.

Where the remaining upside lies, largest first:

* **A sharper Golod-Shafarevich argument** admitting a fourth cap. The deficit
  is 0.00288.
  * *Weights do not help* (checked 2026-10-04). Give the generators unequal
    weights (Ershov's weighted Golod-Shafarevich theory) and generalize the
    block costs naturally. Then uniform weights are a strict local minimum.
    * Lowering the weights of a subspace W changes the function by
      delta (dim W - c(W)), where c(W) is the marginal cost of the local
      generators in W.
    * Over all 51,820 subspaces spanned by local vectors, min(dim W - c(W))
      is +0.311.
    * Two-level and random multi-level searches return to uniform weights.
  * *Index-2 subgroups do not help* (checked 2026-10-04). None of the 255 subgroups H = ker chi_c has a
    negative filtered-Fox GS function; the best value is +0.026 to +0.084. The local Hilbert pairings are
    nondegenerate, so the cup product with any character has rank >= 6, which gives d(H) = 7..9 while H inherits
    duplicated or halved local data.
  * *Further overlaps start in degree >= 6* (checked 2026-10-04). The block bound is exactly tight through degree
    5: the ideal generated by the initial forms of all relators has L_2..L_5 = 15, 26, 80, 192 with four caps, and
    no cap's quartic initial form lies in the ideal of the others. One overlap in degree 6 is worth at most
    t^6 ~ 6e-4, so at least six would be needed. L_6 (dimension 43,764) has not been computed.
  * The exactly known low Lie layers (L2 = 15, L3 = 26, |G/D4| = 2^49) bear on
    both.
* **More Galois information on the tail.** Each further D4 form treated through its L-functions halves the
  undetected ker-W density at all norms.
  * The third form (class 19) is done in Section 11b. It gained 6.7e-4 in C, +2.8e-5 in delta.
  * The fourth form, psi_17, is done in Section 11c. It gained 4.4e-4 in C, +1.8e-5 in delta (1.043170).
    General shell weights then add one more step (1.043171).
  * *This route ends at W''.* No fifth functional keeps every element at alternating rank <= 4. A further form
    would bring L-functions of degree >= 16 over Q, with conductors around 1e40, which is out of reach. After W''
    the undetected density is 1/16 of the vector-0 primes, and only the census reaches it.
* **The design search redone** with C estimated by the present toolbox
  instead of held fixed.
* **The geometric margin derivation (audit 2026-10-04).** Every step is tight except the class-selection
  pigeonhole.
  * The convenience choices together are worth about 2.1e-5 in M, or 9e-7 in delta. The main one is general
    shell weights in place of product weights: +1.55e-5 in M, certain, with optimal weights L-shaped in the
    corner. Bernstein degree, the real places and theta -> 1/2 are worth <= 2e-7 each. Asymmetric windows and
    profiles coupled across places give nothing.
  * The pigeonhole runs over Cl(K)/im Cl(F), but only classes generated by the selected primes occur. Since the
    Artin image of im Cl(F) lies in (1+iota) U^ab, the loss could be smaller by 2^(d_2 Cl_S'(K)/2), which is worth
    0.347 r in M with r = liminf d_2 Cl_S'(K_j)/[K_j:B]. That needs linear growth of 2-ranks along the tower,
    which is not known here: a lead, not a gain.
  * theta itself: doubling the involution class from 2^15 to 2^16 (theta >= 1/2 - 2^-18) would add about 2.4e-6
    to M, enough for delta = 0.043172 with the E_W'' ceiling C_eff <= 0.04226506 (margin about +4.3e-7). A
    group-theoretic argument for that class bound from the Muse run is kept, conditional and not independently
    reviewed, in [research/2026-10-muse-involution-class](../../research/2026-10-muse-involution-class/README.md).

## 14. What is used from earlier work

* 0.04273:
  * Sections tw (Definition tw:GB, Lemmas tw:GB-presentation,
    tw:quadratic-layer, Theorem tw:field-family);
  * an (Lemmas an:monotonicity, an:shift, an:local-contribution,
    an:census-degree, Propositions an:prime-budget, an:Ystar);
  * fw (Proposition fw:transfer, Lemma fw:shell-lemma);
  * the census conventions, lie241.py (R_2) and the genus-field value Y_E
    (afe241_301_300.json).
* 0.0418235 archive: the certified degree-four AFE kernels (nonpositive-afe.py).
* 0.042901: the 41-cap tower and family, `ceiling41.py`, the EF table of
  `geom41.py`, the optimizer `research/optimize41.py`.
