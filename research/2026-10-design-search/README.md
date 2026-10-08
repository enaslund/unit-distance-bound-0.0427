# Design search beyond 1.04273 (October 3–4, 2026)

**Status: negative result. No construction improving the exponent 1.04273
was found.** Everything below the line "Exact computations" is numerical
evidence from a floating-point design model, not a proof. The exact
computations (field enumerations, class groups, local conductors) were done
in PARI/GP 2.17.2 and are reproducible with the scripts here, but have not
been independently re-verified.

Later sections record what the search missed: the swap of the cap at 7 for
one cap above 41 (§8, exponent 1.042901,
[`papers/0.042901`](../../papers/0.042901/README.md)), and the lowering of the
analytic constant of that design (§9, exponent 1.043171,
[`papers/0.043171`](../../papers/0.043171/README.md)).

The search asked whether some change to the construction of the
[1.04273 paper](../../papers/0.04273/README.md) could raise the exponent
significantly (by ≥ 0.005). It extended the calibrated design model of
[`papers/0.04273/research/design-model`](../../papers/0.04273/research/design-model)
and searched all base fields of degree 2–4 with small root discriminant.
Every candidate scored at or below the existing Q(√241) design.

## 1. The model and its extensions

`model/fieldopt.py` generalizes the earlier quadratic-base optimizer to an
arbitrary base field B (degree m, signature, root discriminant, and the
splitting of each prime p ≤ 47). For each prime of B it chooses one local
option by a multiple-choice knapsack, subject to the Golod–Shafarevich
condition `P_B(t) = 1 − s_D + Σ_v β_v(t) < 0`, and it bisects for the
largest δ with a positive margin. The options, with their Golod–Shafarevich
cost `β` (each place's block minus its generator credit) and margin term, are:

| option | local group | absolute type | cost β(t) |
| --- | --- | --- | --- |
| `D` (dyadic, degree-one place) | D of order 32 | (8,4) | 2t − 1 + 1/((1+t)³(1+t²)²) |
| `R22` | C₂×C₂ tame | (2, 2f) | t − 1 + 1/(1+t)² |
| `R21` (**new**) | C₂ tame, Frobenius killed | (2, f) | t²/(1+t) |
| `R24` | C₂×C₄ tame | (2, 4f) | t − 1 + 1/((1+t)²(1+t²)) |
| `u1` (**new**) | unramified, Frobenius killed | (1, f) | t |
| `u2`, `u4` | unramified caps | (1, 2f), (1, 4f) | t²/(1+t), t⁴/((1+t)(1+t²)) |
| real place `keep` | C₂ | complex places of F | −t/(1+t) |
| real place `kill` (**new**) | trivial (ι_v killed) | split-real places of F | 0 |
| complex place of B | none | complex places of F | −t |

Split-real places of F (real places that split into two real places of K)
contribute `log 2 + J_S` per degree to the margin, against
`(1−δ)log 2 + (log π + J_C)/2` for complex places. Here J_S is the
Gaussian functional on R² for the hyperbola (±e^u, ±e^{−u}). This was
re-derived from the class-number formula (Herbrand quotient 2^{b_n−1},
Reg_K/Reg_F = 2^{c−1}I_N Reg¹ with Reg¹ over R^{c+b_s}). It agrees with the
earlier note's 2.81 against 1.93 per degree at δ ≈ 0.042.

`model/fieldopt2.py` adds totally complex (CM) bases. There ι is complex
conjugation of a subfield, the tower is required to be Galois over that
subfield, and all places of F are complex-type.

**Calibration (corrected).** With the splitting data of Q(√241) the model
returns δ = 0.0427. Its design is **not** the published one: it caps both
primes above 29 and **one prime above 41**, and drops the cap at 7. In the
same model, the published caps (7 and 29) give δ = 0.042549, and the 41 swap
gives δ = 0.042705, i.e. +0.00016. The model runs about 0.00018 below the
certificate (unweighted shells, fixed profile gain). That offset roughly
cancelled the gain, so the swap's model value looked like agreement with the
certified 0.04273. This is the improvement certified independently on the
branch `muse-spark-1.3` (exponent 1.042901, a GS-neutral swap of the 7 cap
for a single 41 cap). This search found it but did not recognize it; see §8.

The earlier design search had never offered `R21` (tame ramification with
trivial Frobenius), `u1` or killed real places to its optimizer over bases
of degree ≥ 2. Over Q(√241) the optimizer still does not choose them.

## 2. The bottleneck: Golod–Shafarevich budget

Giving the Q(√241) optimizer an extra x of free budget (subtracting x from
P_B) gives (`model/shadow.py`):

| extra budget x | 0 | 0.05 | 0.10 | 0.20 | 0.30 | 0.50 |
| --- | --- | --- | --- | --- | --- | --- |
| model δ | 0.0427 | 0.0471 | 0.0482 | 0.0586 | 0.0760 | ≥ 0.090 |

The extra budget buys u2 caps at 29, a killed second real place
(split-real), and totally split primes above 3. At the optimum, a unit of
budget is worth about 2 units of margin. Every source of new budget found
costs more than that: about 2.7 for a larger base, ≥ 2.9 for new tame
primes, ≥ 2.4 for larger dyadic groups. That is why no reallocation helps.

The analytic side is not the constraint. The Tsfasman–Vlăduţ inequality
leaves most of its budget unused (the selected primes use about 0.2 of
(ℓ − γ − log 4π)/2 ≈ 1.27), so it would allow residue degree 1 at 3 and 5
at the same root discriminant. Only the tower construction prevents that.

## 3. Hypothetical bases

Using generic splitting for primes ≥ 7 (`model/hypo*.py`), a base field of
degree m in which 2, 3, 5 split completely would give:

| base | rd(B) = 40 | 45 | 60 | 80 | 100 |
| --- | --- | --- | --- | --- | --- |
| totally real quartic | 0.0688 | | 0.0591 | 0.0532 | 0.0490 |
| totally real sextic | 0.0913 | | 0.0796 | 0.0723 | 0.0671 |
| sextic, 2 complex places | | 0.0752 | 0.0673 | 0.0604 | |
| octic, 2 complex places | | 0.0911 | 0.0824 | 0.0747 | |

The gains come from amortizing the constant term of P_B (the earlier note's
§4), which pays for killed real places (split-real places of F) and totally
split primes above 5. **No such fields exist at these root discriminants**
(next section).

## 4. Field searches (all with the full option set)

| family | range | best model δ |
| --- | --- | --- |
| real quadratic, 2 split (incl. 3 or 5 ramified) | D ≤ 4000 | **241: 0.0427**; 41: 0.0423; 1009: 0.0418 |
| imaginary quadratic, 2 split, ι from Q (**new**) | d ≤ 5000 | 31: 0.0419; 311: 0.0417; 71: 0.0410 |
| cubic, 2 split completely, both signatures | rd ≤ 45 (1362 fields) | disc −1759: 0.0420 |
| totally real quartic, 2 split completely | disc ≤ 10⁷ (1008 fields) | 0.0417 |
| quartic, signature (2,1), D4 | disc ≤ 10⁷ (1186 fields) | 0.0413 |
| quartic, signature (2,1), S4 | disc ≤ 10⁷ (7427 fields) | 0.0421 |
| complex cubic, 2,3,5 split completely | smallest: disc −271151, rd 64.7 | 0.0401 |
| totally real cubic, 2,3,5 split completely | smallest: conductor 643, rd 74.5 | 0.0408 |
| narrow Hilbert class fields of real quadratic fields (2 narrowly principal) | D ≤ 20000 | 0.0406 |
| subfields B(√W) of the Kummer field of the Q(√241) tower (GS over a subfield) | dim W ≤ 2 | P_{B'} ≥ +0.198, worse than P_B |

Further facts used above:

* No totally real quartic field with |disc| ≤ 10⁷ (rd ≤ 56.2) has 2, 3 and 5
  split completely. The enumeration with `nflist` covered all 169,301
  C4, V4, D4, A4 and S4 fields (`gp/nfl2.gp`).
* For real quadratic fields with 2, 3, 5 split, the S-class group (S = the
  primes above 2, 3, 5) is trivial for D < 98569. The first nontrivial one
  has order 2, so class groups add no generators at small rd (`gp/qscan3.gp`).
  The same holds for imaginary quadratic fields with d < 17111 (`gp/imq.gp`).
* Abelian fields of prime conductor in which 2, 3, 5 split completely have
  degree 3 below rd 200 (`gp/cycp.gp`).
* Over Q(√241), the smallest prime with Frobenius vector 0 in the Kummer
  group has norm 65809. The smallest with the vector of ι₂ has norm 9791,
  and the smallest with v^{[2]} in the relation span R₂ has norm 2179. So
  batching degree-one relations would need about 2.8 units of budget that
  do not exist (`model/batch.py`).

## 5. Exact computation: dyadic local groups

The Galois-fixed square classes of E₂ = Q₂(√−1, √2, √5) form a
5-dimensional space Φ, matching dim gr₂ of the maximal pro-2 Galois group
of Q₂ modulo D₃. Their quadratic extensions are exactly the class-2 dyadic
local fields. The conductor exponents of the 31 nonzero classes, computed
in the global field Q(i, √2, √5) at its unique dyadic prime
(`gp/e2c.gp`, `results/conductors.txt`), are 0 (once), 2 (twice), 4 (four
times), 6 (eight times) and 8 (sixteen times). For W ⊂ Φ,

    ord₂ 𝔇(E₂(√W)/Q₂) = 2 + Σ_{β ∈ W∖0} c(β) / (4·2^{dim W}).

The span of the classes with c = 0 and c = 2 gives 9/4, which is exactly
the field L₂ of the paper (its group D). The cheapest third gr₂ direction
raises the different to 2.625, the fourth to 3.0625, and the full class-2
field has 2 + 196/128 ≈ 3.53. With these exact values the model keeps D
(`model/dyadbig.py`). A further direction would pay off only if it cost
≤ 0.25 in the different. So **D is optimal among class-2 dyadic groups.**

## 6. Ideas examined and their status

* **Base fields with more real places or more split primes.** Their
  root discriminant outweighs the amortization. This holds for every
  family above, and for Odlyzko-type reasons quartics need rd ≳ 50.
* **CM or imaginary bases, with ι from a subfield.** This is valid, since
  the tower is Galois over the subfield when the conditions are invariant
  under conjugation. One generator is lost relative to a real quadratic
  base (−t against −2t/(1+t)). Best result 0.0419, for Q(√−31).
* **Weighted Golod–Shafarevich.** Giving the real-place generators weight
  ½ forces at least eight dyadic and tame local generators to weight ½,
  and the blocks get worse. No gain found.
* **Non-Galois subfields K^H of tower fields.** These have smaller rd when
  H contains inertia, but a family of them amounts to a Galois tower over
  an intermediate field, which is already covered by the subfield
  computation.
* **Odd-p towers.** Tame ramification needs N𝔮 ≡ 1 mod p with e = p, and
  ℓ exceeds 6.5 in every configuration tried.
* **S'-class groups in the selection lemma.** This is a provable but tiny
  refinement. The ideals 𝔄_j are supported on the selected primes, so the
  pigeonhole group is H_K Cl(F)/Cl(F) (H_K is the subgroup generated by
  the selected primes), of order κh_rel/h⁻_{S'}. For deep K in the tower,
  the 2-part of h⁻_{S'} is at least |U^{ab}/(1+ι)U^{ab}| with
  U = Gal(M/K), hence at least 2^{d(U)/2}. The margin gain is about
  (log 2/2)·(rank gradient of G_B), which is negligible because P_B(t₀) is
  only −0.002.
* **Small refinements of the existing certificate.** One is an adaptive
  treatment of the C-slack (≤ 0.007), using the fact that primes split in
  E_B either split in K (and can be selected) or have f ≥ 2. Another is a
  further optimization of the pair profile. Together these are worth
  about +0.0003 to +0.0005 in δ.

## 7. What a significant improvement would need

Per §2, about +0.05 of Golod–Shafarevich budget at the current root
discriminant would be worth +0.004 in δ, and +0.3 would be worth +0.03.
Every design route found (base, local groups, batching) is priced above the
value of that budget. A significant gain therefore seems to need a new
infinitude criterion for these towers, or a new source of generators at
small root discriminant. A different geometric count would not help: the
count is essentially forced (see the class-number and lattice discussion
in the paper).

## Reproduction

`model/` needs Python with numpy and scipy. It imports the existing design
model through `model/_paths.py`. `gp/` needs PARI/GP ≥ 2.15 (for
`nflist`). For example:

```sh
cd model
python3 shadow.py          # §2 table
python3 quadall.py 4000    # real quadratic bases
python3 imqall.py 5000     # imaginary quadratic bases
python3 dyadbig.py         # §5 with assumed and exact differents
gp -q < ../gp/e2c.gp       # §5 conductors
```

The listings `gp/nfl3.gp` and `gp/cub2.gp` produce the input files for
`evalfields.py` and `evalgen.py`. Their outputs for the quartic searches
are in `results/`.

## 8. Addendum: the improvement this search missed (October 4)

The branch `muse-spark-1.3`, now in master as `papers/0.042901`, certifies exponent 1.042901. It replaces the C4
cap at the inert prime 7 with a C4 cap at one of the two primes of Q(√241)
above 41, and re-optimizes the profiles at the new δ. Its finite replay
(`papers/0.042901/certificates/reproduce41.py`) passes on this
machine. The optimizer here chose the same swap in every Q(√241) run, but it
was not recognized, for three reasons:

* Each design was compared with the certified value instead of with the
  same model's value for the published design. The model's calibration
  offset (−0.00018) was about the size of the gain (+0.00016).
* δ was printed to four decimals, and the chosen caps were misread as the
  published ones.
* Improvements below about 0.005 were treated as out of scope, so even a
  correctly read +0.00016 would not have been pursued.

The earlier design model priced caps per rational prime (both primes above
41 at once, two caps), so the single 41 cap was outside its option space.
The per-prime-of-B model here had it.

**Lesson.** Compare candidate designs within one model, print enough
digits, diff the chosen design against the published one, and certify any
strict improvement before looking for larger ones.

### Follow-up local search after the miss

`model/localsearch.py` runs an exact enumeration at δ = 0.042901 in one
model, with weighted six-shell functionals. It covers every C₁/C₂/C₄/C₈ cap
pattern on primes of Q(√241) up to norm 97 (inert primes included), all tame
types at the four primes above 3 and 5, the dyadic variants D, DU8 and M16,
and keeping or killing the second real place.

* The 41 swap is the unique optimum (model margin −0.00010).
* No fourth C₄ cap fits at any t.
* The next best design is −0.020 lower (order-8 dyadic Frobenius with four
  caps), roughly −0.0009 in δ.

With weighted shells the model gives δ = 0.042897 for the swap, against the
certified 0.042901, so the model is calibrated to about 10⁻⁵. In the same
model Q(√41) gives 0.042413.

An independent fresh-context review of the swap found no error that
invalidates the exponent. Its remaining items are write-up gaps:

* cite Prop fw:transfer, not Cor fw:uniform-types;
* enter the Kummer basis explicitly in kummer41.gp;
* harden the replay hashes;
* fix a δ-mislabelled table in cap-search.md.

## 9. Superseded on the analytic side (2026-10-04/05)

The design search above treats the analytic ceiling C as fixed. That was the
wrong place to stop. The constant can be lowered substantially without
touching the design (the tower, the caps and the local types).
Exponent **1.043171** is certified (research result, finite replay passes) in
[`papers/0.043171/`](../../papers/0.043171/README.md), which builds on the
41-cap variation of §8. Ten independent reviews of its parts found one
material error, which is fixed; the exponent did not change. It uses these
mechanisms:

* D4 quotients of the tower group detect residue degree >= 2 for the primes
  that split completely in the Kummer field, via a census to 10^13.
* The ceiling is taken over E_W = E M_10 M_23, of degree 2048, with 192
  certified degree-4 Hecke L-values (abscissa 1101/1100 at first, 801/800 in
  the final step).
* An adaptive dichotomy (shell profiles at a prime with small residue degree,
  a smaller Euler factor otherwise) handles the residue degrees that stay
  unknown.
* A refined Tsfasman-Vladut step (Proposition D there) bounds Z(1) with the
  selected primes treated exactly. It uses a kernel inequality
  g_1 <= a g_sigma + b w, valid for all q >= 2, at sigma = 801/800. This
  bound is tight for its two constraints: the worst case is a point mass at
  log q ~ 280.
* The census relative to E_W is extended to 8.5e14 with faster programs
  (`census_kw.c`, and `census_kv.c` with AVX-512 IFMA).
* Proposition E replaces the single kernel by a signed combination over 24
  abscissae, with the same per-prime floor domination. It is within about
  1.3e-5 in C of the best possible kernel for that toolbox. Twelve more
  abscissae and the census to 8.5e14 give 1.043124.
* A third D4 form psi_19 doubles the comparison field: E_W' = E M_10 M_23 M_19,
  of degree 4096. zeta_{E_W'} needs 128 more dihedral L-functions and 32 of
  degree 8 over Q (conductors to 1.8e20). These are computed with new
  certified kernels and a C sieve (`certificates/dihedral/deg8/`). This gives
  1.043152.
* A fourth form psi_17 gives E_W'', of degree 8192, whose zeta function has
  128 degree-8 L-functions among its factors (conductors to 7.2e20). With the
  census relative to E_W'' to 4e13 this gives 1.043170. W'' is maximal among
  spaces whose L-functions have degree <= 8.
* General shell weights at 2, 3 and 5, which the shell lemma of the 0.04273
  paper allows but no earlier certificate used, add 1.5e-5 to the margin.
  This gives 1.043171.

These mechanisms lower C from 0.04871285 to 0.0422764, which is +0.000270 in
delta on top of 1.042901. The next step, delta = 0.043172, needs
C <= 0.0422631. With the census relative to E_W'' at the 2^50 limit of
`census_kv4.c` and 71 abscissae, the linear programme reaches only about
0.0422638. What remains of C - Z_sel(1), where Z_sel(1) = 0.0416685, is the
tail of undetected primes beyond the census. It shrinks only like the
logarithm of the census bound. Since C >= Z_sel(1), this route ends at
delta = 0.043196 for this design (Section 13 of that README).
