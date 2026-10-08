# C93 check: R5 quotient repair (Sec 1 + lifting defect verified; mildness conditional; mu16 refuted)

Lane C93, 2026-10-06. Source note (reviewed):
`research/2026-10-muse-involution-class/notes/reviewed/R5-quotient-repair.md` (sections 1-5).
Requested focus (general; coordinator: arbitrary detection depth,
centralizer-lifting defect, commutator set versus generated subgroup,
exact-index/cofinal field transfer; exact-R4 sufficiency and the
210-coordinate requirement including real/dyadic gauges and local-to-global
embeddings; mildness hypotheses versus one presentation; Schmidt/cyclotomic
scope; ranks 7/18 and reduction-code repair).
Check code: `research/2026-10-muse-involution-class/code/C93/c93_quotient_repair_check.py`
(stdlib-only, exit 0).
Reran `research/2026-10-muse-involution-class/code/R5/liftdefect.py` (exit 0) and
`research/2026-10-muse-involution-class/code/R5/bracket45.py` (exit 0, 56/56) with
`/tmp/C62-venv/bin/python`.

Verdict: section 1 (quotient repair) VERIFIED with one notation fix
(commutator set, not generated subgroup); the general-depth lemma, central
inequality, and single-commutator equivalence are proved below. Section 2
(mildness) has its computations VERIFIED (rank 140, cubics add 2,
a5 = -68) but the exclusion is CONDITIONAL and incomplete: Labute's HS
formula has no source in repo/archive (as the note flags) and minimality /
presentation-invariance is not proved (only part is computed). Section 3
(Schmidt) assessments are kept as assessments; the order>=32 reformulation
is PROVED, the GB^ab = F2^8 premise is REJECTED (unproved, likely false;
repaired to no cyclotomic Z2), and the side lemma mu16 in BG is REFUTED
(N = 3,5 not 9,25; phi^2 nontrivial on mu16). Section 4 (lifting defect):
the exact-R4 sufficiency lemma is PROVED, D3/D2 reductions and ranks
(18/18, ker 7) VERIFIED as compatible preliminaries, the 210-coordinate
count is CONDITIONAL (real/dyadic gauge steps unproved), and feasibility /
impossibility-from-recorded-data are assessments, not theorems. Section 5
(reduction-code repair) VERIFIED.

No previously accepted corpus result is overturned (C62, C16, C86 stand as
cited; C86 Lemmas A-D overlap section 1 and agree).

## 1. Quotient repair (proved, with set/subgroup fix)

Let GB be the 41-cap tower group, pi: GB -> Gbar = GB/D4 the retained
quotient. Filtration facts used: [Dm,Dn] subset D{m+n}, g^2 in D{2n} for
g in Dn (tower.tex lines 33-36), Dn open (GB finitely generated), meet
Dn = 1 (pro-2), surjections map Dn onto Dn. |Gbar| = 2^49,
|C_Gbar(ibar1)| = 2^34. Commutator [g,h] = g^-1 h^-1 g h (tower.tex
line 28).

### 1a. General-depth lemma (proved)

Claim (note Sec 1(a)). If x = [g,iota1] in Dk \ D{k+1} for some k >= 5
(g in D4), then for any hyperplane V with D{k+1} subset V subset Dk,
[Dk:V] = 2 missing x: V is open normal, J = D4/V is a finite 2-group on
which iota1 acts nontrivially, |C_J| <= |J|/2, and Q = GB/V has
|cl_Q(iota1)| >= 2^16 with |Q| = 2^{Sk+1}, Sk = 49+g4+...+g{k-1}.
The k = 5 case has |Q| = 2^{50+g4} under hypothesis
[D4,iota1] not subset D6.

Checked proof. Dk/D{k+1} is central in GB/D{k+1} since [Dk,D1] subset
D{k+1}, so every V between is normal; open since D{k+1} open. x mod
D{k+1} nonzero in the F2-space Dk/D{k+1}, so a hyperplane missing it
exists. Write [g,iota1] = g^-1 g^{iota1}; x not in V gives
g^{iota1} != g mod V, so nontrivial action on J. J = D4/V finite
(D4, V open). C_J proper in a 2-group has index >= 2 (Lagrange).
|Dk/V| = 2 (hyperplane), |D4/V| = |D4/Dk|*2 with
|D4/Dk| = 2^{g4+...+g{k-1}}, so |Q| = 2^49*|J| = 2^{Sk+1}. Count:
|C_Q| = |pi(C_Q)|*|C_J| <= 2^34*|J|/2 (kernel C_Q cap J = C_J),
|cl_Q| = |Q|/|C_Q| >= 2^16. This agrees with C86 Lemma B (exact depth 5
is C86 Lemma A under [D4,iota1] not subset D6).

### 1b. Central inequality (proved)

Claim (note Sec 1(b)). For V open normal with D5 subset V subset D4,
|C_Q(iota1)| = |pi(C_Q)|*|J| <= 2^34*|J|, hence |cl_Q| >= 2^15, with
equality iff pi(C_Q) = C_Gbar.

Checked proof. [D4,D1] subset D5 subset V, so J = D4/V central in
Q = GB/V; iota1 acts trivially, C_J = J, kernel = J. So
|C_Q| = |pi(C_Q)|*|J|, pi(C_Q) subset C_Gbar gives the bound.
Equality iff full centralizer lifting. Strict > is the lifting-defect
case (Sec 4). This agrees with C86 Lemma C. Existence of such V needs
g4 > 0 (C16 leaves g4 in [0,81]); the statement is conditional on V.

### 1c. Single-commutator equivalence (proved with fix)

The note states cl_H(phi(iota1)) = phi(cl_GB(iota1)) for every quotient
H = phi(GB), hence N_iota >= 2^16 for some tower H iff
|cl_GB(iota1)| >= 2^16 iff [GB,iota1] cap D4 contains x != 1.

The class-image equality is proved: H = phi(GB) surjective, so
{h phi(iota1) h^-1} = {phi(g iota1 g^-1)} as sets.

Repaired equivalence (proved). Write Cset = {[s,iota1] : s in GB} for
the SET of commutators (not the generated subgroup). Then:

(i) N_iota >= 2^16 for some tower H iff |cl_GB(iota1)| >= 2^16.
(ii) |cl_GB(iota1)| >= 2^16 iff Cset cap D4 contains x != 1.

Proof of (i). => : cl_H = phi(cl_GB), so |cl_GB| >= |cl_H| >= 2^16.
<= : separate 2^16 distinct conjugates by an open normal U (meet of
opens = 1; finitely many differences missed by some Dn, n >= 4 already
in D4, or intersect with D4). Then H = GB/U has >= 2^16 distinct
conjugates of phi(iota1); U subset D4 preserves Gbar, local structure
(U subset D3), separation, b >= 1, rd. The full field-family conclusion
for every 2-power m >= |Q| is C86 Lemma D (exact-index via center
series); existence of some H needs no index adjust.

Proof of (ii). => : 2^16 distinct conjugates in GB map to 2^15 classes
in Gbar, so two share an image: for g = gj^-1 gi,
g iota1 g^-1 = iota1 d with d in D4, d != 1, and
d = iota1^-1 g iota1 g^-1 in Cset (up to inversion/convention).
<= : if [s,iota1] in D4 \ {1}, then pi(s) in C_Gbar automatically
([s,iota1] in D4 iff pi(s) centralizes ibar1). Fix such s. Choose
gi, i = 1..2^15 lifting Gbar/C_Gbar representatives, so
pi(gi iota1 gi^-1) distinct. Then gi iota1 gi^-1 and
(gi s) iota1 (gi s)^-1 = gi (iota1 x) gi^-1 share the same Gbar image
but differ (x != 1 conjugated nonzero), giving 2*2^15 distinct
conjugates in GB.

Notation fix (commutator set versus subgroup). As written with
[GB,iota1] in subgroup notation (<[s,iota1]>), the <= direction of (ii)
is NOT proved: a product of commutators in D4 need not give a single
commutator in D4, and the doubling argument needs a single [s,iota1].
The note's eligible witnesses are both single commutators (depth-k
D4-witness [g,iota1] in Dk \ D{k+1}, g in D4; lifting defect
[s,iota1] in D4 \ 1, s centralizing mod D4), so the set reading is
intended and proved. Do not cite the subgroup reading.

Eligible witnesses preserved: depth-k D4-witness (Sec 1a) or lifting
defect (Sec 4). Both are instances of Cset cap D4 != {1}; they differ
in where V sits (below D5 for depth >= 5 with nontrivial action, versus
between D5 and D4 with trivial action but incomplete lifting).

## 2. Mildness counting (computations verified; exclusion conditional)

### 2a. Relation count (computed; verified)

Reran liftdefect.py (iv): R3 spanning rows 170, rank 142; rank
[R2,L1] = 140, cubics add 2. So the 2 dyadic cubics are independent of
[R2,L1] mod degree 3. The (iii) involved set (21 names, no "cubic")
confirms cubics in no syzygy, consistent. This matches C86's independent
R3 142 / 28 syzygies.

### 2b. Series arithmetic (computed; verified)

With 8 generators, 21 quadrics (degree 2), 2 cubics (degree 3),
7 quartics (degree 4: 4 dyadic + 3 cap), P(t) = 1-8t+21t^2+2t^3+7t^4.
c93_quotient_repair_check.py (exact integers) confirms
1/P = 1+8t+43t^2+174t^3+466t^4-68t^5+... (a0..a5 = 1,8,43,174,466,-68).
Threshold: with q quartics, a5 = 44-16q, so a5 < 0 iff q >= 3. Hence
3 exact-degree-4 quartics already force negativity; all 7 not needed
for the sign. C16's cap independence (I4 960 -> 963, 3 added) gives
3 quartics of exact degree 4 at initial level.

Uncapped remark verified: 1/(1-8t+7t^2) has closed form
a_n = (7^{n+1}-1)/6 > 0 for all n (roots 7,1), so series-consistent
(no obstruction). This does not prove mildness, only no counting
obstruction.

### 2c. Mildness exclusion (conditional, incomplete; not extracted as proved)

The note concludes GB NOT mild, subject to sourcing Labute's HS formula
(HS = 1/P forcing a5 = dim >= 0). Searched repo and references for
Labute/mild/Anick: no source (only this note and STATE.md mention it).
So the Labute step is correctly flagged and stays conditional.

Additional gap (minimality / one presentation versus group). Negativity
for ONE presentation's P(t) rules out mildness of the GROUP only with
minimality/invariance: a non-minimal presentation can be non-mild while
the group admits another mild presentation. The note computes only part
of minimality (21 quadrics independent via R2 21; 2 cubics independent
via (iv)). It does not prove quartic minimality as normal generators nor
that minimal-presentation degrees are forced (any other minimal P' would
still force negativity). The 3-cap initial independence (C16) is at
initial level, not a normal-generation minimality theorem. So even with
Labute sourced, the exclusion needs a minimality lemma not supplied.

Keep as: IF Labute's criterion applies as stated AND the 21+2+(>=3)
relations are part of every minimal presentation's degree count (or the
capped presentation is minimal in the required sense), THEN P(t) with
a5 < 0 rules out mildness. The "No Anick computation needed;
initials-only exactness is dead" consequence is conditional on the same
(Anick/strongly-free route to I = R would be blocked if not mild; I = R
by other means is not ruled out).

## 3. Schmidt assessment (assessments kept; one lemma proved; mu16 refuted)

Read references/schmidt_2002_two_and_infinity_arXiv-math0008246.pdf via
pdftotext (Theorems 1, 2, 2', Lemma 3.1, Sec 3-4).

### 3a. Theorem 1 (cd <= 2): no route identified (assessment)

Schmidt Thm 1: cd GS(2) <= 2 for S cap SR = empty (S containing 2).
Cohomological dimension does not see centers in general (e.g. Z2 has
cd 1 with full center), so full centralizer lifting
C(iota1) = pi^-1(C_Gbar) yields no cd-contradiction without a stronger
center theorem not in hand. Kept as the note states it: no cd-route to
Cset cap D4 != {1} identified. This is a report of no route, not a proved
impossibility.

### 3b. Theorem 2' (free product): assessment + proved order reformulation

Schmidt Thm 2': for K p-S-closed, G(KT(p)|K) is the free pro-p product
of inertia groups T(Kp(p)|Kp). At real places T = C2, so the real part
is a free pro-2 product of C2's (C2 * C2 for two places). This describes
the UNCAPPED kernel; caps cut it via N cap (C2*C2), carrying the
t-dependence (TRUE-section positions). Kept as assessment (maximal-S
applicability alone insufficient for capped GB).

Proved reformulation (preserved). If ord(iota1 iota2) >= 32 in GB, then
a D4-witness exists (hence N_iota >= 2^16 via Sec 1a). Proof: let
d = iota1 iota2 in D1; d^2 in D2, d^4 in D4 (D2^2 subset D4 since
(g-1)^2 = g^2-1 in char 2), d^8 in D8, d^16 in D16 subset D5; ord >= 32
gives d^16 != 1. Dihedral action iota1 d iota1 = d^-1 gives
[d^-8,iota1] = d^16 with d^-8 in D8 subset D4, so x = d^16 in
D16 \ {1} subset D5 \ {1} is a depth-k >= 5 single-commutator witness.
Proving ord >= 32 needs positions (t-blocked): assessment, not proved
impossible from recorded data.

### 3c. Lemma 3.1 (involution-generated): inapplicable via cyclotomic route (assessment; premise repaired)

Schmidt Lemma 3.1: G,G' pro-2 generated by involutions with
H^2(-,Q2/Z2) = 0 on both sides; phi isomorphism iff H^1/H^2
isomorphisms. Schmidt's proof of the H^2 vanishing uses the cyclotomic
Z2-extension plus weak Leopoldt ([9] (10.3.22)/(10.3.25)).

The note's premise "GB^ab = F2^8 finite" is REJECTED as stated:
unproved in note/repo, and "= F2^8" (elementary abelian) is likely false
(Frob_t has order exactly 4 in GB per tw:retained-quotient(b), so
GB^ab may have C4 factors). Finiteness alone (r = 0) is plausible but
also not proved in the note.

Repaired premise (proved). No cyclotomic Z2 inside BG (fixed field of N
with Gal(BG/B) = GB): the cyclotomic Z2-extension has infinite
decomposition at 2, while GB's decomposition at p1,p2 is finite (D of
order 32, tw:GB-basic(a) + tw:retained-quotient(b) that the quotient is
exactly D). Hence BG does not contain the cyclotomic Z2, so Schmidt's
weak-Leopoldt-via-cyclotomic proof of H^2 = 0 is unavailable for GB.
Kept as inapplicability of that route (hypotheses unverifiable by that
method), not as proved H^2 != 0.

### 3d. Cyclotomic side lemma (mu16 in BG REFUTED; mu32 out holds)

The note claims mu16 subset BG but mu32 not subset BG, with N acting
trivially on mu16 and Frob29^4 nontrivial on mu32, then a C2xC4
quotient factoring through GB/D3.

mu16 subset BG is REFUTED. Norms from tower.tex tw:base(c): q1,q2 above
3 and r1,r2 above 5 are degree one, so Nq = 3, Nr = 5 (completions Q3,
Q5), NOT 9,25 as the note states. B(mu16)/B unramified outside 2;
Frobenius at q,r acts as mu -> mu^{N}. The normal generator is phi^2
(D2(G_nu)), acting as mu -> mu^{N^2}: 3^2 = 9, 5^2 = 25 = 9 mod 16,
both != 1 mod 16, so phi^2 acts nontrivially (order 2: 9^2 = 81 = 1
mod 16). Hence N does not fix mu16; mu16 not subset BG. The note's
"Frob^2 = mu^81 = mu" checks the FOURTH power (81 = 9^2), not the
square generating N. What holds is mu8 subset BG at q,r level
(9 = 1 mod 8). Whether ker(Gpj->D) fixes L2 containing mu16 was not
verified and is moot given q,r.

mu32 not subset BG HOLDS, both a fortiori (mu16 not subset BG implies
mu32 not subset BG) and by the note's Frob29 computation, verified:
N = 29 at t1,t2 (degree one), 29 = 13 mod 32 up to the note's
representative, 13^2 = 169 = 9 mod 32, 9^2 = 81 = 17 mod 32, so
Frob^4 acts as mu -> mu^17 != mu on mu32 (17 != 1 mod 32).
c93_quotient_repair_check.py confirms 13^4 = 28561 = 17 mod 32 and
29^4 = 1 mod 16 (caps fix mu16) with 41 = 9 mod 16 (P41[1] Frob^4
fixes mu16). So caps are compatible with mu16 but q,r already exclude
it.

"C2xC4 factors through GB/D3 (D3 = 1)" is REJECTED as garbled:
Gal(B(mu16)/B) = C2xC4 does not factor through GB since mu16 not subset
BG; "D3 = 1" is unexplained (D3(GB) != 1; gr3 is 26-dim); abelian
quotients trivially have class size 1, so no growth, but that is not a
route needing D3. Preserved triviality: any abelian (cyclotomic)
quotient has class 1 and cannot give N_iota >= 2^16.

## 4. Lifting-defect path (reduction proved; preliminaries computed; 210 conditional)

### 4a. Lifting-defect lemma (proved; no R5 needed)

Claim (note Sec 4). Given exact R4 and s in GB with [s,iota1] in
D4 \ D5, let V with D5 subset V subset D4, [D4:V] = 2, V/D5 missing
[s,iota1]_4. Then Q = GB/V has order 2^50 with |cl_Q(iota1)| >= 2^16.

Checked proof. [s,iota1] in D4 gives pi(s) in C_Gbar. V/D5 hyperplane
missing the nonzero class in gr4 = D4/D5 exists; V normal (D4/D5
central) and open. |Q| = 2^49*2 = 2^50. J = D4/V order 2 central,
iota1 trivial on J, so |C_Q| = |pi(C_Q)|*2. sbar not in C_Q
([s,iota1] not in V), and no J-translate centralizes (J central,
trivial action), so pi(s) in C_Gbar \ pi(C_Q); pi(C_Q) proper in a
2-group gives |pi(C_Q)| <= 2^33. Hence |C_Q| <= 2^34,
|cl_Q| >= 2^50/2^34 = 2^16. Only R4 (to certify [s,iota1] not in D5
and pick V) is needed; R5 not needed. Strictly cheaper than D5-cutting
(Sec 1a needs depth >= 5 data).

### 4b. D3 sources (reduction proved; rank 18 compatible)

Reduction (proved). s in D3 has [s,iota1] in D4 with
[s,iota1]_4 = [sbar3,ibar1] in gr4 exactly (Lie bracket induced by
commutators, tower.tex lines 37-40). Lift-independence mod D5:
varying s by D4 gives [D4,D1] subset D5; varying iota1 lift by D2
gives [D3,D2] subset D5. So D3-defect exists iff ad3 = [.,ibar1]:
gr3 -> gr4 nonzero. gr3 exact (L3/R3, 26-dim); target needs exact R4.

Preliminary (computed; verified). Reran liftdefect.py (ii): [L3,c] mod
I4 (41-cap I4, assert rank 963, L4 1044) has rank 18 for c1 AND c2.
Logic one direction only: I4 subset R4, so rank 0 mod I4 would have
proved ad3 = 0; rank 18 is COMPATIBLE (not robustly zero) but proves
nothing (all 18 dims could die in R4 \ I4). R4 decides. Note [R3,c]
subset I4, so the map factors through L3/R3 = gr3; rank mod I4 is an
upper bound on true rank mod R4. Relies on the note's tensor code
(shared machinery with C3/bracket45, which reproduce I4 963 / I5 6353);
no third independent implementation of the 18 was written.

### 4c. D2 sources (automatic D4 proved; Magnus sketch unresolved)

Automatic D4 (proved). u2 in D2, iota1 in D1: [u2,iota1] in D3 with
([u2,iota1])_3 = [ubar,ibar1] in gr3 by definition of the bracket.
Hence ubar in ker(ad2: gr2 -> gr3) gives [u2,iota1] in D4
automatically. Lift-independence: varying iota1 lift by D2 gives
[D2,D2] subset D4, so degree 3 unaffected. Reran liftdefect.py (i):
gr2 basis 15, ad2 rank 8, ker dim 7 (matches C86-audited (7,8)).

Degree-4 part (sketch; unresolved). "[u2,iota]^4 via mechanical Magnus +
(iota)_2-fiber (robust test mod R4+[ubar,R2])" is a plan, not a proved
lemma in the note (no explicit Magnus formula supplied). The robust-test
idea is plausible (varying (iota)_2 by R2 shifts the answer by
[ubar,R2], so non-vanishing mod R4+[ubar,R2] survives any fiber), but
correctness needs the formula. Not extracted as proved.

### 4d. R4 needs (partially proved; 210 conditional)

Fiber arithmetic (proved). Free L2 on 8 gens 36-dim, R2 21-dim, so each
TRUE lift ghat mod D3 has 15-dim fiber mod R2 (36-21). Tame tau/phi x8
gives 120, dyadic x/y/z x6 gives 90, total 210 for those 14 lifts.
All 21 rho_i occur in the 28 syzygies (computed (iii); verified: rerun
lists all 21 Qnames, no "cubic"), so no quadratic initial can be dropped
from syzygy corrections at initial level.

Frob positions irrelevant (proved). Quartic initials exact from gr1:
(rho^2)_4 = r^[2] and (Fhat^4)_4 = S(v)^[2] see no degree-2/3 lift data
([D2,D3] subset D5, (D2)^4 subset D8; if a = bc with c in D3 then
a^2 = b^2 mod D5). So Frob degree-2 data does not enter R4. This matches
R5-bracket45 Sec 2.

Real positions = 0 (UNPROVED). "Gv = C2, D2 = 1, so TRUE (iota)_2 in R2,
harmless fiber" does not follow: D2(C2) = 1 holds (I^2 = 0 in F2[C2]),
but no argument is given that the TRUE degree-2 lift component lies in
R2 (global relation space) rather than an arbitrary 15-dim fiber. Since
c1^2,c2^2 DO occur in syzygies (involved set), their degree-3 parts
matter for R4 unless the fiber is pinned. Kept as conjecture/plan, not
proved. Without it, add back 2x15 = 30 dims.

Demuskin ebar folding (UNPROVED). "ebar folds into dyadic positions (no
independent ebar)" has no argument in the note. R5-bracket45 Sec 2 keeps
an 8-dim local invariant ebar in L3(F3) for rho_p2's degree-3 part [S6:
C89 landed — the 8-dim description is refuted, reframed to 27 formal
dims; see C89 Sec 2c]
(tw:relators/tw:local-two give existence + initial only, no explicit
word). That it lies in the span of position contributions is not shown.
Kept as unresolved; without it, add back up to 8 dims.

No-minimization implication (assessment). All 21 rho_i occurring shows
every initial matters, but "no minimization" of LIFTS needs each lift's
fiber to affect some occurring correction, not computed. Kept as
assessment.

Hence the 210-dim "R4 needs (proved)" is CONDITIONAL: 210 = 120+90 holds
IF real fibers are pinned in R2 AND ebar contributes nothing independent
AND Frob irrelevance (proved) is the only drop from 240+8. The safe
proved count remains 240+8 = 248 (R5-bracket45 Sec 2) minus Frob (already
excluded there), i.e. 240 presentation + 8 local, with real/ebar drops
unproved.

### 4e. Feasibility and conditional chain (assessed / conditional)

Feasibility "FEASIBLE but FRESH (explicit local fields/uniformizers/
D3-quotients, PARI-assisted norms)" is assessed, not computed; no local
computation is attempted in the note. "Reconstruction from RECORDED data
IMPOSSIBLE (positions unconstrained: R2/R3 lift-independent)" is kept as
an assessed obstruction (recorded R2/R3 use initials only, so give zero
constraints on fibers, per R5-bracket45 Sec 2), NOT a proved impossibility
theorem (no for-all-positions compatibility construction). Same scoping
as C86 Sec 4.

Conditional chain preserved (conditional): positions -> exact R4 ->
s (ad3 nonzero or D2-robust) -> V -> Q (2^50) -> K (m >= 2^50) ->
N_iota >= 2^16 -> theta* = 1/2-2^-18 -> M > 0 middle+estimated at
delta = 0.043172 with Gaussian profiles (threshold table per C86,
conditional on stated C-inputs). Profile grids parked.

## 5. Code repair disclosures (verified)

reduce_mod latent bug: the early-return version (return at first
non-pivot lead) leaves smaller pivot bits, giving non-canonical residues
but SOUND zero-tests. Soundness: for echelon basis with distinct leads,
any nonzero span element has lead in pivots, so lead-not-in-pivots
implies outside span; returning 0 implies in span. Hence:

- bracket45.py uses reduce_mod only as `!= 0` to extend the basis with u
  itself, plus rank_basis for ranks: unaffected. Reran: free L4 1044,
  I4 963 -> L4/I4 81, quotient basis 81, I5 6353, bracket ranks 56/56,
  DONE. Confirms 56/56.
- liftdefect.py fixed to full reduction (pop lead, fold basis-minus-lead,
  keep non-pivots); (i) now gr2 15, ad2 rank 8, ker 7, matching the
  C86-audited (7,8). Reran: (iii/iv) 170 rows rank 142, [R2,L1] 140
  (cubics add 2), 28 syzygies with 21 rho_i, (ii) 18/18, DONE.
- C3's c3_gs_higher_degree_check.py shares the early-return pattern
  (lines 165-173) but uses it only in `!= 0` asserts (lines 185,188,189,
  260,263,302): sound, no repair needed for its verdicts.

## 6. What was checked (inputs and versions)

- Read the note at `research/2026-10-muse-involution-class/notes/ready/R5-quotient-repair.md`
  (pre-review location), reviewed `R5-signature-threshold.md` + C86 review
  (`corpus/C86-r5-signature-threshold-check.md`), ready `R5-bracket45.md`,
  C16 (`corpus/C16-lie45-upper-bounds.md`), tower.tex filtration (lines
  25-50), tw:local-groups/tw:local-two (lines 232-366, 456-464),
  tw:local-generators/tw:vector-table/tw:relators (lines 467-640),
  tw:GB/tw:GB-basic/tw:GB-presentation (lines 748-849),
  tw:quadratic-layer/tw:retained-quotient (lines 851-990),
  tw:field-family existence (lines 1443-1589), tw:base (lines 96-126),
  construction-41cap.md Secs 2-3 (P41[1] norm 41, cap swap),
  lie241.py/lie241c.py via reruns, C3 script reduce_mod lines + zero-test
  uses, references/schmidt_2002_two_and_infinity_arXiv-math0008246.pdf
  via pdftotext (Thm 1, Thm 2/2', Lemma 3.1, Sec 3-4).
- Ran `research/2026-10-muse-involution-class/code/C93/c93_quotient_repair_check.py` (stdlib,
  exit 0): capped a0..a5, q-threshold, uncapped positivity, 13^4 = 17
  mod 32, 3^2 = 5^2 = 9 mod 16, 9^2 = 1 mod 16, 41 = 9 mod 16.
- Reran `research/2026-10-muse-involution-class/code/R5/liftdefect.py` (exit 0): outputs quoted
  in Secs 2a/4b/4c/4d. Reran `research/2026-10-muse-involution-class/code/R5/bracket45.py`
  (exit 0): 56/56.
- Searched repo + references for Labute/mild/Anick (no source); confirmed
  the note's flag.
- Proved Secs 1a/1b/1c (with set fix), 3b order lemma, 3c no-cyclotomic-Z2,
  4a, 4b reduction, 4c automatic D4, 4d Frob irrelevance by hand (this
  file); refuted 3d mu16 via N = 3,5 + phi^2 action; verified Sec 5
  soundness argument.
- NOT checked: any new quotient/relator lifts; profile grids (parked);
  41-cap infinitude beyond cited construction (hypothesis for field
  transfer); third independent tensor implementation of (ii) rank 18;
  explicit Magnus formula for D2 degree-4 parts; PARI local degree-2
  computations; any per-layer lower bound on g4/g5.

## 7. Use

Use Sec 1a/1b/1c (with Cset reading) and Sec 4a wherever the old
R5-signature-threshold Sec 3 was cited; they agree with C86 Lemmas A-D
and add the single-commutator equivalence and exact-R4 sufficiency.
Use Sec 2a/2b numbers (140, +2, a5 = -68, q >= 3 threshold) as computed;
do not cite mildness exclusion or initials-only deadness as proved.
Use Sec 3b order>=32 as a sufficient condition for a D4-witness;
treat Schmidt/cyclotomic non-routes as scoped assessments; do not cite
mu16 in BG or GB^ab = F2^8. Use Sec 4b/4c ranks (18, ker 7) as
compatibility (not existence); budget R4 as 248 dims pending real/ebar
proofs (210 only conditionally). Sec 5 soundness justifies continued use
of bracket45/C3 zero-tests.
