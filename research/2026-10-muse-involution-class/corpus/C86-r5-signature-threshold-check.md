# C86 check: R5 signature threshold (threshold + audit verified; quotient lemma repaired)

Lane C86, 2026-10-06. Source note (reviewed):
`research/2026-10-muse-involution-class/notes/reviewed/R5-signature-threshold.md` (sections 1-5).
Requested focus (general; coordinator: both endpoint margins, rounded versus
exact thresholds, both involutions and field transfer; centralizer lifting;
degree-5 detection versus arbitrary finite-quotient repair).
Check code: `research/2026-10-muse-involution-class/code/C86/c86_threshold_check.py` and
`research/2026-10-muse-involution-class/code/C86/c86_involution_ranks.py` (both stdlib-only, exit 0).
Reran `research/2026-10-muse-involution-class/code/R5/involution_audit.py` (exit 0) with
`/tmp/C62-venv/bin/python` (numpy present) and
`papers/0.04273/certificates/lie241c.py` (R3 rank 142, L3 26).

Verdict: section 1 (threshold table) VERIFIED, including the certified
impossibility and the conditional 2^16 close of middle/estimated; section 2
(both-involution audit) VERIFIED with an independent stdlib reimplementation
(both classes exactly 2^15, separation for both). Section 3 as written is
INVALID in two places (central-extension equality; exact-depth-5 existence
from the weak hypothesis) and is REPAIRED below to proved lemmas with exact
hypotheses (Lemmas A-D); the field-transfer half is sound given a suitable
quotient. Section 4's equivalence is REFUTED as stated (only one direction
holds); the obstruction (unrecorded relator lifts block exact R4/R5) is
SOURCED (C16 section 3, confirmed applicable) but the universal
no-quotient-of-order->=2^50 phrasing is kept as an assessed obstruction, not
a proved impossibility.

No previously accepted corpus result is overturned (C62, C16 stand as cited).

## 1. Threshold table at delta = 0.043172 (verified; conditional close)

Inputs: C62-verified zero enclosures (middle theta_0 in
[0.49999550189240666, 0.49999550189240672], estimated theta_0 in
[0.49999348507339658, 0.49999348507339664], certified theta_0 =
0.50001365326... > 1/2), slope enclosure [0.6247461937..., ...] > 0, M(1/2)
enclosures (-8.53e-6 / +2.81e-6 / +4.07e-6), and theta*(N) = 1/2 - 1/(4N)
(from b/d = 1/(2 N_iota), theta = (1-b/d)/2; `tower.tex` thm tw:field-family
proof). M affine with slope > 0 at Gaussian profiles.

Checked (`c86_threshold_check.py`, exact rational arithmetic):

- Rounding cover: quoted zeros + 5e-11 exceed the C62 upper ends (slacks
  5.76e-11 / 7.66e-11). N_min from covered zeros: 55580 / 38374, matching
  the note. From raw C62 upper ends: 55579 / 38374, so the cover costs 1 on
  middle, in the safe direction; both lie strictly inside (32768, 65536),
  so the verdict is unaffected by +-1.
- Gaps: theta*(2^15) = 65535/131072 short of the true zeros by 3.131e-6 /
  1.114e-6; theta*(2^16) = 1/2 - 2^-18 exceeds them by 6.834e-7 /
  2.700e-6. The note's roundings (3.1e-6 / 1.1e-6 / 6.8e-7 / 2.7e-6) are
  confirmed. Min gap / 5e-11 = 13668 > 1e4, so "4+ orders" holds.
- M lower bounds at theta*(2^16) via slope_lo * gap: +4.270e-7 (middle),
  +1.687e-6 (estimated), both > 0; the note's M ~= +4.3e-7 / +1.7e-6
  illustrations match.
- Certified: theta_0 > 1/2 with slope > 0 and M(1/2) < 0 gives M < 0 on all
  of [theta*, 1/2] for every N; unreachable by signature improvement alone
  at fixed profiles. Confirmed.

Proved conditional (preserved): IF a tower quotient/field with
N_iota >= 2^16 is achieved, THEN at delta = 0.043172 with Gaussian profiles
the middle and estimated baselines have M > 0 uniformly on
[theta*_new, 1/2) (theta*_new above both zeros, M(1/2) > 0, slope > 0, so
inf >= M(theta*_new) > 0), while the certified baseline still fails
(M(1/2) < 0 fixed). No such quotient is exhibited here or in the note.

Cap-swap invariance (proved, as cited): the 41-cap tower shares Gbar_B, both
classes and theta* with the 241 tower, because the swap changes only the
(iv) quartics F^4 in D_4 (tower.tex Lemma tw:GB-presentation;
`construction-41cap.md` sections 2-3), which are trivial mod D_4, so
N_B D_4 F, Gbar_B = G_B/D_4, R_2 and R_3 are unaffected (C16 section 2).
This is what licenses applying the 241-vector audit to the 41-cap G_B.

## 2. Both-involution audit in Gbar_B (computed; independently verified)

`involution_audit.py` reruns exit 0: ad(c): L1 -> gr2 has rank 7 and
ad(c): gr2 -> gr3 has rank 8 for BOTH c1 and c2. The independent stdlib
reimplementation (`c86_involution_ranks.py`, own F2 rank, own bracket/tensor
code, copied vector table, no lie241 import) confirms: R2 rank 21 (L2 15),
R3 span 170 vectors of rank 142 (L3 26, 28 syzygies), complement size 15,
(7, 8) for both c1 and c2, separation (d) True for both, c1bar != c2bar.

The class-size inference for c2 is valid: kernel of ad(c2) on L1 is
1-dimensional (8 - 7) and contains the line through c2bar (since
[c2bar, c2bar] = 0), hence equals it; the tower.tex proof of
tw:retained-quotient(c) then applies verbatim (|C| = 2^34, class 2^15),
using only Gbar-level facts (D_2 abelian, D_3 central). Separation (d) for
both follows from lie241.py's check (rerun True on import) and the stdlib
recheck. So both involutions have class exactly 2^15 in Gbar_B; switching
the fixed field to iota_2 gives no gain at the retained level (the
field-family counting is symmetric in iota_1/iota_2 given
ibar1 != ibar2 and separation for both).

## 3. Quotient-extension lemma (as-stated claims refuted; repaired proofs)

Let G_B be the 41-cap tower group, pi: G_B -> Gbar_B the retained quotient.
Filtration facts used: [D_m, D_n] subset D_{m+n} (tower.tex line 35), D_n
open (G_B finitely generated; cf. line 1493), intersection D_n = 1 (pro-2),
surjections map D_n onto D_n. |Gbar_B| = 2^49, |C_Gbar(ibar1)| = 2^34.

### 3a. Central extensions: equality refuted, inequality proved

The note's claim "Central extensions never grow the class: if
D_5 subset V subset D_4 then ... |cl_Q(iota_1)| = 2^15 still" is REFUTED as
stated. Trivial action of iota_1 on the central kernel K = D_4/V gives
K subset C_Q, hence |C_Q| = |pi(C_Q)| |K| with pi(C_Q) subset C_Gbar, so
|cl_Q| = |Gbar|/|pi(C_Q)| >= 2^15: central extensions never SHRINK the
class, but they GROW it exactly when centralizer lifting is incomplete
(pi(C_Q) a proper subgroup of C_Gbar). Equality needs surjective lifting,
which the note does not prove. The direction is backwards, and the claim
contradicts the note's own weaker-variant sentence (lifting defect).

Abstract counterexample (central extension growing the class with trivial
kernel action): Q = D_8 = <r,s | r^4 = s^2 = 1, srs = r^-1>, K = {1, r^2}
central, Gbar = Q/K ~= C2 x C2. The class of s in Q has 2 elements
({s, s r^2}, centralizer {1, s, r^2, s r^2} of order 4), while sbar in the
abelian Gbar has class size 1. So |cl| grew 1 -> 2 across a central
extension on which s acts trivially.

Lemma C (proved repair). Let V be open normal with D_5 subset V subset D_4
(conditional on existence, which needs g_4 > 0; C16 leaves g_4 in [0,81]).
Then K = D_4/V is central in Q = G_B/V and |cl_Q(iota_1)| >= 2^15, with
equality iff pi(C_Q(iota_1)) = C_Gbar(ibar1). (Normality of every such V:
D_4/D_5 is central in G_B/D_5 since [D_4, D_1] subset D_5.)

### 3b. Exact-depth-5 lemma: proof invalid as stated; repaired hypotheses

The note's Lemma assumes [D_4 G_B, iota_1] != 1 and concludes an open normal
V with D_6 subset V subset D_5, [D_5:V] = 2, with |cl_Q| >= 2^16. The proof
step "choose V missing some [g, iota_1] not in D_6 (exists by hypothesis)"
is INVALID: the hypothesis gives [g, iota_1] != 1, not [g, iota_1] not in
D_6; a witness in D_6 \ {1} is consistent with the hypothesis and defeats
the construction (every V above D_6 contains it). Moreover the conclusion's
existence claim alone needs D_5 != D_6 (g_5 >= 1), which is OPEN (C16:
g_5 in [0,199]); under the consistent-with-data scenario g_5 = 0 no such V
exists at all. So the Lemma as stated is not proved (and its exact-depth
conclusion does not follow from its hypothesis).

Lemma A (proved repair, exact depth 5, strengthened hypothesis). Assume
[D_4, iota_1] is NOT contained in D_6, i.e. some g in D_4 has
[g, iota_1] not in D_6 (equivalently the bracket [., ibar1]: gr_4 -> gr_5
is nonzero, since the Lie bracket is induced by commutators). Then
D_5 != D_6, and for any hyperplane V with D_6 subset V subset D_5,
[D_5:V] = 2 missing [g, iota_1]: V is normal (D_5/D_6 central in G_B/D_6)
and open; J = D_4/V is a finite 2-group on which iota_1 acts nontrivially,
so C_J is a proper subgroup and |C_J| <= |J|/2 by Lagrange; |C_Q| =
|pi(C_Q)| |C_J| <= 2^34 |J|/2 (kernel C_Q cap J = C_J); |Q| = 2^49 |J|;
hence |cl_Q(iota_1)| >= 2^16. (J = D_4/V is abelian here since
[D_4, D_4] subset D_8 subset D_6, so the note's |J:C_J| = |image| also
holds; Lagrange alone suffices.)

Lemma B (proved repair, arbitrary depth, weak hypothesis). Assume only
[D_4, iota_1] != 1: some g in D_4 has x = [g, iota_1] != 1. Then x in D_5
and, since intersection D_n = 1, x in D_k \ D_{k+1} for some k >= 5. For any
V with D_{k+1} subset V subset D_k, [D_k:V] = 2 missing x: V is normal and
open by the same central-quotient argument, iota_1 acts nontrivially on
J = D_4/V, and the identical count gives |cl_Q(iota_1)| >= 2^16 with
|Q| = 2^{S_k + 1}, S_k = 49 + g_4 + ... + g_{k-1}. (No abelianness needed:
proper subgroup of a 2-group has index >= 2.)

### 3c. Field transfer (sound given a suitable quotient)

Lemma D (proved, as in the note). Given V open normal with V subset D_4 and
Q = G_B/V with |cl_Q(iota_1)| >= 2^16: for every 2-power m >= |Q| there is
an open normal U subset V of index m (tower.tex existence argument with D_4
replaced by V: pick U' subset V open normal of large index using infinitude
of G_B, N' = V/U', center series gives the exact index since |Q| divides m
as 2-powers), K = Fix(U) has H = Gal(K/B) mapping onto Q, so
N_iota = |cl_H| >= |cl_Q| >= 2^16 (conjugacy classes map onto classes),
b/d = 1/(2 N_iota) <= 2^-17, theta >= 1/2 - 2^-18. Local structure
(U subset V subset D_3, retained-quotient(b)), separation (d) (gr_1 data),
b >= 1 (ibar1 != ibar2), and rd are preserved. Precision: for the 41-cap
G_B this is the 41-cap analogue of tw:field-family (41-cap local table),
not tw:field-family's table verbatim.

## 4. Missing fact and obstruction (equivalence refuted; obstruction sourced)

The note's "[D_4 G_B, iota_1] != 1 iff the bracket gr_4 -> gr_5 is nonzero"
is REFUTED as an equivalence: nonzero bracket implies noncommutation
(witness outside D_6 is nonzero), but the converse fails in general (a
witness in D_6 \ {1} gives noncommutation with zero bracket). For G_B
specifically the bracket question is unresolved. Corrected missing-fact
split: depth-5 bracket-nonzero is SUFFICIENT for 2^16 via Lemma A;
[D_4, iota_1] != 1 at any depth is SUFFICIENT via Lemma B; neither is
NECESSARY (a central lifting defect with [D_4, iota_1] = 1 could also grow
the class, per Lemma C; the note's weaker variant, not pursued).

The obstruction is SOURCED and applicable: exact R_4/R_5 need the subleading
relator parts via the 28 degree-3 syzygies (170-vector R_3 span of rank 142,
rerun in section 2), while the 7 global relators rho_nu are specified via
local class field theory (lifts ghat plus local relations; only quadratic
initials via Hilbert symbols recorded in tw:vector-table/tw:local-initials,
recomputed by kummer241.gp), not as explicit words (C16 section 3;
tower.tex tw:relators/tw:local-forms). The ordering "(i) explicit words to
degree 5, then bounded linear algebra (T_5 dim 8^5 = 32768)" is sound as a
concreteness remark (8^5 = 32768 verified). The universal phrasing "No ...
exhibited quotient Q of order >= 2^50 is possible from recorded data" is
kept as an assessed obstruction (any Q strictly above Gbar needs degree-4
relation data to certify it is a quotient of the actual G_B), not a proved
impossibility theorem. Infinitude-alone-does-not-imply-growth is kept as a
remark (central involutions exist in infinite 2-groups generally).

## 5. What was checked (inputs and versions)

- Read the note at `research/2026-10-muse-involution-class/notes/ready/R5-signature-threshold.md`
  (pre-review location), C62 (`corpus/C62-r5-margin-accounting-check.md`),
  R5-margin-accounting (reviewed), C16 (`corpus/C16-lie45-upper-bounds.md`),
  tower.tex tw:GB-presentation/tw:quadratic-layer/tw:retained-quotient (lines
  806-990), tw:field-family (lines 1443-1589), filtration conventions (lines
  25-50), tw:vector-table/tw:relators/tw:local-initials (lines 525-640),
  lie241.py/lie241c.py sources, `construction-41cap.md` sections 2-3.
- Ran `research/2026-10-muse-involution-class/code/C86/c86_threshold_check.py` (stdlib, exit 0):
  cover, N_min 55580/38374, gaps, 4+ orders, M lower bounds, certified
  impossibility, theta*(2^16) = 1/2 - 2^-18 exact.
- Ran `research/2026-10-muse-involution-class/code/C86/c86_involution_ranks.py` (stdlib, exit 0):
  R2 21, R3 142/28 syzygies, (7,8) both involutions, separation both True.
- Reran `research/2026-10-muse-involution-class/code/R5/involution_audit.py` (exit 0, AUDIT PASS)
  and lie241c.py (rank 142, L3 26) with /tmp/C62-venv/bin/python.
- Proved Lemmas A-D and the D_8 counterexample by hand (this file sections
  3-4); verified the c2 centralizer-count transfer and the cap-swap
  invariance reasoning against C16 section 2 and the cited tower lines.
- Skimmed ready `R5-quotient-repair.md` section 1 (an independent repair of
  the same section 3, pending its own check) for overlap only [S6: since
  reviewed — C93 record exists, agrees with Lemmas A-D with the Cset fix];
  the repairs above were derived and verified independently. NOT checked: any new
  quotient, relator lifts, profile grids (parked), or 41-cap infinitude
  beyond the cited construction record (used only as a hypothesis for
  Lemma D's existence step).
