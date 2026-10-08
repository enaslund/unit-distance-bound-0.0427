# C127 check: R5 uniform-defect computation core (TOTAL 6, LV-exactness, ad3 miss)

Lane C127, 2026-10-06. Source note (reviewed):
`research/2026-10-muse-involution-class/notes/reviewed/R5-uniform-defect.md` §§1-2 (checked at the
ready version; E-fix `R5-defect-efix.md` applied in place).
Requested focus: general.
Check code (stdlib only, no numpy, system python3, exit 0):
`research/2026-10-muse-involution-class/code/C127/c127_uniform_defect_check.py` (ALL PASS),
`research/2026-10-muse-involution-class/code/C127/c127_probes.py`,
`research/2026-10-muse-involution-class/code/C127/c127_kervar_probe.py`.
Reran author's `research/2026-10-muse-involution-class/code/R5/robust_defect.py`,
`validate_chain.py`, `total_margin.py`, `margin_replay.py`,
`collection_check.py`, `genuine_lift.py` (all exit 0, all outputs reproduced).
Ssel-independence probe: `research/2026-10-muse-involution-class/code/C127/c127_sse1_probe.py`
(author modules, exit 0).

Verdict: §§1-2 VERIFIED (computed + proved) with one stale-title nit
(§1 title says 24-dim, correct E-fixed value 6-dim as the body states)
and one precision (rho_p2 channels hold mod I4, sufficient for TOTAL).
Strengthened: LV(kerM) lies in I4 itself (5992/5992), so R4 is constant
over A mod I4; TOTAL/miss independent of quotient section; full-240
37-dim miss corroborated. No claim rejected; H2 (R4-exhaustion) stays
with `R5-no-c4-g4bound.md` §2 (pending its own review) and is NOT
verified here.

## 1. Setup (as used)

F free pro-2 on Kummer lifts; ARB section w-hat (genuine products);
TRUE g-hat = w-hat.d, T' = (d)_2 in L2/R2 per lift (15 x 16 = 240).
A = y1-cut 214-affine space {T' : C1+K+M(T') in I3} (C116-verified;
recomputed here §3). corr_s(T') = (w_s)_4 for the 28 syzygy words
w_s (products of [rho-hat,x-hat] and omega-hat factors, all in D3).
TOTAL = I4 + span(model) + LV(T0) + LV(kerM), the universal enclosing
space: for every T' in A, span_s(corr_s(T')) is contained in TOTAL
(§4). ad3 = [.,i-bar]: L3 -> L4/I4 for c1, c2.

## 2. TOTAL/ad3/witness (computed; verified with two eliminations)

- L2 36, R2 21, L3 168, I3 142, L4 1044, I4 963 (41-cap): reproduced
  with high-bit AND low-bit pivot eliminations (all match).
- Syzygy kernel 28 (170 -> 142), all kernel vectors verified summing
  to 0; 21 Q2 uniquely identified; y1-word uses 9 initials incl rho_p2.
- Model span mod I4 = 4 (E-fixed: ([A,x])_4 = [(A)_3,X] + [(A)_2,X]X;
  E T'-free since (rho-hat)_2 = recorded initial, verified for all 20
  types + r_stand with random T'/U'/T4). E-formula + master
  ([A,B])_4 formula exact 6/6 on random D2 x D1 trips.
- M1 (y1-cut map 240 -> L3/I3): rank 26, R2-kernel 0/336, C1+K
  consistent; kerM dim 214, T0 particular solves the cut; kerM/T0
  re-verified against the cut equation.
- LV(R2) = 0: 0/9408 outside I4 (28 x 16 x 21), so LV descends to the
  240-quotient; sample cross-checked with low-bit elimination.
- TOTAL dim mod I4 = 6 with BOTH eliminations; breakdown model 4,
  model+T0 6, total 6 (T0 adds 2, ker adds 0).
- ad3 rank mod I4 = 18 for c1 AND c2 (both eliminations); escape-dim
  vs TOTAL = 18/18 both (full images disjoint); witness L3-row 1 =
  [X_0^2,X_1] (verified in L3 and nonzero mod R3) misses TOTAL for
  BOTH involutions (residues nonzero with both eliminations);
  192/288 witness rows each. [R3,c] in I4 verified 0/340, so the map
  factors through gr3.
- Full-240 (no y1-cut): TOTAL 37-dim, ad3 still escapes 18/18 both
  (H1-independence corroboration; belongs to `R5-defect-h1free.md`).

## 3. LV-exactness (proved + computed)

corr_s = model_s + LV_s(T') holds EXACTLY for the 24 non-rho_p2
syzygies (direct trip-vs-prediction with random full-L2 T', random T3
U', random T4: 24/24 exact), and MOD I4 for the 4 rho_p2-involving
syzygies (model uses Fpin; difference is [I3+ebar,X] in I4 by
nine-in-I3 + [I3,L1] in I4 by I4 construction; Fpin consistency and
image rank 19 re-verified, both eliminations). Since TOTAL contains
I4, mod-I4 equality suffices for R4(TRUE) subset TOTAL.

- No T'^2: syzygy-word factors lie in D3, so (w)_4 = sum (factors)_4
  with no cross terms; deg-3 parts see inputs' deg <= 2 linearly
  (T'.T' is deg 4); confirmed by random-T' exactness.
- No U': every word has even exponent-sums (squares 2, comms 0,
  tame rho f:0/t:1-p = -2/-4, r-hat formal 0, omega-hat 0/0, syzygy
  words inherited 0); U'.anything is deg >= 4; inverses contribute one
  U' each with exponent-sum-mod-2 coefficient (C116 inverse subtlety).
  Confirmed by random-U3 exactness (equality despite random U3).
- T4/U'' absent: random-T4 exactness (A2 with t4=True); ([A,B])_4
  master formula uses no (A)_4.
- LV formulas per type (squares [V,T'], comms, tame ARB-perturbation,
  r2_cross, omega chain) all covered by the 24/24 trials (all 21 Qnames
  occur; omega slots included). r-hat LV via initial-determined
  r2_cross is justified by C116's LV lemma (D2-word linearization
  depends only on the initial); LV_Wp == LV_r re-verified; r_stand
  affinity + y2 T'/U'-freedom 2/2.
  Clarification (C141, 2026-10-06): "omega slots included" is
  inaccurate — 0/28 syzygy vectors use omega slots in any basis
  (the 2 cubics are independent of the 168 quadric rows: rank
  140 + 2 = 142, so no kernel vector involves them; verified
  with both eliminations). The omega LV/model channels are
  therefore vacuous for corr_s/TOTAL, and the "all live channels
  covered" conclusion stands (20/20 non-p2 Qnames in the 24; p2
  mod-I4 via r_stand). This entry's verdicts are unchanged.

## 4. Why R4(T') sits in TOTAL (proved, given H2+H3)

Assume H2 (R4 = I4 + span_28(corrs), pending) and H3 (§3: corrs =
model + LV). For T' = T0 + sum c_v kv in A: corr_s(T') = model_s +
LV_s(T0) + sum c_v LV_s(kv), each term in TOTAL by construction, hence
each corr_s(T') in TOTAL and span_s in TOTAL. So R4(T') subset TOTAL
for every T' in A. The argument needs only mod-I4 equality for rho_p2
slots (TOTAL contains I4).

## 5. Strengthenings and nits

- LV(kerM) subset I4 (5992/5992, both eliminations + author-code probe
  with 2092 nonzero raw, so not a trivial-zero artifact): R4 is
  CONSTANT over A mod I4 (equals I4 + span_s(model_s + LV_s(T0))).
  The note claims only ker-var 0 beyond model+T0; the stronger
  containment holds.
- Ssel independence: alt quotient section (disjoint 15-set) gives same
  TOTAL 6, same escape 18, same witness row 1 both cases. Theoretically
  expected since M(R2) in I3 and LV(R2) in I4 make M1/LV descend.
- Nit: §1 title "TOTAL is 24-dim" is the stale pre-E-fix number; the
  body correctly states 6-dim (E-fix applied). Cite 6 (A-restricted)
  and 37 (full-240), never 24.
- The §1 breakdown print in code ("model=4 +T0shift=6 +ker-var=6") is
  cumulative (model / model+T0 / total), i.e. increments 4+2+0.

## 6. What was checked (inputs and versions)

- `c127_uniform_defect_check.py` (exit 0, ALL PASS): V parsed from
  lie241.py source (19 vectors); own big-endian tensors, own dict
  Magnus deg3/4, own trip3/trip4, own tame perturbation; every rank
  with high- AND low-bit eliminations; PART1 ranks, PART2
  syzygy/qlabel/Fpin/nine/model-4, PART3 y1-cut 26/0/consistency +
  kerM-214/T0 + cut-equation re-verification, PART4 TOTAL-6/ad3-18/
  witness-1/escape-18/full240-37, PART5 E+master 6/6, (rho)_2 recorded
  20+r_stand, r_stand/B 2/2, A2 24/24 (random T'/U'/T4), PART6 margin
  replay, PART7 256-V group-like.
- `c127_probes.py` (exit 0): [R3,c] in I4 0/340; L3row1 in L3 and
  nonzero mod I3.
- `c127_kervar_probe.py` (exit 0): LV(kerM) in I4 0/5992 outside with
  both eliminations (independent reimplementation).
- `c127_sse1_probe.py` (exit 0, author modules): ker-var 2092 nonzero
  raw / 0 outside I4; alt Ssel TOTAL 6 + escape 18 + witness 1 both.
- Reran author's robust_defect.py (TOTAL 6, 18/18, witness 1, bit-2177,
  fingerprint c150066198ceb819), validate_chain.py (A1/A2-24/B/C-12),
  total_margin.py (escape 18, full240 37, bit-2112,
  fingerprint 0998513c045145e5), margin_replay.py, collection_check.py
  (D1-D5), genuine_lift.py (26-dim cut, 51/71/57/56, nine, 27->8):
  all exit 0 as claimed.
- Read: genuine_lift.py (704 lines), robust_defect.py, validate_chain.py,
  collection_check.py, total_margin.py, margin_replay.py; corpus
  C116-fiber-cut-26 (LV lemma, U'-lemma, formal pin cited for rho_p2),
  C93 §4b (bracket exactness cited, not re-proved), C107 (ranks).
- NOT checked: H2 R4-exhaustion (no-c4 §2, pending); per-layer lower
  bounds on g4/g5; third tensor endianness for the SAME miss bits
  (low-bit elimination is the independence used; cert fingerprints are
  basis-dependent and reproduced, not independently re-derived).

## 7. Use

Cite TOTAL = 6-dim mod I4 over A (model 4 + T0 2 + ker 0; LV(kerM) in
I4), LV(R2) = 0 (9408), ad3 rank 18/18, witness [X_0^2,X_1] missing
TOTAL for both involutions with escape-dim 18, E-formula, and LV
affinity (exact 24/24, mod-I4 for rho_p2) as verified. Cite full-240
37-dim + escape 18 as corroboration (owned by the h1free note). For the
defect-to-fields-to-margin chain see `C127-uniform-defect-chain.md`
(conditional on H2). Do not cite TOTAL 24 (stale).
