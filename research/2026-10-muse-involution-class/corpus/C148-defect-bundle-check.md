# C148 check of R5-defect-bundle (stabilized H1a+H2+H3 + full-240 cert)

Lane C148, 2026-10-06. Source note (reviewed):
`research/2026-10-muse-involution-class/notes/reviewed/R5-defect-bundle.md` (checked at the ready
version). Requested focus: general.
Check code (author tensor imports; all ranks/residues recomputed with an
independent lowbit elimination; fresh seed 148; own trip4 + own word algebra;
exit 0): `research/2026-10-muse-involution-class/code/C148/c148_bundle_check.py` (ALL PASS, 65 checks),
log `research/2026-10-muse-involution-class/code/C148/c148_bundle_check.log`.
Reran author's `research/2026-10-muse-involution-class/code/R5/total_margin.py`,
`robust_defect.py`, `validate_chain.py`, `collection_check.py` (all exit 0,
all outputs reproduced; both tracked fingerprints reproduced;
`git status` clean after reruns, i.e. deterministic regeneration).

Verdict: COMPUTATIONS VERIFIED (lowbit + fresh randomness); H2 CONCLUSION
PROVED (statement owned by C126; this note's sketch screened with no errors);
H1a/H3 CONCLUSIONS VERIFIED WITH THE STANDING C129 REPAIR (both sections
repeat the refuted Fpin wording: "F_r in K+I3" + "Fpin exact mod I4" in §1
and "corr_s EXACTLY" in §3 are FALSE as stated at the 4 rho_p2 syzygies;
repaired to the K basepoint mod I4, offsets verified in TOTAL, miss
survives); §4 cert VERIFIED; §5 VERIFIED AS CONDITIONAL (repaired H3 +
checked links + infinitude hypothesis). No new refutation beyond C129's
standing verdict; nothing rejected outright.

No previously accepted corpus result is overturned.

## 1. Setup + L0 (§0): verified

F/π/ARB/TRUE/T'/U'/U'' setup matches the C116-verified framework; 15x16 =
240 quotient dims. L0 (LV(R2) = 0, 0/9408) recomputed with lowbit
elimination: 0 outside I4 over all 28x16x21 = 9408 combinations, so
variation descends to the 240-quotient and TOTAL_full240 is well-defined.

## 2. H1a y2-pin (§1): premises verified; pin statement inherits C129's refutation, repaired

Verified:

- Wp = y2^2[x2,y2][x2,z2] in N_B: y2^2 by the D-cap y^2 = 1 and the comms
  by [x,y] = [x,z] = 1 in D (tw:local-two(b), read), each a D-word hence
  in N_B by the D-word converse (tower.tex lines ~1400-1403, read).
- r-hat in N_B (local relation, tw:relators/tw:GB-presentation, as cited
  by C116); (Wp)_2 = (r-hat)_2 = deminit(2) recomputed from ARB trips.
- W'' = Wp.r-hat^{-1} in N_B cap D3: deg-2 parts cancel in char 2
  (both D2, no cross), so (W'')_3 in R3 = I3 by paper exactness in
  degree 3 (tw:retained-quotient(a), read: R3 spanned by the 21x8
  brackets + 2 cubics, rank 142).
- (W'')_3 = (Wp)_3 + (r-hat)_3 (D2 factors, no cross; inverse contributes
  +(r-hat)_3 since (r-hat)_1 = 0): identity-level, consistent with the
  trip algebra (P5 identities below).
- U'-absence for Wp: occurrence counts X:4/Y:4/Z:2, all even (P0); r-hat
  formal-D2, even. LV_Wp = LV_r as maps recomputed (same lists); the
  CONCLUSION stands via C116's LV lemma (initial-determined
  linearization, triple-commutator proof), not via the tautological
  code check (same formula twice, per C116 §2).

Refuted as stated (inherited from C129, reconfirmed here with lowbit):

- "Hence F_r in K + I3; model-term [Fpin,X_i], Fpin = K + LV_r(ARB2),
  exact mod I4" is FALSE for TRUE F_r. TRUE F_r = K + LV_r(T'_true) + e,
  e in I3 (W''-argument, C129 §2). LVa = Fpin^K is NOT in I3 (lowbit),
  and [LVa,X] is outside I4 for all 8 X (lowbit 8/8). So neither "TRUE
  F_r in K+I3" (needs LV_r(T'_true) in I3, false in general and unproved
  for TRUE) nor "[Fpin,X] exact mod I4" (off by [LVa,X]) holds.
- Repair (C129/C141, re-verified here): use the K basepoint. The
  per-syzygy offsets v_s = sum over p2 slots of [LVa,X] (s = 5,6,9,11,
  author's kernel indices) all lie in TOTAL_214 (4/4, lowbit) hence in
  TOTAL_full240 (4/4, lowbit). Repaired K-model TOTALs are 2-dim over A
  and 33-dim over full-240 (lowbit; both subsets of the Fpin models),
  and the witness miss survives (escape 18/18 both involutions, §4).
  Do not cite H1a with the Fpin basepoint; use K mod I3.

## 3. H2 R4-exhaustion (§2): correct sketch of a statement proved by C126

Statement R4 = I4 + span_28(corr_s(T'_true)) is PROVED in
`research/2026-10-muse-involution-class/corpus/C126-g4-lower-bound.md` (both inclusions;
dim R4 in [963,991]). This note's sketch was screened step by step; no
errors found. Omissions are exactly the load-bearing steps C126's repair
supplies (even-exponent combining with the pairing
rho^g.rho^h = rho^2[rho,g][rho,h] mod D5, f = x.u conjugator reduction,
[a,bc] induction, well-definedness of the 28-image, subleading
(rho)_3 cancellation by even multiplicity). Computational premises
re-verified here (lowbit + fresh seed-148 trips):

- R2 rank 21 (quadric exponents even); 170 R3 rows rank 142, kernel 28,
  all verify; omega slots vacuous in this basis (0/28; cubics
  independent, rank 140+2 = 142, per C141).
- ([A,B])_3 = [(A)_2,V_B] EXACTLY for A in D2: 10/10 on random trips
  with full random higher parts (B_2/B_3 terms cancel as claimed).
  This is the identity underlying C116's LV lemma; the bundle's H2(ii)
  use (deg-3 is a 170 -> 142 syzygy) follows.
- Master ([A,B])_4 = [(A)_3,V_B] + [(A)_2,(B)_2] + [(A)_2,V_B]V_B:
  10/10 exact (fresh seed); E-identity 10/10 (no (A)_4 term);
  a4-cancellation 10/10 (U'' absent from commutator deg-4).
- [R2,L2] subset I4: 0/756 outside (lowbit folding); [R3,L1] subset I4
  (all R3 rows x 8 gens, lowbit); cubic adjustment in [R3,L1],
  quartic invariance, D3-factor none ([D3,D3] subset D6 = 1 in F/D5),
  [D3,D2] subset D5: as stated (collection_check D1-D5 rerun green).
- E-terms T'-free since (rho-hat)_2 = recorded initial (asserted in D3;
  C127 verified all 20 types + r_stand).

Cite the H2 statement from C126; cite this note's §2 only as a
corroborating sketch with complete collection references.

## 4. H3 affinity + cancellation (§3): conclusions verified; "EXACTLY" inherits C129's refutation, repaired

Verified (lowbit + P0 word algebra + reruns):

- Occurrence-parity table (values as OCCURRENCE counts; the note labels
  them "exponent-sums" — harmless terminology nit since occurrences ==
  exp-sum mod 2, verified on all table words): squares 2; cap comms
  2/2; tame rho f:2/t:1+p = 4/6 (p = 3/5); omega Y:4/Z:6 with exp 0/0;
  Wp X:4/Y:4/Z:2 with exp X:0/Y:2/Z:0; dyadic 4/4; products inherit
  evenness (syzygy words). All even under either reading. (The tame
  exp-sum form is 1-p = -2/-4, parity-equivalent to the note's 1+p.)
- T'^2 absent (D3 factors, no cross in deg-4; deg-3 parts linear in
  deg <= 2 inputs), E T'-free, U'' absent (a4-cancel, P5), U' absent
  (parity + random-T3 trials): validate A2 24/24 exact rerun green
  (author seed); fresh-seed identities in P5 corroborate the symbolic
  arguments. Omega LV/model channels vacuous for corrs (0/28).
- LV formulas per type + L0 (§1): covered by the trials + LV(R2) = 0.

Refuted as stated (C129's refutation, inherited):

- "corr_s = model_s + LV_s(T') EXACTLY" with the Fpin basepoint is FALSE
  at the 4 rho_p2 syzygies (off by v_s + I4; §2 above). Repaired H3
  (K basepoint, exact for the 24 non-p2 syzygies, exact mod I4 at p2
  via [I3,L1] subset I4) is VERIFIED. The note's own H1a parenthetical
  ("I3/ebar parts land in [I3,L1] subset I4") already concedes mod-I4
  absorption for residuals, consistent with the repair.
- Enclosure R4(TRUE) subset TOTAL holds either way (v_s in TOTAL, §2).

## 5. Full-240 certificate (§4): verified (computed)

Lowbit recomputation + rerun:

- TOTAL_full240 = 37-dim mod I4 (Fpin model; repaired K-model 33-dim).
- ad3 rank 18 for c1 AND c2; escape-dim vs TOTAL_full240 18/18 both
  (full images disjoint); witness L3-row 1 = [X_0^2,X_1] misses both;
  192/288 witness rows each.
- Separating functional exists (lowbit analogue verified; author-layout
  bit 2112 with wit1 = 1, zero on the basis, rerun-confirmed).
- Fingerprint 0998513c045145e5 reproduced; tracked
  `defect_cert_full240.json` byte-identical after rerun.
- A-restricted cert (6-dim, bit-2177, fingerprint c150066198ceb819)
  likewise reproduced; it is a refinement needing H1b, while the
  full-240 cert stands without H1b (TOTAL_214 subset TOTAL_full240:
  0 vectors outside, lowbit).

## 6. Defect + dependencies (§5): verified as conditional

R4(TRUE) subset TOTAL_full240 by H2 (C126 proved) + repaired H3 (K
basepoint + v_s in TOTAL, §2/§4). Witness outside by §4 gives
[s,iota_j] in D4 \\ D5 for lifts s of s-bar, both involutions, uniformly
([s,iota]_4 = [s-bar,i-bar] exact by C93 §4b, cited). Then C93 §4a
(Q 2^50, >= 2^16) -> C86 Lemma D (fields) -> C62 replay (margin):
chain logic sound as verified by C127/C142; transfer and analytic
witness correctly scoped as separate (not redone here). Scoping
precision (as in C86/C127/C142): C86 Lemma D uses 41-cap GB infinitude
as a HYPOTHESIS (tw:infinite covers the 241 tower); middle/estimated
analytic inputs remain uncertified (R4 owns certification; certified
tier fails regardless). The note's "conditional" label is accurate with
the H3 repair applied.

## 7. Falsification routes (§6): accurate

H1a (W'' in N, (W'')_2 = 0; R3 = I3): premises hold (§2). H2 (word
outside the 28 corrs): none exists by C126; the collection cases locate
any putative counterexample. H3 (LV formula error): finite-difference
trials (validate A-C, collection D, all rerun green + fresh-seed P5)
catch errors; none found beyond the Fpin basepoint (repaired).
Functional: deterministic regenerator rerun reproduces both certs.

## 8. What was checked (inputs and versions)

- `c148_bundle_check.py` (exit 0, ALL PASS, 65 checks,
  PYTHONPATH=/tmp/pylibs system python3): P0 word parity (own algebra,
  no author code); P1 ranks lowbit (L2 36, R2 21, L3 168, I3 142,
  free L4 1044, I4 963, [R3,L1]/[R2,L2] in I4); P2 kernel 28 lowbit +
  all verify + omega vacuity; P3 model 4, LV(R2) 0/9408, kerM 214, T0,
  TOTAL_214 6, TOTAL_full240 37, subset; P4 ad3 18, escape 18/18 vs
  both TOTALs, wit1, 192/288, functional existence; P5 fresh-seed
  trip identities (deg-3 10/10, master 10/10, E 10/10, a4-cancel
  10/10) + Fpin/K (LVa outside I3, [LVa,X] 8/8 outside I4, v_s 4/4 in
  both TOTALs, K-model 2/33, miss survives); P6 (Wp)_2 = deminit(2),
  LV_Wp == LV_r lists.
- Reran author's total_margin.py (TOTAL 6, escape 18 + 192 rows each,
  full240 37 + escape 18/18, bit 2112, fingerprint 0998513c045145e5),
  robust_defect.py (I4 963, model 4, kerM 214, LV(R2) 0/9408, TOTAL 6,
  ad3 18, wit1, bit 2177, fingerprint c150066198ceb819),
  validate_chain.py (A2 24/24, B 2/2, C 12/12), collection_check.py
  (D1 6/6, D2 0/756, D3 20/20 + r_stand, D4 exact + I4, D5 7
  quartics): all exit 0 as claimed.
- Read: the note; code genuine_lift.py (K/Fpin/LVa/M construction),
  robust_defect.py (model/LV/TOTAL/functional), validate_chain.py,
  collection_check.py, total_margin.py; paper tower.tex
  tw:GB-presentation (lines 806-849, 30 = 21+2+7), tw:quadratic-layer
  (R2 21), tw:retained-quotient(a) (R3 = I3, 170 -> 142), tw:local-two(b)
  (D presentation), D-word converse (~1401-1403); corpus C116-fiber-cut
  (LV lemma, premises), C126 (H2 proof), C127 x2, C129, C141, C142,
  C93 §4a/§4b citations (application verified, lemmas cited).
- NOT checked: C126's proof itself beyond premise verification (relied
  on as checked corpus); transfer lemmas and margin replay beyond
  application scoping (C127/C142 verified); analytic-input
  certification; 41-cap infinitude proof.

## 9. Use

Cite the bundle's parity table (occurrence counts, all even), deg-3
commutator identity, master/E/a4 identities, LV(R2) = 0, TOTALs
(6 A-restricted / 37 full-240 Fpin; 2 / 33 repaired K-model), ad3
18/18 escape with witness [X_0^2,X_1], both functionals, and the
conditional uniform defect ([s,iota] in D4 \\ D5 for every T', no H1b)
as verified. Cite H2's R4 = I4 + span_28 from C126 (this note's §2 is a
corroborating sketch). Do not cite "F_r in Fpin+I3", "Fpin exact mod
I4", or H3 "exactly" with the Fpin basepoint (use K mod I3 with the
v_s repair). Do not drop the infinitude-hypothesis and
uncertified-input qualifications on the chain to fields and margin.
