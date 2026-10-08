# C161 second review: R4 containment for the 41-cap defect (H1a+H2+H3 reconstructed)

Lane C161, 2026-10-06. Source note (reviewed, stays in place):
`research/2026-10-muse-involution-class/notes/reviewed/R5-uniform-defect.md` (second-opinion check;
first review by C127). Bundle version checked: corrected bundle at
`40d08300` ("R5: correct exponent-sum tables"), with the full-240
certificate `research/2026-10-muse-involution-class/code/R5/defect_cert_full240.json`
(fingerprint `0998513c045145e5`) and the A-restricted certificate
`defect_cert.json` (`c150066198ceb819`).
Requested focus: second independent review of actual R4 containment;
reconstruct H1a/H2/H3 for the 41-cap presentation; trace the
thirty-relator claim through tw:complete-global-presentation; collect
arbitrary conjugates modulo D5; derive higher-input cancellation in
degree-four corrections, especially cubic words, including the E-term
and the local-relator pin; establish containment before reproducing
the separator.

Check code (stdlib only, system python3, exit 0, ALL PASS 76 checks):
`research/2026-10-muse-involution-class/code/C161/c161_containment_check.py` (fresh seed 161;
V parsed from `lie241.py` source; little-endian bit tensors; lowbit
elimination; own trip3/trip4; own word algebra).
Reran author's `total_margin.py`, `robust_defect.py`,
`validate_chain.py`, `collection_check.py`, `no_c4.py`,
`margin_replay.py` (all exit 0, all outputs and both fingerprints
reproduced; `git status` clean: deterministic regeneration).

Verdict: CONTAINMENT VERIFIED (computed + proved):
R4(TRUE) is contained in TOTAL_full240 (37-dim Fpin / 33-dim repaired
K-model) with the standing C129 Fpin->K repair, hence the uniform
[s,iota] defect holds with NO y1-cut (H1b-free). The separator
(ad3 18/18 escape, witness [X_0^2,X_1], bit-2112 functional,
fingerprint 0998513c045145e5) is corroborated with an independent
layout and fresh randomness. Two new findings, both benign:
(a) the code's commutator convention (a.b.a^-1.b^-1) differs in
degree 4 from tower.tex ([g,h] = g^-1.h^-1.g.h), but the difference
lies in I4 on every R2 slot (168/168), so models agree mod I4 and
containment is unaffected; D3xD1 brackets agree exactly (C93 S4b is
convention-free); (b) author's `lv_omega` z-term passes degree 3
instead of 2 for the [Y,Z] factor (bug in dead code: omega channels
are vacuous 0/28, so TOTAL is unaffected; corrected formula verified
8/8 here; C140's P6b 12/12 passed by luck, never exercising the
buggy term with high probability). No claim rejected; no corpus
verdict overturned.

## 1. Thirty-relator 41-cap presentation (traced, proved as cited)

S = {p1,p2,q1,q2,r1,r2} (primes above 2,3,5) and Sigma = S + {v1,v2}
(tw:base(d), read). The 8 local relators rho_nu (2 real squares,
4 tame, 2 dyadic Demuskin) have the initials of tw:local-initials;
tw:complete-global-presentation (read: H^2 bound 7 via Br(X)[2],
seven independent initials, Nakayama) gives R = normal closure of
the 7 relators in (i) (Sigma minus p1); tw:any-seven is the same
for any seven. tw:GB-presentation (read) then gives N_B = normal
closure of 30 elements: (i) 7 + (ii) 6x2 dyadic (x^2,[x,y],[x,z],
[[y,z],z],z^4,[y,z]^2; y^2 replaced by r via the coefficient-one
spanning argument, ker(G_Q2->D) by the other six) + (iii) 8 tame
squares + (iv) 3 Frobenius fourth powers; N_B in D2, rho_p1 in N_B
via R. Count: 21 quadrics (7+6+8) + 2 cubics + 7 quartics
(4 dyadic + 3 cap).

41-cap transfer (construction-41cap.md Secs 2-3,6 + check41.py,
read): B, S, G_S, R, (i)-(iii) are unchanged by the cap swap; only
(iv) moves one generator (Frob at 7, vector f7, to Frob at P41[1]).
Cap compatibility verified here: S(P41[1]), S(P41[2]), S(f291),
S(f292) all outside R2 (own lowbit code), so each capped Frobenius
has order exactly 4 in G_B/D3 (D4-depth: (g-1)^4 = g^4-1) and
relative f = 4; v != c1 separation as in the swap review. Fourth
powers lie in D4, so L1/L2/L3 and G/D3 are unchanged; R2/R3/I3 are
identical to the 241 tower; I4 differs only in one quartic initial
(P41[1] for f7) with rank recomputed 963 here.

## 2. H2 exhaustion (C126 proof screened; conclusion relied on + probed)

Statement (C126-g4-lower-bound.md, relied on as checked corpus):
R4 = I4 + span_28(corr_s(T'_true)), dim R4 in [963,991].
The proof was screened step by step; no errors found. Load-bearing
steps and their status here:
- Fbar = F/D5 finite; D4/D5 central exponent 2; D3 abelian mod D5;
  [D3,D2] = 1; [D2,D2] in D4 (filtration facts per tower.tex as
  cited by C93/C126; consequences verified computationally: D3
  additivity 10/10, [D2,D2]_4 = bracket 20/20, D2 inverse 10/10,
  quartic invariance 10/10, cubic-conjugate formula 10/10).
- Inverses differ by I4 (quadrics via (R2)^[2]; D3/D4 elements
  square to 1); even-exponent combining via the pairing
  rho^g.rho^h = rho^2.[rho,g].[rho,h] mod D5 (tower, gr4-equal
  10/10 here).
- Gr2 forces even quadric occurrences (R2 independence 21,
  re-verified); subleading (rho)_3 cancels by even multiplicity.
- Gr3 is a 170 -> 142 syzygy via ([A,B])_3 = [(A)_2,V_B] exactly
  for A in D2 (20/20 here; B_2/B_3 cancel). Kernel 28-dim, all
  verify; brackets span 140, cubics add 2 (independent), so every
  kernel vector has D = 0 (omega vacuous 0/28): cubic degree-4
  unknowns t_j never contribute to R4/I4. All 21 Qnames occur.
- Gr4: f = x.u reduction ([rho,u] in [R2,L2] folded to I4,
  756/756 re-verified; [[rho,x],u] = 1) and [a,bc] induction
  (identity exact under the tower convention 6/6 here; double
  brackets in [[R2,L1],L1] in I4) give [rho_i,f] = Sum a_l s_il
  mod I4 with fixed s_il. Falsification probes with GROUP-LIKE
  conjugators (f = x.u, (u)_2 in L2; non-Lie (f)_2 would escape
  [R2,L2] and is outside the proof's scope since f sits in
  Fbar): reduction 12/12 tower + 12/12 author; syzygy lifts with
  random higher-part conjugators stay in corr + I4 (8/8, gr3
  still vanishes); r_stand reduction 6/6. No counterexample.
- psi: F2^170 -> L4/I4 linearity; both inclusions
  (R4/I4 = psi(kernel), dim <= 28). Fiber-dependence correctly
  scoped to the count.

## 3. H3 affinity and higher-input cancellation (verified)

corr_s = model_s + LV_s(T') holds EXACTLY for the 24 non-p2
syzygies (fresh-seed A2 24/24 with random full-L2 T', random T3
U', random T4) and mod I4 at the 4 p2 syzygies via the K repair
(S2 below). Mechanisms, each derived and tested:
- No cross in deg-4: syzygy-word factors lie in D3, so
  (w)_4 = Sum (factors)_4 (D3 additivity 10/10).
- No T'^2: deg-3 parts see inputs' deg <= 2 linearly
  (T'.T' is deg 4); T' additivity (vanishing second difference)
  6/6; single-factor affinity via the same trials.
- No U': every word has even occurrence/exponent sums (own word
  algebra: squares 2; comms 2/2 with exp 0/0; tame f:2/t:4or6
  with exp 0/-2or-4, i.e. 1-p, parity-equivalent to the note's
  1+p; omega Y:4/Z:6 exp 0; Wp X:4/Y:4/Z:2 exp 0/2/0; r_stand
  same; [rho,x] doubles rho occurrences + 2, hence even;
  formal r-hat even by (w)_1 = 0 over independent dyadic V's).
  U'.anything has deg >= 4; inverses contribute one U' each
  with exponent-sum-mod-2 coefficient (C116 subtlety, adopted).
  Confirmed by random-U3 exactness.
- No U'': a4 cancels in commutator deg-4 (master has no (A)_4
  term; E-identity + a4-cancel 16/16; random-T4 exactness).
- E-term: ([A,x])_4 = [(A)_3,X] + [(A)_2,X].X (corollary of the
  master with B = (X,0,0,0); master 20/20 + exhaustive-B1 256
  here). E is T'-free since (rho-hat)_2 = recorded initial
  (20/20 non-p2 + r_stand re-verified). Load-bearing: dropping
  E fails 4/6 predictions.
- LV formulas: squares [V,T'], comms [T',V]+[V,T'] (covered by
  A2 over all occurring channels); tame via ARB-base
  perturbation (exact linearization given affinity); r2_cross
  via C116's LV lemma (initial-determined; LV_Wp lists ==
  LV_r lists recomputed; the code equality is tautological per
  C116 S2, the lemma proof via triple commutators + deg-3
  identity was screened); omega chain corrected and verified
  8/8 (author's z-term degree bug scoped in S5).
- LV(R2) = 0: 0/9408 outside I4 (28x16x21), so LV descends to
  the 240-quotient and TOTAL_full240 is well-defined.

## 4. H1a y2-pin (premises verified; pin repaired to K)

Wp = y2^2.[x2,y2].[x2,z2] in N_B (y^2 = [x,y] = [x,z] = 1 in D
per tw:local-two(b), read; D-words lie in N_B by the converse at
tower.tex ~1401-1403, read) and r-hat in N_B (local relation,
(i)); (Wp)_2 = (r-hat)_2 = deminit(2) recomputed; W'' =
Wp.r-hat^-1 in N_B cap D3 with (W'')_3 in R3 = I3 (paper exact
deg-3, tw:retained-quotient(a), read; 41-cap inherits since caps
are D4). (W'')_3 = (Wp)_3 + (r-hat)_3 (D2 factors, no cross;
inverse contributes +(r-hat)_3). U'-absence by even parity (S3).
Control verified: r_stand (same initial, different word) is
affine 4/4 and Wp.r_stand^-1 is T'/U'-free with
K^FSTAND in I3 (W'' in R3).

C129's refutation reconfirmed (lowbit, own layout): LVa is NOT
in I3 and [LVa,X] is outside I4 for all 8 X, so "F_r in K+I3"
and "[Fpin,X] exact mod I4" are FALSE for TRUE F_r =
K + LV_r(T'_true) + e (e in I3). Repair to the K basepoint:
per-syzygy offsets v_s (4 p2 syzygies) all lie in TOTAL_full240
(4/4) and in the A-restricted TOTAL by rerun inheritance;
repaired K-model spans 2-dim (A) / 33-dim (full-240), both
subsets of the Fpin models (4/37), and the witness miss
survives (escape 18/18 both involutions, both models).

## 5. Containment, then separator (verified, in that order)

Containment: by H2 (S2) R4(TRUE) = I4 + span_28(corr_s(T'_true));
by repaired H3 (S3-S4) each corr_s(T'_true) = K-model_s +
LV_s(T'_true) mod I4 lies in TOTAL (full-240: LV over all 240
quotient directions, no cut assumed; Fpin-model offsets v_s
absorbed). Hence R4(TRUE) subset TOTAL_full240 for EVERY T',
with no H1b (y1-cut). Commutator-convention precision (new):
the code uses a.b.a^-1.b^-1 while tower.tex/C126/C93 use
a^-1.b^-1.a.b; the two agree in gr3 and for D3xD1 in gr4
(10/10: ([w,g])_4 = [(w)_3,V_g] both, so C93 S4b is
convention-free), and differ for D2xD1 by [[r,X],X]-type terms
in [[R2,L1],L1] subset I4 (168/168 R2 slots, R3/R4-free), so
tower-models and author-models agree mod I4 and containment
is unaffected. [a,bc] as stated holds tower-exactly (6/6);
it fails author-exactly, but no code path uses it.

Separator (checked only after containment): ad3 rank 18/18 mod
I4 for c1 and c2; escape-dim vs TOTAL_full240 18/18 both
(Fpin and K); witness L3-row 1 = [X_0^2,X_1] (in L3, nonzero
mod I3) misses both TOTALs for both involutions; 192/288
witness rows each; [R3,c] in I4 (340/340) so the map factors
through gr3. Author-layout functional (bit 2112, wit row 1)
and fingerprint 0998513c045145e5 reproduced by rerunning
`total_margin.py` (exit 0; basis-dependent values, own-layout
analogues verified). A-restricted numbers (TOTAL 6 = 4+2+0,
bit 2177, c150066198ceb819) reproduced by rerunning
`robust_defect.py` (exit 0).

## 6. New findings (benign; verdicts stand)

- Commutator-convention gap (precision, no repair needed):
  earlier H2/H3 checks verified the master/E/[a,bc] either
  without naming the convention or with the author's
  convention, while C126/C93 use tower.tex. Difference
  characterized here (D2xD1 diff in I4 on R2 slots; D3xD1
  exact agreement); all enclosure conclusions hold under
  either convention. Cite models mod I4.
- `lv_omega` z-term degree bug (author dead code, no repair
  needed): `robust_defect.py` passes degree 3 for the [Y,Z]
  factor (should be 2). Benign because omega slots are
  vacuous (0/28 kernel vectors use them, basis-independent):
  `lv_omega` never contributes to corr_s/TOTAL. Corrected
  formula verified 8/8 here. C140's P6b "12/12" is weak (a
  random-lift test hitting the buggy z-term with only ~1.5
  expected hits; plausibly vacuous) but its verdicts
  (E-fix, TOTAL, miss) do not depend on it. No corpus entry
  cites `lv_omega` values (C127's "omega slots included" was
  already corrected to vacuous by C141).
- Falsification probes found no counterexample: arbitrary
  group-like conjugates (D2/D3/D4 parts), higher-part
  syzygy conjugators, and r_stand controls all land in
  corr + I4 as H2 predicts. Non-group-like (non-Lie (f)_2)
  conjugators CAN escape [R2,L2]; that is outside H2's scope
  (conjugators live in Fbar) and is recorded as a scope
  boundary, not a gap.

## 7. What was checked (inputs and versions)

- `c161_containment_check.py` (exit 0, ALL PASS 76 checks,
  system python3, seed 161): P1 ranks/foldings/caps (lowbit +
  highbit cross-checks); P2 kernel 28/omega-vacuity/p2-4/
  21-names; P3 trip identities (master 20/20 + B1-256,
  deg-3 20/20, E+a4 16/16, [D2,D2] 20/20, D3-add 10/10,
  cubic 10/10, quartic 10/10, D2-inverse 10/10, pairing
  tower 10/10, [a,bc] tower 6/6); P3b conventions (D3xD1
  10/10, R2-slot diff in I4 168/168, R3/R4-free); P4 word
  parity (8 words + inheritance); P5 full-240 rebuild
  ((rho)_2 20/20, (Wp)_2/rstand_2, LVa/[LVa,X], Fpin 4 /
  K 2 models, LV_Wp==LV_r lists, Ssel 15, LV(R2) 9408,
  TOTAL 37/33 + subset, v_s 4/4, ad3/escape/witness/[R3,c]);
  P6 H3 (A2 24/24, additivity 6/6, E 4/6 fail w/o, omega
  8/8 corrected, r_stand 4/4 + K^FSTAND in I3); P7 H2
  (reduction tower+author 12/12 each, higher-part 8/8,
  r_stand 6/6, 30-census).
- Reran author's `total_margin.py` (TOTAL 6 + escape 18 +
  full-240 37 + escape 18/18 + bit 2112 +
  0998513c045145e5), `robust_defect.py` (I4 963, model 4,
  kerM 214, LV(R2) 0/9408, TOTAL 6, ad3 18, wit 1, bit
  2177, c150066198ceb819), `validate_chain.py` (A2/B/C),
  `collection_check.py` (D1-D5), `no_c4.py` (diag + g4
  premises), `margin_replay.py` (middle/estimated ends):
  all exit 0 as claimed; tracked certs byte-identical
  after rerun.
- Read: the note + C127 review; bundle/support/efix/h1free/
  robust/collection notes + C129/C140/C141/C142/C144/C148
  corpus entries; C126 H2 proof (screened) + C116 H1a
  premises/corpus (LV lemma proof screened; LV_Wp==LV_r
  code equality acknowledged tautological per C116 S2);
  tower.tex tw:base(d), tw:local-groups(b)(c), tw:local-two,
  tw:local-generators/table/relators, tw:local-forms,
  tw:complete-global-presentation + tw:any-seven,
  tw:GB/basic/presentation, tw:quadratic-layer,
  tw:retained-quotient(a), D-word converse ~1401-1403;
  construction-41cap.md + check41.py + review-41cap.md
  (swap scope); C93 S4a/S4b (application + convention
  check, lemmas cited).
- NOT re-checked here (relied on as checked corpus or
  rerun): the y1-cut 214 machinery (M rank 26, kerM 214,
  T0, TOTAL_214 = 6 breakdown) beyond rerun (C116/C127/
  C129 own it; not needed for the full-240 defect);
  nine-in-I3 + formal 27->8 counts (C116/C148); C86 Lemma
  D transfer + margin-table internals beyond application
  scoping and replay rerun (C127/C142); analytic-input
  certification (R4; certified tier fails regardless);
  41-cap GB infinitude proof (hypothesis, same scoping as
  C86/C127); filtration opennesses/meet = 1 (cited via
  C93/C126); PARI/local degree-2 data.

## 8. Use

Cite R4(TRUE) subset TOTAL_full240 (37-dim Fpin / 33-dim
repaired K, H1b-free) and the uniform [s,iota] defect over
all of (L2/R2)^16 as verified (conditional on the cited
paper degree <= 3 exactness + checked C126/C116/C93 links).
Cite the full-240 separator (ad3 18/18, witness [X_0^2,X_1],
bit 2112, 0998513c045145e5) as corroborated. Cite H2's
R4 = I4 + span_28 from C126 (this entry corroborates its
computational premises and probes its reduction; it does
not replace the proof). Do not cite Fpin-basepoint
exactness ("F_r in Fpin+I3", H3 "exactly" at p2 slots);
use K mod I3 with v_s in TOTAL. Do not cite `lv_omega`
values from author code (degree bug; vacuous channels).
Do not drop the infinitude-hypothesis and uncertified-input
qualifications on the chain to fields (C86 Lemma D) and
margin (C62/R4).
