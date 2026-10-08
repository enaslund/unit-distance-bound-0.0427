# C129 check of R5-robust-test (PASS verified; Fpin/K basepoint bug found benign and repaired)

Lane C129, 2026-10-06. Source note (reviewed):
`research/2026-10-muse-involution-class/notes/reviewed/R5-robust-test.md` (checked at the ready
version; the note moved by this review).
Requested focus: general. Check code (stdlib only, no numpy):
`research/2026-10-muse-involution-class/code/C129/c129_robust_test_check.py` (exit 0, ALL PASS
with system python3).
Reran `research/2026-10-muse-involution-class/code/R5/robust_defect.py`
(PYTHONPATH=/tmp/pylibs, exit 0): every number reproduced
(I4=963, syzygy 28, model 4, ker 214, LV(R2) 0/9408, TOTAL 6,
ad3 18/18, witness row 1, bit 2177, fingerprint c150066198ceb819).

Verdict: the note's CONCLUSIONS STAND, with one repaired bug.
The reported PASS (TOTAL 6-dim, ad3 escape, witness, functional)
is VERIFIED as computed. The §2 affinity conclusion (corr affine
in T', U'/U'' absent) is VERIFIED, but the in-note proof is
incomplete as written (gaps listed in §4, filled by this check).
BUG (repaired, benign): the rho_p2-slot model basepoint Fpin
should be K (off by LVa, see §2); H3-as-stated ("exactly") is
therefore FALSE at the 4 p2 syzygies, but enclosure survives
because all four offsets land in TOTAL (verified), and the
repaired K-basepoint TOTAL (2-dim) still misses the witness.
H1 (214-cut) is now CHECKED (C116 landed; corroborated here).
H2 (R4-exhaustion) stays CONDITIONAL (open R5 notes). Repaired
H3 is VERIFIED. So the uniform-defect PASS is now conditional
on H2 only (+ checked C93/C86/C62 links).

No previously accepted corpus result is overturned. C116's
formal pin is clarified (§2, pointer paragraph added there);
its 27→8 count and all C116 verdicts stand.

## 1. Verified computations (independently reproduced)

Own implementation: little-endian tensors, lowbit elimination,
V table parsed from lie241.py source text, own dict-Magnus and
trip algebra, fresh randomness (seed 129045). Agreement:

- L2=36, R2=21, free L3=168, I3=142, free L4=1044, I4=963 (P0).
- [I3,L1] ⊂ I4 (0 outside) and [R2,L2] ⊂ I4 (0/756) (P0).
- Syzygy kernel 28-dim over 170 R3 rows, all verify; 21 Q2
  identified to unique labels (P1).
- y1bar^2 uses 9 initials incl. rho_p2; (Wp)_2 = deminit(2);
  tame Wp-perturbation equals r2_cross in 36/36 directions
  (non-vacuous; trip/dict K match) (P2-P3).
- Fiber-map rank 26 mod I3; M R2-kernel 0/336; C1+K
  consistent; quot subset 15; ker M1 = 214; T0 found (P3).
  (Fourth implementation of the C116-verified 240→214 cut.)
- LV(R2) outside I4: 0/9408 (P4).
- TOTAL_old 6-dim mod I4, breakdown model 4 / +T0 6 / +ker 6
  (i.e. +2/+0 increments) (P4).
- ad3 rank 18/18 mod I4 for c1 AND c2; witness L3-row 1
  ([X_0^2,X_1]) misses TOTAL for both; escape-dim 18/18 both;
  separating functional exists (author-layout bit 2177
  confirmed by rerun; own-layout analogue verified) (P5).
- Occurrence/exponent-sum parity even for all 10 word types
  (P6; tame per-lift sums are 0 and 1−p, both even — the
  note's "1+p" is a parity-equivalent slip).
- U'-absence in deg 3: 44/44 trials; (w_s)_4 U'/T4
  independence 48/48 (non-p2) + 8/8 (p2 via r_stand);
  T'-additivity 24/24; exact model+LV prediction 48/48
  (non-p2, K-model = old model there) + 8/8 (p2 via
  r_stand with Fstand-adjusted model); E-terms load-bearing
  (prediction without E fails 18/24); master ([A,B])_4
  formula 10/10; E-identity 6/6 (P2, P6).
- Random T' in A (T0 + ker-combo + R2 part) gives all 28
  corr in TOTAL_new, 3/3 trials (P8).

## 2. Fpin/K basepoint bug: statement, proof, repair

At rho_p2 syzygy slots the code models TRUE (r̂)_3 as
Fpin + LV_r(T') with Fpin = K + LVa (LVa = r2_cross-formula
at ARB2). The correct basepoint is K mod I3. Proof: with
W'' = Wp·r̂^{−1} ∈ N_B ∩ D3 (C116-verified premises) and
R3 = I3 (paper), (W'')_3 = (Wp)_3 + F_r ∈ I3 (D2 factors,
no cross; inverse contributes +(r̂)_3 since (r̂)_1 = 0),
and (Wp)_3 = K + LV_r(T'_true) (A1-affinity, C116 LV
lemma), so TRUE F_r = K + LV_r(T'_true) + e, e ∈ I3.
Hence the model is off by LVa at p2 slots. Verified:
LVa ∉ I3; [LVa,X] ∉ I4 for all 8 X; r_stand control
Fstand = K mod I3 (in I3: True) but ≠ Fpin mod I3 (P6-P7).
C116's pin "Fformal ∈ Fpin+I3" is the same constraint
stated for the double-counted object Fformal = P_r(ARB2)
+ LVa (equivalently P_r(ARB2) ∈ K+I3); it is true as a
formal constraint, but Fpin is NOT the TRUE (r̂)_3
basepoint — the code's use double-counts LV_r(ARB2).
(Clarification paragraph added to
`research/2026-10-muse-involution-class/corpus/C116-fiber-cut-26.md` §3; C116's
27→8 count and verdicts unchanged.)

Benign + repaired (P7): the per-syzygy offsets
v_s = Σ_{p2 slots}[LVa,X] (s = 5, 6, 9, 11) all lie in
TOTAL_old (4/4; basis-independent by linearity), so
R4(TRUE) ⊂ TOTAL_old still holds and the reported PASS
is sound. Repaired K-basepoint TOTAL_new is 2-dim
(model 2, +T0/+ker add 0), TOTAL_new ⊂ TOTAL_old, and
the miss survives (escape 18/18 both involutions,
witness row 1, separating functional exists). H3-as-stated
("corr_s = model_s + LV_s(T') exactly") is REFUTED at p2
slots (off by v_s + I4); repaired H3 (K basepoint, exact
mod I4 via [I3,L1] ⊂ I4) is VERIFIED.

Sibling flag: `research/2026-10-muse-involution-class/code/R5/total_margin.py`
reuses RD.model_corrs, hence the same Fpin basepoint; its
enclosure likewise survives by the subset argument
(v_s ∈ TOTAL_214 ⊂ TOTAL_full240), but its 37-dim number
is left to its own checker.

## 3. Test logic (§1) and citations (proved / faithful)

Sound-for-miss argument VERIFIED: under H1 (TRUE T' ∈ A),
H2 (R4 = I4 + span_28 corr_s), repaired H3 (affine corr
+ LV(R2) = 0), every TRUE corr_s lies in TOTAL, so
R4(TRUE) ⊂ TOTAL and a witness outside TOTAL is outside
R4(TRUE). With C93 §4b ([s,ι]_4 = [s̄,ī] exact,
lift-independent) this gives [s,ι] ∈ D4∖D5, and C93 §4a
gives Q = GB/V of order 2^50 with |cl_Q(ι_1)| ≥ 2^16.
The "countermodel shows insufficiency only" scoping is
correct. C93/C86/C62 uses are faithful: C93 §4a/§4b
proved; C86 §1 numbers (+4.270e-7 middle, +1.687e-6
estimated at δ = 0.043172, certified fails) and Lemma D
as cited; C62 enclosures as cited. The computation is in
41-cap gauge; the inferred group-theoretic conclusion is
gauge-independent as stated. Status update: the note's
"C116/C117" conditions are discharged for H1 (C116
review_complete; D2-completeness not needed for
soundness here).

## 4. Gaps in the note as written (filled here, not fatal)

- §2 argues U'-absence for (word)_3 only; corr_s is
  degree 4 and needs the assembly step (U' enters deg-4
  only via U'-free (ρ̂)_3 / chain-rule terms) — verified
  by 48/48 + 8/8 independence trials, not by the text.
- T'²-absence ("factors in D3") addresses cross-factor
  terms; within-factor affinity verified by 24/24
  additivity + 48/48 exact-prediction trials.
- U''-absence and E-terms are not mentioned in §2 though
  needed for "TOTAL (T'-only) is complete" — verified by
  T4-independence trials and 18/24 no-E failures.
- H3's parenthetical omits the basepoint/pin subtlety
  (§2 above); repaired and verified here.
- "Tame ρ 1+p even" should read 1−p (parity identical).

## 5. Hypothesis ledger after this review

- H1 (TRUE T' ∈ A, 214-cut): CHECKED (C116; P3 corroborates).
- H2 (R4 = I4 + span_28): CONDITIONAL — ready
  `R5-no-c4-g4bound.md` §2 + `R5-defect-support.md` §1 /
  `R5-collection-check.md`, none yet reviewed. Pieces
  corroborated here ([I3,L1] ⊂ I4, [R2,L2] ⊂ I4,
  master/E formulas) do not imply exhaustion.
- H3 (affine corr): VERIFIED as repaired (§§1-2).
- Chain to N_ι ≥ 2^16 / conditional 1.043172 on
  middle/estimated inputs: conditional on H2 only
  (+ checked links; certified still fails).

## 6. What was checked (inputs and versions)

- `c129_robust_test_check.py` (exit 0, ALL asserts pass):
  P0 ranks/foldings; P1 kernel/qlabel; P2 model/master/E;
  P3 full y1-cut rebuild + non-vacuous Wp perturbation;
  P4 LV(R2)/TOTAL old+new; P5 ad3/witness/functional/escape;
  P6 parity + fresh-random affinity/U'/E trials + r_stand
  control; P7 Fpin/K analysis + repair; P8 enclosure trials.
  V parsed from lie241.py source; P41[1] =
  [0,0,1,1,1,0,0,0] (C3 value, as cited).
- Reran author's `robust_defect.py` (exit 0): all outputs
  incl. bit 2177 and fingerprint c150066198ceb819.
- Read: the note; `R5-uniform-defect.md`, `R5-no-c4-g4bound.md`,
  `R5-defect-efix.md`, `R5-defect-support.md`,
  `R5-defect-bundle.md`, `R5-defect-h1free.md`,
  `R5-collection-check.md` (ready); reviewed
  `R5-genuine-lift.md`; corpus C93/C99/C107/C116/C117/C86/C62
  entries (citations rechecked against those files);
  `genuine_lift.py`, `validate_chain.py`,
  `collection_check.py`, `total_margin.py` (Fpin-use survey).
- Proved by hand in review (this file §2-§3): K-basepoint
  theorem via W'', Fpin double-count diagnosis, test
  soundness with repaired H3.
- NOT checked: H2 exhaustion proof; full-240 37-dim
  number (sibling note); margin replay (sibling note;
  C86 §1 numbers already checked); any per-layer lower
  bound on g4/g5 beyond the conditional chain.

## 7. Use

Cite the robust-test PASS as verified-computed (TOTAL 6,
ad3 18/18 escape, witness [X_0^2,X_1], functional) and
the repaired K-basepoint TOTAL (2-dim, miss survives) as
proved. Cite corr-affinity (U'/U''/T'²) as verified.
Cite the uniform defect ⇒ Q(2^50, ≥2^16) step as
conditional on H2 (R4-exhaustion) only. Do not cite H3
exactness with the Fpin basepoint; use K mod I3 (Fpin =
K + LVa double-counts). Do not cite any g4 bound from
this note.
