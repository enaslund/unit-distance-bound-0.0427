# C127 check: R5 uniform-defect conditional chain (defect -> quotient -> fields -> margin)

Lane C127, 2026-10-06. Source note (reviewed):
`research/2026-10-muse-involution-class/notes/reviewed/R5-uniform-defect.md` §§3-4 (checked at the
ready version).
Requested focus: general.
Check code: `research/2026-10-muse-involution-class/code/C127/c127_uniform_defect_check.py` PART6
(margin replay, stdlib fractions, exit 0); §§1-2 computations verified
in `research/2026-10-muse-involution-class/corpus/C127-uniform-defect-computation.md`.
Reran `research/2026-10-muse-involution-class/code/R5/margin_replay.py` (exit 0, matches C86).

Verdict: §§3-4 VERIFIED AS CONDITIONAL (no error in the chain logic;
all links either verified elsewhere or precisely flagged as open).
IF H1 (C116 verified) + H2 (no-c4 §2, PENDING) + H3 (C127 computation
verified) + C93 §4a/§4b + C86 Lemma D (+ 41-cap infinitude hypothesis)
hold, THEN Q of order 2^50 with |cl| >= 2^16, tower fields of every
2-power degree m >= 2^50 with N_iota >= 2^16, and M > 0 middle/estimated
at delta = 0.043172 (conditional exponent 1.043172; certified still
fails). No certification claimed; none established here.

## 1. Uniform defect (conditional on H1+H2+H3)

Assume: (H1) T'_true in A, the y1-cut 214-affine space (genuine-lift §4,
VERIFIED by C116 `C116-fiber-cut-26.md`); (H2) R4(TRUE) = I4 +
span_s(corr_s(T'_true)) (no-c4 §2, PENDING its own review, not checked
here); (H3) corr_s = model_s + LV_s(T') (exact 24/24, mod-I4 for rho_p2;
VERIFIED in the C127 computation file).

Then R4(TRUE) subset TOTAL (linear-algebra containment proved in the
computation file §4). The §1 witnesses give, for lifts s in D3 of
s-bar = [X_0^2,X_1] mod R3 (nonzero mod R3, verified) and both
involutions: [s,iota_j] in D4 with ([s,iota_j])_4 = [s-bar,i-bar]
exactly (C93 §4b, cited), and [s-bar,i-bar] outside TOTAL hence outside
R4(TRUE), so [s,iota_j] in D4 \\ D5 — uniformly over A with no knowledge
of TRUE beyond A. (Full-240 37-dim miss makes H1b unnecessary a
fortiori; that strengthening belongs to `R5-defect-h1free.md`.)

## 2. Quotient and fields (cited lemmas; hypotheses match)

- C93 §4a (cited, verified): V with D5 subset V subset D4, [D4:V] = 2,
  V/D5 missing [s,iota_1]_4 exists (nonzero class in the F2-space gr4;
  V normal since D4/D5 central, open since D5 open). Then Q = GB/V has
  order 2^49 x 2 = 2^50 with |cl_Q(iota_1)| >= 2^16. Hypotheses match:
  [s,iota_1] in D4 \\ D5 supplied by §1 uniformly.
- C86 Lemma D (cited, verified): given V open normal V subset D4 and Q
  with |cl| >= 2^16, for every 2-power m >= |Q| = 2^50 there is open
  normal U subset V of index m (center series; uses GB infinitude),
  K = Fix(U) has H = Gal(K/B) mapping onto Q, N_iota >= 2^16, with U
  subset V subset D3 (local structure), gr1 separation, i-bar1 !=
  i-bar2, rd preserved. Hypotheses match (V subset D4). ADDITIONAL
  HYPOTHESIS (as in C86): 41-cap GB infinitude (construction record;
  paper tw:infinite covers the 241 tower; the 41-cap analogue is used
  only as a hypothesis here, same scoping as C86 §3c/§5).

## 3. Margin consequence (conditional; numbers re-verified)

Assume §1-§2 chain (hence N_iota >= 2^16). Then theta*_new = 1/2 -
2^-18 applies to the tower sequence. At delta = 0.043172 with Gaussian
profiles, on C62's checked enclosures (M(theta*) + slope.2^-18,
slope_lo > 0, exact rational intervals recomputed independently):

- certified: M(theta*_new) ~ -1.091304e-5, M(1/2) < 0: FAIL both ends.
- middle: M(theta*_new) >= +4.26958e-7 (C86 +4.270e-7), M(1/2) > 0:
  uniform inf > 0 on [theta*_new,1/2) (affine, slope > 0, both ends).
- estimated: M(theta*_new) >= +1.686958e-6 (C86 +1.687e-6), M(1/2) > 0:
  uniform inf > 0 likewise.
- theta*_new above C62 zeros by 6.834e-7 / 2.700e-6; M(1/2)
  recomputation consistent with C62's table (-8.53e-6/+2.81e-6/+4.07e-6).

Hence the conditional exponent 1.043172 on middle/estimated analytic
inputs (headline 1.043171 as stated), NOT certified (certified baseline
M(1/2) < 0 fixed per C86). Analytic-input certification for middle/
estimated is owned by other lanes (R4); no slack claimed here.

## 4. Dependency ledger (exact)

Verified links: H1 y1-cut (C116); H3 affinity (C127 computation);
C93 §4a defect->quotient + §4b bracket exactness; C86 Lemma D transfer
(+ infinitude hypothesis) and §1 margin table; C62 margin accounting;
margin replay numbers (C127 PART6 + author margin_replay.py, both match
C86). OPEN: H2 R4-exhaustion (no-c4 §2, pending review); 41-cap
infinitude (hypothesis, same as C86); certified analytic witness (R4;
certified fails regardless). The note's "pending margin replay and
independent review of the three R5 links" is accurate with H1 now
verified: remaining are H2 review (+ replay acceptance, supplied here)
and this note's review (supplied here).

## 5. What was checked (inputs and versions)

- Recomputed margin intervals from C62's enclosures with stdlib
  Fractions (PART6): theta*_new - theta* = 2^-18, M(new) = M(*)
  + slope.2^-18, M(1/2) = M(*) + slope.2^-17 consistency, positivity/
  negativity per tier, theta*_new above zeros. All match C86/margin
  replay to quoted digits.
- Read C93 §4a/§4b and C86 Lemmas C/D + §1 in corpus; checked each
  hypothesis against the defect output (D4\\D5 membership, V shape,
  order count, centralizer count, V subset D4/D3 inclusions, 2-power
  divisibility, affinity/uniform-inf argument). No re-proof of the
  cited lemmas; application verified.
- Read tower.tex tw:infinite/tw:field-family existence lines
  (1492: infinitude used for large-index U); confirmed 41-cap
  infinitude is hypothesis-only here (C86 scoping adopted).
- NOT checked: H2 (deferred to no-c4 reviewer); any new quotient search;
  analytic-input certification; 41-cap infinitude proof.

## 6. Use

Cite as CONDITIONAL: IF H2 verifies (+ cited lemmas + infinitude
hypothesis), THEN uniform [s,iota] defect over A, Q 2^50 with class
>= 2^16, tower fields every 2-power m >= 2^50 with N_iota >= 2^16, and
M > 0 middle/estimated at delta = 0.043172 (exponent 1.043172;
certified fails). Do not cite as an unconditional improvement; do not
drop the H2/infinitude/uncertified-input qualifications. For the verified
computational core see `C127-uniform-defect-computation.md`.
