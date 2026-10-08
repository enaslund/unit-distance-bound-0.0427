# R5: uniform D3-lifting defect over the 214-space (conditional chain to 1.043172)

Status: ready for checking. Code: `research/2026-10-muse-involution-class/code/R5/robust_defect.py`
(exit 0). Depends on ready `R5-genuine-lift.md` §4 (y1-cut: T'_true in
A), ready `R5-no-c4-g4bound.md` §2 (R4 = I4 + span(28)), `C93`
(§4a defect→quotient, §4b bracket exactness), `C86` (Lemma D transfer,
§1 margin table), `C62` (margin accounting), `C107` (§3 ranks; §2(d)
nit flagged in §5). No certification claimed; positive candidate
pending margin replay and independent review of the three R5 links.

## 1. TOTAL is 24-dim; ad3 escapes it (computed)

R4(T') = I4 + span_s(corr_s(T')) with corr_s exactly affine in T'
(§2). Over the y1-cut 214-affine space A: TOTAL := I4 + model-span
(4, ARB base, E-corrected) + T0-shift (2) + ker-variation (0 beyond)
= 6-dim mod I4 (E-fix: R5-defect-efix; was 24-dim pre-fix). LV(R2) ⊂
I4 (0/9408): variation well-defined on the 240-quotient. ad3-images
[L3,c1], [L3,c2] have rank 18/18 mod I4 (C93 cross-check) and are NOT
contained in TOTAL: witness L3-row 1 ([X_0²,X_1]) gives [s̄,ī] ∉
TOTAL for BOTH c1 and c2 (residues verified nonzero mod TOTAL-basis).

## 2. LV-exactness (proved in note)

corr_s(T') = model_s + LV_s(T') exactly: no T'² (all syzygy-word
factors lie in D3, so (w)_4 = Σ(factors)_4 with no cross terms;
deg-3 parts are T'²-free), no U' (every lift has even exponent-sum
in every word: squares 2, comms 0, tame ρ 1+p even, r̂ formal 0,
ω̂ 0). LV formulas: squares [V,T'], comms [T',V]+[V,T'], tame via
ARB-base perturbation, r̂ via initial-determined r2_cross, ω̂ via
chain rule; formal-r3 model uses Fpin with ebar-residual in
[I3,L1] ⊂ I4 (nine-in-I3 re-verified).

## 3. Uniform defect and quotient (conditional)

T'_true ∈ A (genuine-lift) and R4(TRUE) = I4 + span_s(corr_s(T'_true))
(no-c4 exhaustion) give R4(TRUE) ⊂ TOTAL. The §1 witnesses give
[s,ι_j] ∈ D4 ∖ D5 for lifts s ∈ D3 of s̄ (both involutions; [s,ι]_4
= [s̄,ī] exact by C93 §4b). By C93 §4a: V (D5 ⊂ V ⊂ D4, [D4:V] = 2)
missing [s,ι_1]_4 yields Q = GB/V of order 2^50 with |cl_Q(ι_1)| ≥
2^16 — uniformly, with no knowledge of TRUE beyond A. By C86 Lemma D:
tower fields K of every 2-power degree m ≥ 2^50 with H = Gal(K/B)
mapping onto Q, N_ι ≥ 2^16, local structure/separation/rd preserved.

## 4. Margin consequence (conditional)

IF §3's chain verifies, THEN by C86 §1 (checked numbers): at
δ = 0.043172 with Gaussian profiles, M ≥ +4.270e-7 (middle) and
M ≥ +1.687e-6 (estimated), uniformly positive — i.e. conditional
exponent 1.043172 on middle/estimated analytic inputs (headline
1.043171). The certified baseline still fails (C86: M(1/2) < 0
fixed); this is NOT a certified improvement. Needs: review of the
three R5 links, margin replay, and (for certification) analytic-input
certification by other lanes.

## 5. Flag: C107 §2(d) wt-1 nit

C107 §2(d) (accepted corpus) states 1+V non-group-like "for V ≠ 0"
(defect V⊗V, primitive convention). Under the group-algebra coproduct
(ΔX_i = X_i⊗1+1⊗X_i+X_i⊗X_i), single-bit 1+X_i = x̂_i IS group-like
(by definition Δ(g) = g⊗g); correct statement: non-group-like iff
wt(V) ≥ 2 (genuine-lift §1, 19/19; C107's own §1 derivation is
convention-independent). Multi-bit conclusions everywhere unaffected.
Suggested repair: "V ≠ 0" → "wt(V) ≥ 2" in C107 §2(d) and its §8 use
note. C107 owns the final call.

## 6. Scope

Decisive for the D3-defect route if verified: defect holds for every
T' ∈ A, so no further fiber acquisition is needed for N_ι ≥ 2^16.
Remaining gaps are exactly: (i) review of genuine-lift §4, no-c4 §2,
this note; (ii) margin replay; (iii) certified analytic inputs.

## C127 review (2026-10-06; review_complete)

Checker: C127. Code: `research/2026-10-muse-involution-class/code/C127/c127_uniform_defect_check.py`
(stdlib only, exit 0, system python3; own tensors/Magnus/trip, V parsed
from lie241.py source, high- AND low-bit eliminations),
`c127_probes.py`, `c127_kervar_probe.py`, `c127_sse1_probe.py` (all exit
0). Reran author's `robust_defect.py`, `validate_chain.py`,
`total_margin.py`, `margin_replay.py`, `collection_check.py`,
`genuine_lift.py` (all exit 0, all outputs reproduced).

Verdict: §§1-2 VERIFIED (computed + proved) with stale-title nit and
rho_p2 mod-I4 precision; §§3-4 VERIFIED AS CONDITIONAL (chain logic
sound; H2 + infinitude + uncertified inputs flagged); §5 flag CONFIRMED
(already corrected by C116). No claim rejected.

Extracted to corpus:
- §§1-2 computation core -> `research/2026-10-muse-involution-class/corpus/C127-uniform-defect-computation.md`
  (TOTAL 6 over A with breakdown 4+2+0, LV(R2)=0/9408, ad3 18/18,
  witness [X_0^2,X_1] miss both with escape 18, E-formula, LV affinity
  exact 24/24 + mod-I4 rho_p2, LV(kerM) in I4 strengthening, Ssel
  independence, full-240 37 + escape 18 corroboration).
- §§3-4 conditional chain -> `research/2026-10-muse-involution-class/corpus/C127-uniform-defect-chain.md`
  (H1+H2+H3 => R4 in TOTAL => [s,iota] defect => Q 2^50 >=2^16 =>
  fields every 2-power m>=2^50 => M>0 middle/estimated at 0.043172,
  exponent 1.043172; certified fails; dependency ledger).
- §5 C107 §2(d) flag confirmed (group-like iff wt<=1, all 256 V) but
  NOT newly extracted: C116 already applied the "wt(V)>=2" correction
  to C107/C99 (`C116-coproduct-fix.md`); this review corroborates.

Rejected/unresolved: nothing rejected. Unresolved (outside this note):
H2 R4-exhaustion (`R5-no-c4-g4bound.md` §2, pending its own review) —
the chain stays conditional on it; 41-cap infinitude (hypothesis, same
scoping as C86); certified analytic witness (R4; certified fails
regardless). Nit: §1 title "24-dim" is stale pre-E-fix; cite 6
(A-restricted) / 37 (full-240).

## Second review by C161 (2026-10-06; review_complete)

Checker: C161. Code: `research/2026-10-muse-involution-class/code/C161/c161_containment_check.py`
(stdlib only, exit 0, system python3, ALL PASS 76 checks; V parsed
from lie241.py source, little-endian tensors, lowbit elimination,
own trip3/trip4 + word algebra, fresh seed 161). Reran author's
`total_margin.py`, `robust_defect.py`, `validate_chain.py`,
`collection_check.py`, `no_c4.py`, `margin_replay.py` (all exit 0,
all outputs + both fingerprints reproduced; git status clean).
Bundle version: corrected bundle `40d08300`; full-240 certificate
`0998513c045145e5`. This is a second-opinion check; the note is not
moved. Requested focus: reconstruct H1a/H2/H3 for the 41-cap
presentation and establish R4 containment before the separator.

Verdict: CONTAINMENT VERIFIED (computed + proved). R4(TRUE) sits in
TOTAL_full240 (37-dim Fpin / 33-dim repaired K) with the standing
C129 Fpin->K repair, so the uniform [s,iota] defect holds with no
y1-cut (H1b-free). Separator corroborated (ad3 18/18, witness
[X_0^2,X_1], bit 2112, 0998513c045145e5). Two new benign findings:
commutator-convention difference (code vs tower.tex) lies in I4 on
R2 slots (168/168), containment unaffected, C93 §4b
convention-free; author's `lv_omega` z-term has a degree bug in
dead code (omega vacuous 0/28), corrected formula verified 8/8.
No claim rejected; no corpus verdict overturned.

Extracted to corpus:
- Everything -> `research/2026-10-muse-involution-class/corpus/C161-containment-second-review.md`
  (30-relator 41-cap trace via tw:complete-global-presentation;
  H2 screening + group-like falsification probes; H3 affinity +
  E/cubic/parity; H1a premises + K repair with v_s 4/4;
  containment-then-separator; convention analysis; lv_omega
  dead-code bug; precise unchecked list).

Rejected/unresolved: nothing rejected. H2's conclusion is relied
on from C126 (proof screened here, no errors; premises re-verified
+ probed, proof not replaced). y1-cut 214 machinery relied on from
C116/C127/C129 + rerun (not rebuilt; unneeded for full-240).
Remains open outside this note (unchanged): 41-cap infinitude
(hypothesis); middle/estimated analytic-input certification (R4;
certified fails regardless); C86 Lemma D transfer beyond
application scoping. Nit recorded: C140's P6b "lv_omega 12/12"
likely never exercised the buggy z-term (random-lift test, ~1.5
expected hits); its verdicts stand (channels vacuous).

