# R5: stabilized H1a+H2+H3 bundle — complete collection, cancellation, functional

Status: ready for checking (primary bundle for C127/C129 inclusion
reviews; supersedes the H1–H3 exposition of prior notes, whose
computations stand as evidence). Code: `total_margin.py`,
`robust_defect.py`, `validate_chain.py`, `collection_check.py` (all
exit 0); tracked certs `defect_cert_full240.json` (fingerprint
0998513c045145e5; the space actually used) and `defect_cert.json`
(A-restricted refinement). Depends on paper (tw:GB, tw:relators,
tw:quadratic-layer, tw:retained-quotient(a), tw:local-two(b),
tw:kummer-field), `C16` (folding, syzygy frame), `C93` (§4a/§4b),
`C89` (D2-word method). Transfer (C86 Lemma D) and analytic witness
(C62/R4) separate, not redone here.

## 0. Fixed setup

F free pro-2 on X̂ lifting Kummer; π: F → GB fixed-unknown; ARB
section ŵ (genuine products); TRUE ĝ = ŵd, d ∈ D2; T' = (d)_2 ∈ L2,
U' = (d)_3 ∈ T3, U'' = (d)_4. Quotients L2/R2 per lift (15 × 16).
Computed lemma L0: LV(R2) = 0 (0/9408) — variation descends.

## 1. H1a: y2-pin (proved)

Wp = ŷ2²[x̂2,ŷ2][x̂2,ẑ2] ∈ N_B (ŷ2² by D-cap y² = 1; comms are cap
relators); r̂ ∈ N_B (local relation); (Wp)_2 = (r̂)_2 = deminit(2)
(recorded). W'' = Wp·r̂⁻¹ ∈ N_B ∩ D3, so (W'')_3 ∈ R3 = I3 (paper
exact deg-3). (W'')_3 = (Wp)_3 + (r̂)_3 (D2-factors, no cross) = K +
F_r: LV_Wp = LV_r verified as maps (same initial), U' absent (Wp
sums X:4/Y:4/Z:2, all even; r̂ formal 0; occurrence-parity §3).
Hence F_r ∈
K + I3; model-term [Fpin,X_i], Fpin = K + LV_r(ARB2), exact mod I4
(I3/ebar parts land in [I3,L1] ⊂ I4; nine-in-I3).

## 2. H2: R4-exhaustion with complete collection (proved)

w ∈ N_B ∩ D4 = ∏(n_k^{g_k})^{e_k} (30 gens; pairing
ρ^gρ^h = ρ²[ρ,g][ρ,h] mod D5). (i) Deg-2: quadric
exponents 0 mod 2 (R2 rank 21); even parts give squares with
initials (R2)^{[2]} ⊂ I4. (ii) Deg-3: ([A,B])_3 = [(A)_2,V_B]
EXACTLY for A ∈ D2 (B_2/B_3-terms cancel; derived) — so (w)_3 is a
relation among the 170 free-gen R3-rows with f from gr1-exponents:
(w)_3 = 0 ⇔ 28-dim syzygy (170 → 142). (iii) Deg-4: master formula
([A,B])_4 = [(A)_3,V_B] + [(A)_2,(B)_2] + [(A)_2,V_B]V_B (derived;
D1-verified exact): [ρ,g] reduces to free-gen [ρ̂,x̂] mod I4
([ρ,d]-pieces in [R2,L2] ⊂ I4 by folding, D2-verified 756/756;
u-collection in [[R2,L1],L1] ⊂ I4); cubics (ω^g)_4 = (ω)_4 +
[(ω)_3,V_g] with bracket an R4base-row combination; quartics
(Q^g)_4 = (Q)_4 ∈ I4; D3-factor collection none; [D3,D2] in D5.
Hence R4 = I4 + span_28(corr_s(T'_true)); E-terms ([r,X]X) included
in corr_s from the start (T'-free, recorded).

## 3. H3: affinity and higher-input cancellation (proved + computed)

corr_s = model_s + LV_s(T') EXACTLY: factors in D3 ⇒ no cross in
deg-4; T'² absent (deg-3 parts see inputs' deg ≤ 2 linearly; (ω̂)_4
chain has (W1)_2 fixed); E T'-free (a_2 recorded); U'' absent (a_4
cancels in commutator deg-4); U' absent by occurrence-parity —
exponent-sums even for every word (table: real/cap squares 2;
cap comms 2/2; tame ρ f:2/t:1+p (4/6); r̂ formal (0,0,0); ω̂
Y:4/Z:6; Wp X:4/Y:4/Z:2; syzygy words inherited even). LV formulas
per type (squares/comms/tame-perturb/
r2_cross/ω-chain) + L0. Random trials (validate A–C, collection D)
are VALIDATION EVIDENCE for these symbolic arguments, not replacements.

## 4. Certificate in the space used (computed)

TOTAL_full240 = I4 + span(model) + LV(full 240) = 37-dim mod I4;
ad3 escape-dim 18/18 both involutions (full images disjoint).
Separating functional λ*_full = bit-2112 of TOTAL-residue:
λ*|_TOTAL = 0, λ*([X_0²,X_1],ī) = 1 both cases — value from recorded
data; no acquisition. A-restricted cert (6-dim, bit-2177) is a
refinement needing H1b; the full-240 cert stands without it.

## 5. Defect and dependencies (conditional)

[s,ι_j] ∈ D4 ∖ D5 (s lifting s̄) uniformly: R4(TRUE) ⊂ TOTAL_full240
by H2+H3, witness outside by §4. Then C93 §4a (Q 2^50, ≥2^16) →
C86 Lemma D (fields) → C62 replay (prior notes; separate). Open:
review of H1a/H2/H3 proofs + computations; transfer; witness.

## 6. Falsification routes

H1a: W'' ∉ N or (W'')_2 ≠ 0 (recheck D-cap/r̂); R3 ≠ I3 (paper).
H2: D4-content outside 28-corrs (exhibit word; collection cases
above locate it). H3: LV formula error (finite-difference catches;
A2/B cover all channels). Functional: rerun regenerator.

## C148 review (2026-10-06; review_complete)

Checker: C148. Code: `research/2026-10-muse-involution-class/code/C148/c148_bundle_check.py`
(stdlib logic + author tensor imports, exit 0, ALL PASS 65 checks; log
`c148_bundle_check.log`), independent lowbit elimination, fresh seed
148, own trip4 + own word algebra. Reran author's `total_margin.py`,
`robust_defect.py`, `validate_chain.py`, `collection_check.py` (all
exit 0, all outputs + both fingerprints reproduced; git status clean).

Verdict: COMPUTATIONS VERIFIED; H2 CONCLUSION PROVED (via C126; sketch
screened, no errors); H1a/H3 CONCLUSIONS VERIFIED WITH THE STANDING
C129 REPAIR (Fpin wording false as stated, repaired to K); §4 cert
VERIFIED; §5 VERIFIED AS CONDITIONAL. No new refutation; nothing
rejected outright.

Extracted to corpus:
- All sections -> `research/2026-10-muse-involution-class/corpus/C148-defect-bundle-check.md`
  (§0 L0 0/9408; §1 premises verified, (Wp)_2 = deminit, LV-cancel via
  C116 lemma, Fpin "exact mod I4" refuted + repaired with v_s 4/4 in
  TOTAL, K-model 2/33, miss survives; §2 sketch correct, statement
  proved by C126, deg-3 identity 10/10 + master/E/a4 10/10 fresh-seed,
  foldings 756/756; §3 parity table verified as occurrence counts with
  mod-2 lemma, "EXACTLY" refuted + repaired; §4 full240 37 + escape
  18/18 + wit1 + 192/288 + bit 2112 + fingerprint 0998513c045145e5;
  §5 conditional defect with infinitude/uncertified-input scoping).

Repaired (inherited from C129, reconfirmed lowbit here):
- §1 "F_r in K+I3" + "[Fpin,X] exact mod I4" is FALSE for TRUE F_r
  (TRUE F_r = K+LV_r(T')+e; LVa not in I3, [LVa,X] 8/8 outside I4).
  Repaired to K basepoint; offsets v_s (s=5,6,9,11) land in both
  TOTALs (4/4), K-model miss survives.
- §3 "corr_s EXACTLY" with Fpin is FALSE at the 4 p2 syzygies (off by
  v_s+I4); repaired H3 (K, exact 24/24 + mod I4 at p2) verified.
- §1/§3 "exponent-sums" labels occurrence counts; harmless by the
  mod-2 lemma (verified: all even under either reading).
- §1 "LV_Wp = LV_r verified" as code is tautological (same formula
  twice, per C116 §2); conclusion stands via C116's LV lemma.

Unresolved (outside this note): transfer lemmas + margin replay beyond
application scoping (C127/C142 verified); analytic-input certification
(R4); 41-cap infinitude proof (hypothesis, same scoping as C86/C127).
C126's proof relied on as checked corpus (premises re-verified here).
