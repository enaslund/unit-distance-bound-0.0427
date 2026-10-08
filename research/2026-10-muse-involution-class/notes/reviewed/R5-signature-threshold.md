# R5: conjugacy-class threshold at δ = 0.043172 and the class-growth missing fact

Status: ready for checking. Code: `research/2026-10-muse-involution-class/code/R5/involution_audit.py`
(both-involution ranks, exit 0). Depends on reviewed `R5-margin-accounting.md`
(C62: zeros, both-endpoint framework), `C62-r5-margin-accounting-check.md`,
`C16-lie45-upper-bounds.md` (syzygy obstruction), `tower.tex` (tw:retained-quotient,
tw:field-family, tw:GB-presentation), `papers/0.04273/certificates/lie241.py`,
`lie241c.py`. Profile grids parked per coordinator direction.

## 1. Threshold table: N_ι needed per baseline at δ = 0.043172 (proved)

With θ*(N) = 1/2 − 1/(4N) and the C62-verified margin zeros
θ_0 = 0.50001365 / 0.4999955019 / 0.4999934851 (certified / middle /
estimated), M > 0 needs θ*(N) > θ_0 strictly (C62 precision note:
uniform positivity is strict at both endpoints):

| baseline | θ_0 | N_min | 2^15 = 32768 | 2^16 = 65536 |
|---|---|---|---|---|
| certified 0.0422764 | 0.50001365 > 1/2 | impossible | M < 0 on all of [θ*, 1/2] | same |
| middle 0.04226506 | 0.4999955019 | 55580 | θ* short by 3.1e-6 | θ* exceeds by 6.8e-7, M ≈ +4.3e-7 |
| estimated 0.0422638 | 0.4999934851 | 38374 | θ* short by 1.1e-6 | θ* exceeds by 2.7e-6, M ≈ +1.7e-6 |

N_min uses the quoted zero + 5e-11 (rounding cover); all gaps exceed rounding
by 4+ orders. So: one doubling 2^15 → 2^16 closes middle and estimated at
δ = 0.043172 with Gaussian profiles; the certified baseline is unreachable by
signature improvement alone (M(1/2) < 0, slope > 0). The 41-cap tower shares
Ḡ_B, both classes, and θ* with the 3-cap tower (cap swap changes only (iv)
quartics in D_4, so R_2, R_3 are unaffected; C16 §2).

## 2. Both-involution audit in Ḡ_B (computed)

Reran the lie241.py/lie241c.py rank computations for c2 as well as c1
(`involution_audit.py`, PASS): ad(c): L1 → gr2 has rank 7 and ad(c): gr2 → gr3
has rank 8 for BOTH c1 and c2, so both classes have exactly 2^15 elements
(rank-7 kernel is the line through c̄ since [c̄, c̄] = 0; class 2^(7+8) by the
centralizer count in tw:retained-quotient(c)). Separation (d) already covers
both (rerun: True). Switching the fixed field to ι_2 gives no gain; the
retained quotient is exhausted for both involutions.

## 3. Quotient-extension lemma (proved)

Let G_B be the 41-cap tower group, π: G_B → Ḡ_B the retained quotient.
Central extensions never grow the class: if D_5 ⊂ V ⊂ D_4 then K = D_4/V is
central in Q = G_B/V, ι_1 acts trivially on K, and |cl_Q(ι_1)| = 2^15 still.

Lemma. If [D_4G_B, ι_1] ≠ 1, there is an open normal V with D_6 ⊂ V ⊂ D_5,
[D_5:V] = 2, such that Q = G_B/V has |cl_Q(ι_1)| ≥ 2^16; moreover for every
2-power m ≥ |Q| there is K/B of degree m through Q with N_ι ≥ 2^16, and the
full tw:field-family conclusion holds with θ* = 1/2 − 2^−18.

Proof. G_B acts trivially on D_5/D_6 (as [D_5,D_1] ⊂ D_6), so any D_6 ⊂ V ⊂ D_5
is normal; choose V missing some [g, ι_1] ∉ D_6 (exists by hypothesis, V open
since D_6 is). Then ι_1 acts nontrivially on J = D_4/V = ker(Q → Ḡ_B), so
|C_J(ι_1)| ≤ |J|/2 (nontrivial involution action: |J : C_J| = |{[k,ι_1]}| ≥ 2),
and |C_Q(ι_1)| = |π(C_Q(ι_1))|·|C_J(ι_1)| ≤ 2^34·|J|/2 gives
|cl_Q(ι_1)| = |Q|/|C_Q(ι_1)| ≥ 2^16. For the fields: the tw:field-family
existence proof works verbatim with D_4 replaced by V (V open normal of
2-power index; the exact-index step needs |Q| | m). Local structure
(U ⊂ V ⊂ D_3), separation (d) (gr_1 data), b ≥ 1, and rd are preserved. ∎

A weaker variant (V ⊃ D_5 exploiting an incompletely lifting centralizer)
would need exact R_4 and lift analysis; it is not pursued (same obstruction).

## 4. The missing fact and why it is blocked (proved reduction; sourced obstruction)

[D_4G_B, ι_1] ≠ 1 ⟺ the bracket [·, ῑ_1]: gr_4G_B → gr_5G_B is nonzero, a finite
exact linear-algebra question given exact R_4, R_5. It is BLOCKED on
unrecorded relator lifts (C16 §3, confirmed applicable): the R_3 spanning set
has 28 syzygies whose degree-4 corrections need the subleading parts of the
relators, but the 7 global relators ρ_ν are specified via local class field
theory, not as explicit words (only quadratic initials via Hilbert symbols are
recorded). No exact-R_4/R_5 computation, p-quotient computation, or exhibited
quotient Q of order ≥ 2^50 is possible from recorded data.

What would change the answer, in order of concreteness: (i) explicit ρ_ν words
to degree 5 (then exact R_4, R_5 and the bracket rank are bounded linear
algebra in T_5, dim 8^5 = 32768); (ii) an exhibited finite quotient Q ⊃ Ḡ_B
with |cl_Q(ι_1)| ≥ 2^16; (iii) a structural theorem that ι_1 cannot
centralize D_4G_B (not in hand; infinitude alone does not imply class growth).

## 5. Scope and checking

Threshold arithmetic recomputed from C62's verified zeros (this note §1);
audit script exit 0; no new quotient found; no certification (no slack on the
certified baseline under any signature bound). Profile-grid work (BB screen
orientation lattice, higher Bernstein, s-optimization) parked, not exhausted.

## C86 review (2026-10-06)

Reviewer: C86 lane. Reran `involution_audit.py` (exit 0, AUDIT PASS) and
`lie241c.py` (R3 rank 142) with /tmp/C62-venv/bin/python; wrote stdlib-only
`research/2026-10-muse-involution-class/code/C86/c86_threshold_check.py` (exit 0: cover, N_min
55580/38374, gaps, M bounds, certified impossibility) and
`research/2026-10-muse-involution-class/code/C86/c86_involution_ranks.py` (exit 0: R2 21, R3
142/28 syzygies, (7,8) for both c1 and c2, separation both True). Read
tower.tex tw:GB-presentation/tw:retained-quotient/tw:field-family,
tw:vector-table/tw:relators, C62, C16, and construction-41cap.md §§2-3.

Extracted to corpus (source at
`research/2026-10-muse-involution-class/notes/reviewed/R5-signature-threshold.md`):

- `research/2026-10-muse-involution-class/corpus/C86-r5-signature-threshold-check.md`: §1 verified
  (threshold table, certified impossibility, conditional 2^16 close of
  middle/estimated; cover costs 1 on middle, safe direction); §2 verified
  (both classes exactly 2^15, separation for both, c2 count transfer);
  cap-swap invariance of Gbar/R2/R3; repaired Lemmas A (exact depth 5,
  strengthened hypothesis), B (arbitrary depth, weak hypothesis), C
  (central inequality), D (field transfer given a suitable quotient);
  sourced obstruction (unrecorded lifts block exact R4/R5).

Rejected or unresolved:

- §3 "central extensions never grow the class ... = 2^15 still": REFUTED
  as stated (inequality reversed; D8-over-C2xC2 counterexample with
  trivial kernel action grows 1 → 2). Repaired to |cl_Q| ≥ 2^15 with
  equality iff full centralizer lifting (Lemma C).
- §3 Lemma proof ("choose V missing [g,ι1] ∉ D6, exists by hypothesis"):
  INVALID (hypothesis gives ≠ 1, not ∉ D6; conclusion also needs g5 ≥ 1,
  open per C16). Repaired to Lemma A (hypothesis [D4,ι1] ⊄ D6) and
  Lemma B (hypothesis [D4,ι1] ≠ 1, arbitrary depth k ≥ 5).
- §4 "⟺": REFUTED as an equivalence (only bracket-nonzero ⇒
  noncommutation holds). Missing fact split into depth-5 (Lemma A) and
  arbitrary-depth (Lemma B) sufficient conditions; neither is necessary
  (lifting-defect route open in principle).
- §4 universal "no quotient of order ≥ 2^50 possible from recorded data":
  kept as an assessed obstruction, not a proved impossibility.
- Precision: Lemma D gives the 41-cap analogue of tw:field-family (41-cap
  local table), not tw:field-family's table verbatim.

No previously accepted corpus result was overturned. Ready
`R5-quotient-repair.md` §1 (same §3 repair, pending its own check) was
skimmed for overlap only; the repairs above are independent. A flaw in the
as-stated §3/§4 does not rule out the signature route; Lemmas A/B/D keep
exactly what a future quotient or lift computation would need to supply.
