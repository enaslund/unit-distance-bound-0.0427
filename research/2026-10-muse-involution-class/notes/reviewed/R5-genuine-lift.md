# R5: one genuine arithmetic lift datum — coproduct fix, paradox resolution, 26-dim fiber cut

Status: ready for checking. Code: `research/2026-10-muse-involution-class/code/R5/genuine_lift.py`
(exit 0). Depends on `tower.tex` (tw:GB, tw:GB-presentation,
tw:local-two(b), tw:local-groups, tw:retained-quotient(a) exact degree 3,
line 1401-1403 D-word converse), `C89-r5-bracket45-check.md` (maps/ranks
adopted, paradox repaired), `C93-quotient-repair-check.md` (Cset, Frob),
`C96-tame-pilot-check.md` (T3 model, census), `C99-r5-exact-r4-check.md`
(model rank). Supersedes `compat_gap.py` §§2-3 (convention/reduction fixes
below); `R5-compatibility-gap.md` retraction stands.

## 1. Coproduct convention; tensors vs graded classes (proved + computed)

X_i = x̂_i − 1 has ΔX_i = X_i⊗1 + 1⊗X_i + X_i⊗X_i (x̂_i group-like), so
1+V is group-like iff the off-diagonal defect
Σ_{i<j}v_iv_j(X_i⊗X_j+X_j⊗X_i) vanishes, iff wt(V) ≤ 1 — verified
19/19 recorded vectors. Single-bit 1+X_i IS the free generator
(genuine); multi-bit 1+V is not (genuine word: ∏(1+X_i)^{v_i}).
This corrects compat_gap §2 and the C99 §3 side remark as stated
("V ≠ 0", primitive convention); main verdicts unaffected.
Homogeneous Magnus tensors (ĝ)_n vs graded classes: only elements of
D_n have degree-n parts in gr_n; D1 elements' higher parts are tensors.

## 2. C89 §3 paradox resolved as non-genuine-base artifact (computed)

The minimal paradox word used 1+(Y+Z) (multi-bit, non-group). Rebuilt
genuinely (ŶẐ = (1+Y)(1+Z)): (w)_1 = (w)_2 = 0 with (w)_3 ∈ L3 —
no paradox. The non-genuine version reproduces C89's D3-nonLie tensor.
Consequence: C89's fiber MAPS stand (linearizations see only degree-1
base data — re-verified by ARB-base perturbation), but pure-base
CONSTANTS were ill-formed; §4 recomputes them genuinely.

## 3. Fiber-rank reconciliation (computed)

compat_gap's canonical-reduction bug (early return leaves lead bits)
inflated residue ranks. Fixed: fiber rows ⊂ L4 and I4 ⊂ L4 verified
(rank 1044 both), TRUE ranks mod I4 = rank(I4+fibers) − 963 are
51 (y1), 71 (z1), 57 (p31), 56 (c1) — all ≤ dim L4/I4 = 81.
C99's 148-193 reproduction used the same non-canonical residue method
(absolute ranks incl. I4 leftovers), not ranks in L4/I4. Fibers still
genuinely matter (all > 0).

## 4. One arithmetic fiber cut 240 → 214 + formal-r3 pin (proved + computed)

Gauge: ARB monomials ŵ_g = ∏X̂_i^{v_i} in Kummer basis; TRUE ĝ = ŵ_g·d_g,
T'_g = (d_g)_2 ∈ L2/R2 (15 dims × 16 lifts = 240). Local normalization:
Lemma (b) triple with y² = 1 in realized D = Gal(L2/Q2); tame word
shapes per Lemma (b). Map: decomposition → D-cap (tw:GB; every D-word
in lifts lies in N_B, tower.tex 1401-1403) + local relation r̂ ∈ N_B
with recorded initial; R3 = I3 exact (tw:retained-quotient(a)).

U'-lemma (proved): degree-3 fibers U' enter (w)_3 only as Σe_liftU'_lift
(exponent-sums mod 2); all words below have even exponent-sums
(squares 2, comms 0, tame ρ: 1+p even, r̂ formal-D2: 0), so U' is
absent and (w')_3 = C + M(T') exactly (T'² is degree 4).

y1-word (ŷ1² ∈ N_B; S(ȳ1) = 9 initials incl. rho_p2, reproduced) plus
y2-word (Wp = Y²[X,Y][X,Z] ∈ N_B at p2; LV_Wp = LV_r verified, so
fibers cancel) eliminate the unknown formal r3: fiber-only constraint
C1 + K + M(T') ∈ I3 with M of rank 26 mod I3 (R2-kernel 0/336) and
C1+K verified consistent — a 26-dim affine cut, fibers 240 → 214,
unconditional beyond paper degree ≤ 3. Formal pin: Fformal ∈ Fpin+I3
with pushforward injective (27), image rank 19 mod I3, Fpin consistent —
formal-r3 cut 27 → 8 (ebar-Lie free; nine nested in I3 re-verified).

## 5. Scope

R4 needs positions-3 too (U' enters degree 4), so this cut constrains
but does not yet give exact R4; C93's degree-4 lifting-defect test
awaits R4. Next: further D2-words (ρ_p1-word, tame words) for more
cuts, or direct fiber acquisition. No certification (no slack).

## C116 review (2026-10-06; review_complete)

Checker: C116. Code: `research/2026-10-muse-involution-class/code/C116/c116_genuine_lift_check.py`
(stdlib only, exit 0, system python3; little-endian tensors, lowbit
elimination, trip-algebra words, V parsed from lie241.py source).
Reran author's `research/2026-10-muse-involution-class/code/R5/genuine_lift.py`
(PYTHONPATH=/tmp/pylibs, exit 0): all outputs reproduced.

Verdict: ALL SECTIONS VERIFIED (proved + computed). No claim rejected;
nothing unresolved. Two of the note's justifications were replaced by
stronger ones during review (LV lemma proof; LVa = known2 derivation);
all numbers and conclusions confirmed as stated.

Extracted to corpus:
- §1 coproduct fix -> `research/2026-10-muse-involution-class/corpus/C116-coproduct-fix.md`
  (strengthened to all 256 V). Also corrects the same "V != 0"
  side remarks in C99 §3 and C107 §2(d) (correction paragraphs
  added there; their main verdicts unaffected).
- §2 paradox resolution + C89 maps stand ->
  `research/2026-10-muse-involution-class/corpus/C116-paradox-resolution.md` (non-genuine
  tensor matches C89's {012,021,102,201} exactly; tame ARB-base
  == pure-base in all 288 columns). C89 §3 quarantine lifted for
  genuine words.
- §§3-4 fiber cut + formal pin ->
  `research/2026-10-muse-involution-class/corpus/C116-fiber-cut-26.md` (§3 ranks 51/71/57/56
  corroborate C107; 26-dim cut 240 -> 214 unconditional beyond
  paper degree <= 3; formal pin 27 -> 8 with derivation supplied;
  tower premises tw:GB/tw:GB-presentation/tw:local-two(b)/
  tw:local-groups/tw:retained-quotient(a)/lines 1401-1403 all
  read and confirmed as cited).
- §5 scope accepted as assessed (no new claims).

Rejected/unresolved: none. Constraint status for lift fibers is now
"26 dims constrained" (this avenue), superseding C89's "UNRESOLVED";
remaining 214 + 8 dims and exact R4 stay open. Do not cite any g4
bound from this note.

