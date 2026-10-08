# R5: finite-quotient repair, mildness exclusion, Schmidt assessment, concrete local path

Status: ready for checking. Code: `research/2026-10-muse-involution-class/code/R5/liftdefect.py`
((i)-(iv), exit 0). Depends on ready `R5-signature-threshold.md` (§3 repaired
below; that note left stable for C86), ready `R5-bracket45.md`,
`C16-lie45-upper-bounds.md`, `tower.tex`, archived
`literature_references/schmidt_2002_two_and_infinity_arXiv-math0008246.pdf`
(Schmidt 2000). No mildness/Anick/Labute source in repo or archive (searched).

## 1. Repair to signature-threshold §3 (proved)

Three fixes; the threshold table (§1) and audit (§2) of that note stand.

(a) Exact-depth vs general. [D4,ι1] ≠ 1 does NOT locate a witness in D5/D6:
x ∈ [D4,ι1] may sit at any depth k ≥ 5. General-depth lemma: if
x = [g,ι1] ∈ Dk ∖ D{k+1} (k ≥ 5), take V open normal with D{k+1} ⊂ V ⊂ Dk
missing x (hyperplane in Dk/D{k+1}; normal since GB acts trivially on it).
Then ι1 acts nontrivially on J = D4/V, |CJ(ι1)| ≤ |J|/2, and Q = GB/V has
|clQ(ι1)| ≥ 2^16 with |Q| = 2^{Sk+1} (Sk = 49+g4+...+g{k-1}). The note's
Q (order 2^{50+g4}) is the k = 5 case, hypothesis [D4,ι1] ⊄ D6.

(b) Central kernel gives inequality, not equality. For D5 ⊂ V ⊂ D4,
|CQ(ι1)| = |π(CQ(ι1))|·|J| ≤ 2^34·|J| hence |clQ(ι1)| ≥ 2^15; equality needs
surjective centralizer lifting π(CQ) = C_Ḡ, which was unjustified. Strict >
is the eligible lifting-defect case (see §4).

(c) Necessary and sufficient. clH(φ(ι1)) = φ(clGB(ι1)) for every quotient
H = φ(GB) (H = φ(GB), so conjugates lift). Hence Nι ≥ 2^16 for some tower
H ⟺ |clGB(ι1)| ≥ 2^16 ⟺ [GB,ι1] ∩ D4 ∋ x ≠ 1 (sufficiency: separate 2^16
conjugates by open normal U, intersect with D4, exact-index adjust).
Eligible witnesses: depth-k D4-witness (a) or lifting defect
([s,ι1] ∈ D4 ∖ 1, s centralizing mod D4).

## 2. Mildness excluded by counting (computed; Labute citation flagged)

Minimal-relation count (computed (iv)): [R2,L1] has rank 140 in L3, the 2
cubics add 2 (R3 = 142), so with 21 quadrics + 7 quartics the 30-relator
capped presentation has inert series P(t) = 1−8t+21t²+2t³+7t⁴. Its reciprocal
has a0..a5 = 1, 8, 43, 174, 466, −68 (exact integer arithmetic). Mildness
(Labute: HS = 1/P) would force a5 = dim ≥ 0. So GB is NOT mild, subject to
sourcing Labute's HS formula (no source in repo/archive; flagged, not cited).
Remark: uncapped GΣ (7 rels, 1/(1−8t+7t²), all coeffs > 0) is
series-consistent — the CAPS (7 → 30 relations) kill mildness. No Anick
computation needed; initials-only exactness is dead.

## 3. Schmidt assessment: no route to centralizers for capped GB (proved gaps)

Schmidt 2000 Thm 1 (cd GS(2) ≤ 2 for S ∩ SR = ∅): cohomological dimension
does not see centers — the full-lifting assumption C(ι1) = π⁻¹(C_Ḡ) (ι1
central in open C(ι1)) yields no cd-contradiction (cd ≤ 2 groups may have
centers). No cd-route to [GB,ι1] ∩ D4 ≠ 1 identified.

Thm 2' (free product G(BT|BS0) = C2∗C2 at real places): describes the
UNCAPPED kernel; caps cut it via N ∩ (C2∗C2), which carries the
t-dependence (TRUE-section positions). Missing-hypothesis reformulation:
order(ι1ι2) ≥ 32 in GB ⟹ (ι1ι2)^16 ∈ D5 ∖ 1 (depth-5 witness) — needs
positions (t-blocked). Maximal-S-ramified applicability alone insufficient,
as foreseen.

Lemma 3.1 (involution-generated groups): needs H²(−,Q2/Z2) = 0 on both
sides; unavailable for GB (no cyclotomic Z2 inside BG: GB^ab = F2^8 finite,
so weak-Leopoldt-via-cyclotomic fails). Inapplicable.

Side lemma (proved): μ16 ⊂ BG but μ32 ∉ BG (every normal generator of N
acts trivially on μ16: ker(Gpj→D) fixes L2 ∋ μ16; τ̂² inertia-trivial;
φ̂²: Frob² = μ^81 = μ at q,r (N = 9,25); Frob⁴ = 1 mod 16 at t0 (N = 49),
t1,t2 (N = 29), P41[1] (N ≡ 9); while Frob29^4 ↦ μ^{13⁴}, 13⁴ ≡ 17 mod 32).
The cyclotomic quotient C2×C4 factors through GB/D3 (D3 = 1) so its class
has ≤ 2^15: cyclotomic route excluded for growth.

## 4. Concrete path: lifting defect via exact R4 (proved reduction; computed preliminaries; feasibility assessed)

Lifting-defect lemma (proved): given exact R4 and s ∈ GB with
[s,ι1] ∈ D4 ∖ D5, V with D5 ⊂ V ⊂ D4, [D4:V] = 2, V/D5 missing [s,ι1]4 gives
Q of order 2^50 with |clQ(ι1)| ≥ 2^16 (s ∉ CQ halves |π(CQ)| ≤ 2^33). NO R5
needed — strictly cheaper than D5-cutting.

D3-sources (clean): s ∈ D3 has [s,ι1]4 = [s̄3,ῑ1] exactly (all
lift-corrections land in [D3,D2] ⊂ D5). So D3-defect ⟺ ad3 ≠ 0. Computed
(ii): [L3,c] mod I4 has rank 18 for c1 AND c2 — compatible (not robustly
zero); R4 decides.

D2-sources: [u2,ι̂] ∈ D4 is AUTOMATIC for ū ∈ ker(ad2) (computed (i): ker
7-dim), since ([u2,ι̂])3 = [ū,ῑ1] in gr3 by definition of the Lie bracket
([D2,D2] ⊂ D4, so (ι̂)2 does not enter degree 3). [u2,ι̂]4 via mechanical
Magnus + (ι̂)2-fiber (robust test mod R4+[ū,R2]).

R4 needs (proved): 210-dim fresh local Artin-degree-2 data — tame τ̂φ̂×8
(120) + dyadic x̂ŷẑ×6 (90). Real positions = 0 (Gv = C2, D2 = 1, so TRUE
(ι̂)2 ∈ R2, harmless fiber). Frob positions irrelevant (quartics exact).
Demuskin ē folds into dyadic positions (no independent ē). All 21 ρi occur
in the 28 syzygies (computed (iii)) → no minimization.

Feasibility (assessed, not computed): FEASIBLE but FRESH — explicit local
fields/uniformizers/D3-quotients (tame order 16, dyadic order 256),
PARI-assisted norm computations (~14 local degree-2 computations + global
assembly). Reconstruction from RECORDED data is IMPOSSIBLE (positions
unconstrained: R2/R3 lift-independent; R5-bracket45 §2).

Conditional chain: positions → R4 → s (ad3 or D2-robust) → V → Q (2^50) →
K (m ≥ 2^50) → Nι ≥ 2^16 → θ* = 1/2−2^−18 → M > 0 middle+estimated
(threshold table, conditional on stated C-inputs). Profile grids parked.

## 5. Scope and disclosures

reduce_mod latent bug: early-return reduction leaves smaller pivot bits
(non-canonical residues). bracket45 unaffected (uses only zero-tests, which
are sound, + rank_basis): rerun confirms 56/56. liftdefect fixed to full
reduction; (i) now matches audited rank 8. C3's script shares the pattern
but uses only zero-tests (sound). Labute HS formula flagged for sourcing;
mildness exclusion is conditional on it. No certification (no slack).

## C93 review (2026-10-06)

Reviewer: C93 lane. Reran `research/2026-10-muse-involution-class/code/R5/liftdefect.py` (exit 0:
R3 142, [R2,L1] 140 with cubics +2, 28 syzygies with all 21 rho_i, ad2
8/ker 7, [L3,c] mod I4 18/18) and `research/2026-10-muse-involution-class/code/R5/bracket45.py`
(exit 0: 56/56) with /tmp/C62-venv/bin/python; wrote stdlib-only
`research/2026-10-muse-involution-class/code/C93/c93_quotient_repair_check.py` (exit 0: capped
a0..a5, q>=3 threshold, uncapped positivity, 13^4=17 mod 32,
3^2=5^2=9 mod 16). Read tower.tex filtration/local/GB/quadratic/
retained/field-family/base, construction-41cap.md Secs 2-3, C86/C16,
R5-bracket45, C3 reduce_mod uses, and Schmidt 2000 via pdftotext
(Thm 1, Thm 2/2', Lemma 3.1).

Extracted to corpus (source at
`research/2026-10-muse-involution-class/notes/reviewed/R5-quotient-repair.md`):

- `research/2026-10-muse-involution-class/corpus/C93-quotient-repair-check.md`: Sec 1(a)(b)
  verified (general-depth lemma with |Q|=2^{Sk+1}; central inequality
  with equality iff full lifting; agree with C86 A-C); Sec 1(c)
  verified with set/subgroup fix (single-commutator equivalence
  N>=2^16 iff |cl_GB|>=2^16 iff Cset cap D4 != {1}); Sec 2 numbers
  verified (140/+2, a5=-68, q>=3 threshold, uncapped >0) as computed;
  Sec 3 order>=32 => D4-witness proved, no-cyclotomic-Z2 proved,
  no-cd-route / Thm2'-capped / Lemma-3.1-inapplicable kept as
  assessments; Sec 4 lifting-defect lemma proved (exact R4, Q 2^50,
  no R5), D3 reduction + 18/18 and D2 automatic-D4 + ker 7 verified
  as compatible preliminaries, fiber 15/Frob-irrelevance/all-21-rho_i
  verified; Sec 5 code repair verified (zero-test soundness, 56/56,
  rank 8, C3 sound).

Rejected or unresolved:

- Sec 1(c) "[GB,iota1]" subgroup reading: NOT proved (needs single
  commutator, not product); repaired to Cset reading (proved).
- Sec 2 "GB NOT mild" / "initials-only exactness dead": CONDITIONAL,
  not proved (Labute HS unsourced as flagged, plus minimality/
  presentation-invariance gap: only quadrics+cubics independence
  computed; quartic minimality not tied to criterion).
- Sec 3 Lemma 3.1 premise "GB^ab = F2^8 finite": REJECTED (unproved;
  =F2^8 likely false given Frob order 4); repaired to proved
  no-cyclotomic-Z2 (finite D at 2), keeping H^2-route inapplicability
  as assessment, not proved H^2 != 0.
- Sec 3 side lemma "mu16 subset BG": REFUTED (Nq=3, Nr=5 degree one
  per tw:base(c), not 9,25; phi^2 acts as mu^9 != mu on mu16; note
  checked 4th power mu^81 instead of square). mu32 not subset BG
  HOLDS (a fortiori + Frob29 13^4=17 mod 32 verified). "C2xC4 via
  GB/D3 (D3=1)" REJECTED as garbled (no such quotient; abelian class
  1 trivially).
- Sec 4 "R4 needs (proved) 210-dim": CONDITIONAL (real positions=0
  unproved: D2(C2)=1 does not give (iota)_2 in R2, and c1^2/c2^2 do
  occur in syzygies; ebar folding unproved vs R5-bracket45 8-dim;
  no-minimization implication assessment). Safe proved count stays
  240+8; 210 only if real/ebar gaps close. D2 Magnus + robust test:
  sketch, unresolved (no formula supplied).
- Sec 4 "Reconstruction from RECORDED data IMPOSSIBLE": kept as
  assessed obstruction (R2/R3 lift-independent), not a proved
  impossibility theorem.

No previously accepted corpus result was overturned. A flaw in an
as-stated claim does not rule out the approach; Secs 1/4 keep exactly
what a future R4/lift computation would need to supply.
