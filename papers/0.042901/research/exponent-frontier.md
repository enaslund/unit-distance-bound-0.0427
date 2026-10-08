# The exponent frontier: why 1.042901 is essentially optimal in-framework, and what 1.05 would need

> **Superseded in part (2026-10-05).** Lead 1 of §11, the dihedral analytic
> refinement, was carried out and taken further in
> [papers/0.043171](../../0.043171/README.md), which certifies exponent
> 1.043171 (the estimates here are about 1.043046 for one D4 quotient and
> 1.04315 for three). This stays within the cap of §3.1: all non-abelian
> refinement gains at most about +0.00029, and the limit analysis there
> ends this design at δ = 0.043196. The paths under /tmp in §§3 and 10-11
> were never part of the repository.

Date: 2026-10-04. Status: **research analysis** (evidence as labeled; parallel-review
synthesis pending but not load-bearing).
Not a theorem: each item below is labeled with its evidence type
(COMPUTED = reproduced numbers, SCAN = optimizer/census search,
STRUCTURAL = proof-sketch argument, HEURISTIC = scaling estimate).
No tracked certificate or manuscript file is affected by this note.

## 1. Bottom line

The 41-cap design (δ = 0.042901, exponent 1.042901) sits at a joint optimum
of the tower method used in this repository (pro-2 tower + quadratic K/F +
norm-one-unit transfer). Every improvement direction examined is either
quantitatively exhausted, blocked by a structural argument, or worth at most
~+0.0003 individually:

- Killing ALL remaining analytic slack gains ≤ +0.000294 (exact, §3).
- All further useful C4 caps combined gain ≤ +0.000752 (hard windows, §3),
  and need Golod–Shafarevich budget that does not exist.
- All geometric slack combined gains ≤ ~1e-8 (§3).
- No other real-quadratic base beats Q(√241) (corrected optimizer scan, §4).
- No complex-cubic or quartic base comes close (discriminant searches, §5).
- Higher-degree K/F, signature changes, odd-p towers, subfield bases, and
  f=1 conditions are each blocked structurally (§§6–9).

Summing every individually-maximal gain (mutually inconsistent miracles)
gives a framework ceiling of δ ≈ 0.0440 (exponent ≈ 1.0440). A no-dyadic
tower lead was investigated and KILLED exactly (§11.0: GS +0.0864, E/B wild
at 2, E ⊄ K incoherence — S ∋ 2 is forced). The target δ = 0.05 needs
+0.0071, roughly 6× beyond all miracles combined; no lead with the right
order of magnitude remains open (residual: hypothetical cubic-Fox caps
+0.00075 + dihedral #1+#2+#3 +0.00025 ≈ +0.0010 combined; subgroup GS
closed negative).

The last within-framework lead examined, a weighted Golod–Shafarevich
criterion for a 4th C4 cap, screens negative: uniform weights are a strict
local minimum and weighted variants are 10–30× worse (§11). No
within-framework lead with material gain remains open.

## 2. Accounting conventions

Margin slope dM/dδ ≈ −24 (certified: margin +5.779e-6 at δ=0.042901,
−1.814e-5 at 0.042902, slope −23.9). So +0.0024 margin ≈ +0.0001 δ, and
δ = 0.05 needs +0.17 margin over the current saturated design.

References: [41-cap note](construction-41cap.md), [cap search](cap-search.md),
[241 construction](../../0.04273/research/construction.md),
[design search](../../0.04273/research/design-search.md).

## 3. Exhaustion bounds (all COMPUTED)

### 3.1 Analytic slack: ≤ +0.000294

C − B_sel(1) = 0.0070444, decomposed (independent recomputation) as
(Y*−B_sel) 0.0048929 (69.5%) + ε·κ∞ 0.0021231 (30.1%) + ε·R 0.0000284.
Even C → B_sel(1) (zero slack) gains 0.0070444/24 = +0.0002936 δ.
Sub-structure: gross completely-split-in-E_B mass = 0.006925 (2× #1's
exact gain; density 1/256; the 0.00688 figure is rounding), offset by
census saving −0.00163; the v=0 tail at N > 10^9 single-handedly
sustains the abscissa optimum near ε = 1/300. Non-abelian refinement
is now CAPPED EXACTLY: every valid tower quotient's net gain is
v0-halving only (f4-floor resolutions telescope exactly vs Δ, f ≥ 8
unresolvable), so all non-abelian gain ≤ v0 mass 0.006925 C ≈
+0.00029 δ (#1 +0.000145 exact, #2 +0.000071 guaranteed gated by
σ-conductors, #3 +0.000036; realistic k=3: δ ≈ 0.04315, absolute:
0.04319; §11.1). AFE lengths are ~10^7–10^8 terms at conductors
~10^11–10^13 (not 10^9/10^17) — engineering, not analysis-blocked. Census extension ≤ 1e-9 δ; abscissa residual
≤ 6e-7 δ. G_B^ab is elementary abelian, so no intermediate abelian step exists.

### 3.2 Further caps: ≤ +0.000752 (and unaffordable)

Hard-window pair profits (1,4) at δ = 0.042901, (log2 − 4δlog p)/4:
29: 0.02883, 41: 0.01397, 47: 0.00811, 53: 0.00296, 59: −0.00164 (negative),
larger p worse. Singles are half (effective (2,4)). Beyond the current
29-pair + 41-single, the only positive additions are completing the 41-pair
(+0.00699), the 47-pair (+0.00811) and the 53-pair (+0.00296): total
+0.01805 margin ≈ +0.000752 δ (shells add ~10%: ≈ +0.00083).
Cappability of all three additions VERIFIED (41-second-prime by check41.py;
47-pair + 53-pair: both split, all four Frob vectors nonzero with S(v)
outside R2 and c1 separated — /tmp/caps/report.md; evaporated: 0).
Cost: 5 more caps ≈ +0.025 GS against slack 0.00211; the 4-cap minimum is
already +0.00288 > 0. So even the cap miracle needs a new infinitude proof.

### 3.3 Geometric slack: ≤ ~1e-8

Full inventory (all quantified): degree-5 archimedean +8.5e-9 δ; 8–10 shells
+2e-9; θ* → 1/2 +2.0e-7 (tower-gated, needs larger class); concentration,
β-scan, k-ranges, Fourier μ all ≤ 2e-10 or exactly zero. Shells are dense in
radial profiles and 8–10 shells match 6 shells to +5e-8 margin, so the
radial-profile gap is closed. Total ≲ 1.1e-8 δ.

## 4. No better real-quadratic base (SCAN)

A corrected optimizer (split-cap options fixed: single-cap-half-profit at
1×c4 vs pair-cap-full-profit at 2×c4; the old model charged 1×c4 for full
profit) was scanned exhaustively over squarefree D ≡ 1 mod 8 to 2600 with
ANY splitting of 3,5 (260 of 261 D; only D = 1 = Q missing, covered by the
Q-optimizer; the prior scan required 3 split and stopped at 74/108).
Result: D = 241 wins at δ_model = 0.042973 with exactly the 41-cap
configuration (S = {2,3,5}, 29-pair + 41-single); next are D = 41
(0.041811), 337/1009 (0.041523), 97 (0.041496). Gap 0.00116 — decisive. D > 2600 loses on root
discriminant alone (each doubling of D costs 0.457·0.5·log2 ≈ 0.158 margin
vs bounded prizes). Small-D alternatives (e.g. D = 17, δ_model = 0.0392)
fail GS with S = {2,3,5} alone (min P_B = +0.215) and the forced
S-expansion costs ~2.4 margin against ~+0.14 base saving.
Model→certificate reconciliation (why no hidden winner): cert margin at
0.042901 (+6e-6) vs model margin there (+24·(0.042973−0.042901) = +0.00173)
gives shells-gain (+0.0049) minus true-ceiling-loss (−0.00662) = −0.00172
net for 241. Alternatives (smaller genus) lose MORE on the true ceiling
(−0.0136 for dim 7) while gaining LESS from shells (smaller finite sum):
their true δ sits ~0.0003+ below model, WIDENING 241's lead. The hard-window
fixed-slack ranking understates the certified gap.

## 5. No better higher-degree base (SEARCH + STRUCTURAL)

### 5.1 The 2-splitting obstruction (STRUCTURAL)

p splits completely in a degree-m field only if m ≤ p (needs m distinct
roots mod p). Hence NO degree ≥ 3 field splits 2 completely; the Q2-based
dyadic theory and dyadic multiplicity of the 241 design are unavailable
above degree 2. Similarly 3 admits at most type (1+1+2) unramified in a
quartic, etc.

### 5.2 Complex cubics (SEARCH)

Best possible shape: 2 of type (1+2) (one Q2 prime reusing D, one Q4 prime
needing new theory), 3 and 5 completely split. PARI sweep over general
cubics found minimal |disc| = 54419 (rd 37.9, margin cost −0.41 vs prize
≤ +0.02): dead. Fields with |disc| ≤ 5000 are covered by the sweep box
(reduced-coefficient bounds) and none qualify; break-even needs |disc| ≤
4250. Smaller-S variants (5 inert etc.) lose more finite profit than they
save in rd. Totally real cubics were already excluded (min disc 413449).

### 5.3 Quartics (SEARCH)

Best shape: r1 = 2, 2 of type (1+1+2), 3 of type (1+1+2), 5 split.
Box sweeps to ±20 (309 fields) give minimal disc = 2455515 (rd 39.6):
dead. Break-even needs disc ≤ 57700; 1.05 needs disc ≤ ~10^4 at density
~1/2304 (S4) — no field below 10^5 found. Biquadratic (V4) fields are
catastrophic (discriminants multiply: rd ~ 10^5+). Cyclic (C4) fields
cannot split 2,3,5 (conductor argument).

### 5.4 Higher degrees and splitting economy (HEURISTIC + STRUCTURAL)

Harvesting a prize prime p via base splitting costs ≥ 0.457·0.5·log(D*_p)
root discriminant per independent condition against prize ≤ 0.09 (for 7)
— net negative in every computed case, across C2, multiquadratic
(explicitly catastrophic: rd ~ 10^8 for five conditions), S3-sextic, and
D4-quartic examples. Quadratic C2 has the optimal splitting economy
(smallest Galois group), and 241 is its optimum (§4).

### 5.5 Subfield bases B(√α) (STRUCTURAL: condition counting)

A quadratic subfield of the 241 tower splitting all of S needs 14 linear
conditions on dim-8 V (dyadic: 3+3 since Q2^×/squares ≅ C2^3; tame: 2×4):
impossible. Best feasible (split dyadic + two prize primes) loses ~0.45
finite profit (tame primes go inert, (2,2) → (2,4)) against ≤ +0.13 prizes.
Non-S-unit α pays ramification rd exceeding any prize.

## 6. No better K/F step (STRUCTURAL)

### 6.1 Higher-degree K/F loses (relative-dimension liability)

The margin's rd rate is (rel.dim/d)·ℓ and arch rate (rel.dim/d)·archrate
(read off the mass-density/class-number computation: quadratic gives
−(1/2−δ)ℓ with rel.dim/d = 1/2). Since ℓ = 5.656 > archrate = 1.911,
relative dimension is a net liability (−3.75 per unit). Biquadratic K/F
([K:F] = 4, rel.dim/d = 3/2) triples the liability: net −3.75 margin vs
quadratic. Quadratic K/F is optimal; the finite/arch functional changes
(normalized densities) are second-order.

### 6.2 Real place required (theorem, quoted dependencies)

geo:transfer/fw:transfer assume (G1) b ≥ 1; at b = 0 four steps break
(signs/roots of unity, regulator comparison, capitulation kernel, and the
planar projection itself — the compact coordinate IS the plane). Imaginary
bases (F totally real, θ = 0) lose 0.31/degree arch against ≤ +0.18
conceivable gains. Split-real variants lose on GS cost (optimizer:
δ = 0.0397 all-split-real).

### 6.3 Odd-p towers collapse (STRUCTURAL: involution)

In a pro-p group with p odd, complex conjugation c (order ≤ 2) is trivial,
so the tower field K is totally real and F = K^<c> = K: no quadratic step,
transfer inapplicable. (Total reality was separately shown unprofitable.)

## 7. No better local conditions (SCAN + STRUCTURAL)

- f=1 (kill Frobenius): ratio-good (+0.34 margin per prime at 3) but
  absolutely unaffordable: +t + c1 ≈ +0.355 GS per prime vs slack 0.00211,
  and buying budget via S-expansion costs 6–7× the profit. Same wall at
  inert primes (ratio 4.4, same absolute wall).
- Higher tame f, e = 4 tame/dyadic, uncapped Frobenius, C8 caps, non-uniform
  caps: each loses in the model or arithmetically (profit loss ≥ 3× budget
  gain, or negative profit).
- Alternative dyadic local quotients (COMPUTED census, §11.9): all 21
  abelian 3-gen quotients (order ≤ 256) + non-abelian (8,8)/(16,4)/(8,2)
  — best NET (abelian (4,4), +0.0167) is GS-infeasible (+0.063),
  best feasible (shallow-abelian (8,8), −0.0066) loses; D stands.
- Larger S over Q or B: each added ramified prime nets −0.3 to −0.7 margin
  (rd cost dominates profit); the optimizer's exact DP confirms the chosen S.

## 8. Framework ceiling

Summing the individually-maximal, mutually-inconsistent gains:
caps +0.01805 (infinite GS budget) + analytic +0.0070444 (zero slack) +
geometric ~0 + profiles ~0 ≈ +0.0251 margin ≈ +0.00105 δ, giving
δ_max ≈ 0.04395 ≈ 0.0440 with shells. Realistic correlated gains are far
smaller. Target δ = 0.05 exceeds this by 0.006, ~6× the sum of all miracles.
Scope: this ceiling is specific to the norm-one-unit transfer — it sums
maxima of the norm-one rate equation. A different transfer (e.g. the
trace-zero alternative, §11.8) has its own rate equation and its own
ceiling; §8 does not bound it.

## 9. What δ = 0.0440 would require (exact)

Certified margin +5.779e-6 at δ = 0.042901 with slope −23.9 gives margin
−0.02626 at δ = 0.0440: reaching it needs **+0.02626 margin**. Available
maxima (§3): all-useful-caps +0.01805 (hard) / ~+0.0199 (shells, heuristic
+10%) + zero-analytic-slack +0.0070444 ≈ +0.0251/+0.0269. So δ = 0.0440
needs literally every miracle simultaneously — all 5 further caps (infinite
GS budget), zero analytic slack (infinite non-abelian tower), full shell
optimization — and even then succeeds only marginally (+0.00068 headroom,
shell-dependent). It is the all-infinities ceiling, not a target. Realistic
correlates: dihedral #1+#2+#3 (+0.00603, §11.1: #1 PLAN + #2 guaranteed
gated + #3 likely) + micro-harvest (+2e-5, needs FLINT env) + cubic-Fox
caps if sharing exists (+0.01805 max, §11.4; subgroup GS closed negative)
≈ +0.0241 best-case — still short of +0.02626.

## 10. Reproduction (of the searches/screens)

- Corrected scan: /tmp/scan/corrected/ (report /tmp/scan/report.md when done).
- Cap-prize arithmetic: §3.2 formulas (stdlib recompute).
- Cubic search: /tmp/cubic_search2.gp (PARI/GP; general cubics, disc<0,
  2 of type (1+2), 3,5 split; min |disc| 54419).
- Quartic search: /tmp/quartic_search.gp (r1=2, 2:(1+1+2), 3 ≥ 2 linears,
  5 ≥ 3 linears; min disc 2455515 at box ±20).
- Slack decompositions: /tmp/analytic/report.md, /tmp/geometry/report.md.
- Baseline review: /tmp/review41/report.md (41-cap sound).

## 11. Remaining leads (residual)

0. **No-dyadic tower S = {3,5} + inert 7: NO-GO (exact computation;
   retracts the δ ≈ 0.055 hand-estimate).** Three independent fatal
   findings (/tmp/no2/report.md): (i) GS FAILS (+0.0864 best, 0 caps with
   redundancy correction; +0.17 without) — the hand-estimate (−0.35)
   double-counted −t for the inert block in true-P_B normalization;
   (ii) E/B ramifies WILDLY at 2 (units −1, ε; cond exp 2), so log rd(E) =
   5.7625 EXCEEDS old 5.6561 (+0.1065, margin −0.049), and Y_E′ inflates by
   +0.042/degree (smaller degree); (iii) INCOHERENT as specified: E/B
   ramified at 2 but K/B unramified at 2 means E ⊄ K; correctly formulated
   (generator rank = 2-unramified Selmer V′, dim 5, not 7) GS fails harder
   (≥ +0.24). Formal margin δ′_est ≈ 0.0411 < 0.042901. Rescue A (5×
   C2×C4 locals) passes GS (−0.174) but dies analytically (genus degree
   ≤ 64 → C′ ≳ 0.09; est δ′ ≈ 0.033). Lesson: S ∋ 2 is FORCED (dropping 2
   drops 2 generators via V′ and breaks E ⊂ K). The §8 ceiling stands.
1. **Dihedral analytic refinement: PLAN (#1 +0.000145 → 0.043046,
   1–3 months; #2 GUARANTEED +0.000071 → 0.043117; #3 +0.000036 →
   0.043153; exact non-abelian cap +0.00029 → 0.04319; needs FLINT
   env).** Complete F2-classification
   finds 27 GL-orbits of D4 quotients of G_B; explicit β1 built with
   Gal(M~/B) = D4 triple-confirmed (sign pattern, 400-prime census
   χ2 = 1.0, conductor-discriminant square). The 64 twist AFE conductors
   are max 2.0e12 (verified; ~1e5× below the old ~1e17 estimate — the
   tower D4 is minimally ramified with N(f) = 4), max cutoff 5.7M terms,
   total ~5e7: NOT analysis-blocked. Exact ΔY* = −0.0034625 (v0-halving;
   non-v0 gains cancel Δ-losses exactly), ε-dividend ~6e-6 second order.
   Root number +1 confirmed (lfun FE −128 bits). Degree-4/Q AFE kernels
   DERIVED + PARI-VALIDATED (balanced AFE L(σ)=C(σ)Σa_n[I_{2σ−1}+εI_{1−2σ}],
   reproduces repo 'quartic' kernels exactly; β1 AFE vs lfun rel diff
   1.1e−13; tail theorem with explicit constants; /tmp/afe4/report.md).
   Remaining: sieve 2/64 MAX rows DONE (e=212/214, M=5.667M,
   Q=2.007e12; setup ~12min + sieve ~5–7min each; a361 = +2/−2
   twist split ✓; coef/ + jobs/ logs) — prototype works; twist-reuse
   (1 setup + 64 Legendre twists) still to implement (setup
   dominates). Root numbers: lfuncheckfeq INFEASIBLE at max Q
   (needs 107M coeffs, 19× cutoff, + >8GB stack — both max-row logs
   overflow at 8G) — use Artin-root-number formula instead. Sieve
   agent FD-blocked (2 attempts, zero new compute) — resume 62 rows
   when shell stable. Then rigorous enclosure (FLINT, hours–days),
   ceiling integration, write-up/Lean. Reports + scripts:
   /tmp/dihedral/ (d4search.py,
   verify.gp, census.gp, twist.gp, coef3.gp, twistQ.txt) + /tmp/afe4/
   (derivation, afe4.gp, validation.txt). #2 (NEW,
   /tmp/beyonddih/report.md, PROVED): distinct D4 orbits give distinct
   halving quadratics ψ (same ψ ⇒ same coset/kernel/ρ ⇒ same orbit),
   so ANY of the 26 unused orbits FULLY halves the remaining v0
   (any pair of distinct nonzero F2-functionals is independent):
   ΔC ≈ −0.00171 (±0.00004; exact needs β₂ + census join), Δδ ≈
   +0.000071 → δ ≈ 0.043117. Compositum irreps proved exact (order
   1024 = fiber F₂⁸ ×_W H, |H| = 32 subdirect; 256 linears + 192
   two-dim in 3 families of 64 — ρ₁ done in #1, ρ₂ + σ-mixed new;
   all monomial degree-4 Hecke, no 4-dim irreps, no Artin issue):
   128 NEW AFE rows (~10⁸ terms total, 2–4 months ~1.5× #1). GATE:
   σ-family conductors need β₂ — build the #2 AFE only if max-Q_σ ≲
   10¹³ (crude bound 10¹⁴–10¹⁵ unpriced; mitigation: re-rank orbit
   pairs by σ-quartic discs; σ/F₂′ kernel families may need 1–2 new
   kernel builds — critical-path flag). #3: ΔC ≈ −0.00086, +0.000036
   → δ ≈ 0.043153 (+256 rows in 7 families of 64; #3 CONFIRMED
   AVAILABLE — psi_rank.py RAN: every #1+#2 pair extends to a triple
   (min 1, mean 13.0 valid k over 25 j), ψ-rank = 15; needs β₃ +
   triple-mixed conductors; do iff #2's pipeline works). Q8 backup
   DEAD (complete search RAN: 64770 surjective φ1, 0 survive — no Q8
   quotients; unneeded since D4 #3 confirmed). #4 (+0.000018, +512
   rows) not recommended.
   Higher groups CLOSED: A4 impossible (G_B pro-2); NO C4 quotient
   of G_B at all (Ḡ^ab = F₂⁸ proved — 22 initials' S-parts span F₂⁸)
   kills C4×C2/C8/every C4-quotient group; D16/Q16/SD16/M16 (order
   16) impossible twice over (D4(Q) ≠ 1 via Zassenhaus AND C4
   quotients); order-16 D3=1 survivors (D8×C2, Q8×C2, extraspecials,
   C4-central products) + order ≥ 32 dominated (≤1–2 halvings at ≥
   D4 cost — backup halvings only); Q8 existence search scripted
   (backup). Mechanism theorem: every valid tower refinement's NET
   gain is v0-halving only (K-floors are (1,4); f4-resolutions
   telescope EXACTLY vs Δ — re-verified for #2's E₁-types; f ≥ 8
   unresolvable since Gal(Ẽ/E) has exponent ≤ 2). EXACT CAP on all
   non-abelian gain: v0 mass 0.006925 C ≈ +0.00029 δ (2× #1's exact
   gain; the 0.00688 figure is −0.7% rounding — adopt 0.006925);
   k halvings gain 0.006925·(1−2^{−k}) (k ≤ 41 in principle,
   [D₂:D4] = 2⁴¹; k ≤ 15 cheap D3-level); realistic k=3 (#1+#2+#3):
   δ ≈ 0.04315; absolute (k→∞, infeasible AFE): δ ≈ 0.04319; after
   #1+#2 ALL remaining non-abelian gain ≤ +0.000075 δ. Scripts (ALL
   UNRUN — shell down, run in order): psi_rank.py (ψ-rank, triples,
   Q8), orbit_screen.py (#2 ranking), gen_orbit_gp.py (PARI templates;
   validate orbit 0 reproduces twistQ.txt first), order16.py (backup
   census INCOMPLETE: 2/14 groups pass Part A (D8xC2, Q8xC2), hung on
   3rd — terminated after 1h; D4 #1+#2+#3 path unaffected).
2. **Subgroup GS for 4–8 caps: NEGATIVE (landslide).** Index-2
   Reidemeister–Schreier + sparse F2 Magnus + exact Tietze, all 255 χ,
   exact Fractions: best min P_U = +0.562/0.562/0.581/0.597 for 3/4/6/8
   caps (0/255 pass; medians +0.62). Structural: 46–50 exact quadratics vs
   d_U²/4 ≈ 12–20 affordable (~3× over). Literature confirms the question
   was genuine (subgroup GS provably independent of G GS — explicit
   H×C2 example) — and the answer is no. Machinery validated on finite
   controls (D8/Q8/trivial all ≥ 0) + cross-checks; word-lift caveat
   quantified (would need ~30 systematic jumps; PARI S-unit d(U) bounds
   corroborate). The 4th cap is not recoverable by GS strengthening
   (standard, weighted, and subgroup all fail). Report + replay (4 min):
   /tmp/subgs/report.md, `python3 subgs.py 3 4 6 8`.
3. **Micro-harvest toward certified 0.042902 (borderline, needs FLINT env).**
   Need +1.814e-5 margin; available ~+2.0e-5 (abscissa →1/280: +1.5e-5 C;
   θ-envelope +4.8e-6; degree-5 +2e-7; shells +5e-8). Blocked in this
   environment (no python-flint/mpmath/numpy, no pip/network/root); run on
   the documented stack per the synthesis plan (/tmp/synthesis/report.md
   §5). Success flips one grid point (0.042902), not 0.0440.
4. **Fox-row dependencies beyond s_D: leading order CLOSED (unique),
   cubic+ OPEN with explicit bounds (new within-framework lead).**
   (/tmp/foxdep/report.md; MACHINE-CONFIRMED — foxdep.py RAN: all
   checks passed, P_B matches manuscript exactly, t³/t⁴ scales
   confirmed.) Quadratic screen: rank(22
   initials) = 21 exactly, unique dependency = Σ of the 8 local
   classes (all 36 F2 entries checked; independently confirms
   tw:quadratic-layer); every single-block split shares exactly its
   local row at leading order, and ALL 56 second splits are 0 — no
   successive split can exploit a second leading-order saving (the
   "other dyadic row" is an alternative, not additional, saving).
   Cubic+ orders are PROVABLY UNSCREENABLE from recorded data (lifts
   ĝ beyond linear parts + dyadic Koch word beyond quadratic initial
   unrecorded — needs new data, not just compute). Bounds for
   hypothetical higher-order sharing: ≤ ~0.0245 (F³) / ~0.0071 (F⁴)
   in P_B units. Significance: a maximal cubic sharing (~0.0245)
   would JUST fund all 5 useful caps (~0.023 needed) → δ ≈ 0.04365;
   quartic (~0.0071) funds the 4th cap → δ ≈ 0.0432. So cubic-Fox is
   a possible MECHANISM for the §8 cap miracle (not new headroom
   beyond it). Cubic follow-up (/tmp/cubicfox/analysis.md + recipes.md,
   theory-complete): IMPLAUSIBLE as usable saving — [ρ,x]-type dead
   EXACTLY (rows in I·Λ∂ρ ⊂ S_old, G3 fails generally), lone-cap F³
   IMPOSSIBLE (gr_3(U_cap) = 0 exact, caps principal), survivors
   (Koch-bridge: shared z_3 spans both dyadics, ker dim exactly 8;
   dyadic cubic cut [[ŷ,ẑ],ẑ]: recorded F³ class, locally
   cubic-independent — hand-proved f ∉ [L_1,[r]_2]) have NO G1
   mechanism; cubic sharing ⟺ vanishing triple-Massey (arithmetic,
   untested; quadratic reciprocity exhausted). Value razor-thin:
   5-cap cost ≈ 0.02548 vs s′ ≤ t³ ≈ 0.02454 + slack 0.00211 =
   0.02665: funds with +0.0012 at fixed t₀, but realistic s′ < t³
   (annihilator) + t-shift needs joint re-optimization to confirm.
   Missing data inventoried EXACTLY: 472 fixed bits (464 Kummer
   4th-power over E_3/E, deg 2^29 — direct Cl(O_E) infeasible,
   duality via Hilbert symbols has one bounded derivation gap; 8
   Koch z_3 bits, Q_2-local) + 112 free fiber bits (sweepable).
   FIRST COMPUTATION: R0a recorded-only F³ graded screen (~1h code,
   seconds run — recipes.md R0a–R0d; script queued) — a positive hit
   is the only surprise route; expected-negative forces Kummer+Koch
   conspiracy (R1–R4 decide). DOWNGRADE: unlikely; screen to confirm.
5. **L4/f = 8 census: CLOSED — gain ≤ ~4e-7, do not pursue.**
   (/tmp/l4census/report.md + lie4_241.py + census8_241.py; MACHINE-
   CONFIRMED — both scripts RAN, all asserts passed.) Free restricted
   L4 on 8 gens = 1044 exact (restricted Witt + multidegree
   corroboration); R4c = 1920 explicit gens ([R3,L1]+[R2,L2]+S(R2)+Q4
   incl. 7 exact quartic words z⁴,[y,z]²,F⁴ — no F2[D] Jennings
   computation needed); rank(R4c) = 963, L4-quotient = 81,
   |G_B/D5| = 2^130, rank[R2,L1] = 140 ⟹ E_lift ≤ 36 exact. Task's f8 test
   was backwards: correct test is S(v) ∉ R2 AND S²(v) ∉ R4, so
   P8 ⊆ P4 (no f2→f8 jumps; only 72376 f=4 primes are candidates).
   Quartic completeness FAILS structurally: R4_true = R4c + E_lift,
   dim E_lift ≤ 176−rank[R2,L1] (~36, lift-data brackets — no
   initials-only closure); computed promotions are a conditional
   upper bound, while Σ₂/cap non-promotions are robust (hand-proved
   from S(R2)+[R2,L2]+Q4). Gain bound (unconditional): smallest
   unselected split prime is 41 (hand-verified Legendre), so gain ≤
   (1.01/8)·2·(P(4)−Σ_{p≤37}p⁻⁴) ≈ 3.6e-7; MACHINE f8 census (to 10⁶,
   f=4 saving reproduces paper to 12 digits: 0.001629841112): 69010
   conditional f8 primes, marginal gain 2.3e-7 ≈ 1e-8 δ — 1% of one
   grid step (and OVERSTATES: includes the selected 41-cap prime,
   truly f4 — true conditional gain ~1.3e-7). The "bigger f=8
   savings" premise dies on the norm distribution (all small-norm
   split primes already selected with exact types). Bonus: the 41-cap
   Frobenius tests f8-conditionally but is truly f4, PROVING E_lift
   ≠ 0 (S²(v_cap) ∈ E_lift ∖ R4c). Caveats: report.md file itself is
   truncated at §3 (full JSON in child session log); census8_241.py
   excludes 29 but not the 41 cap prime (accounts for the ~1e-7
   overstatement; f=4 baseline comparison unaffected). Other
   micro-leads: finer GS t-grid (confirmed no help).
6. **Weighted Golod–Shafarevich for a 4th cap: NEGATIVE (screen).**
   Standard GS fails by only +0.00288, but a 122184-direction weighted
   screen (Ershov-type criteria; proxy validated against gs241.py/lie241.py
   at the uniform point) finds uniform weights a strict local minimum
   (0 negative slopes) with finite-distance choices 10–30× worse than
   uniform (+0.033/+0.087 vs +0.002876); even a free 4th cap cannot rescue
   weighted choices (+0.028). Mechanism: relation supports are large, so
   upweighting costs 0.358/coord against ≤ 0.25 savings. Consistent with
   two prior bounded screens on other towers in
   papers/0.04273/certificates/.cache/publication/. Screen-level (floating
   point, one weight-function family incompletely covered), not an
   obstruction theorem — but no candidate to promote. Report:
   /tmp/wgs/report.md, reproduce `cd /tmp/wgs && python3 wgs_screen.py`.
7. **A new method entirely** (non-tower lower bounds beating n^1.044):
   literature survey (/tmp/methods/report.md) finds NONE: every published
   non-tower bound is subpolynomial (closest: Erdős grid 1+c/log log n,
   asymptotically 0.0429 behind); incidence/sum-product/finite-field/
   Behrend/quasicrystal routes are wrong-direction, dual-problem, or
   bounded-coordination. Structural reason: polynomial bounds need BOTH
   many representations (high dimension) AND exact length preservation
   (algebraic norm) — towers are the only known joint source. Open loophole
   flagged: a non-tower infinite bounded-rd family (none known; decades of
   discriminant-bounds work against).
8. **Trace-zero transfer: KILLED (exact-pairs obstruction — no
   continuous unfolding).** (/tmp/tracetheory/derivation.md +
   verdict.md; theory agent read geometry/finite-windows/profiles/
   certificate in full and derived the trace margin shape M′(θ) =
   a(1−2δ′)−(1/2−δ′)ℓ−δ′log2+(1−2θ)J′_R+θJ′_C — but the formal
   equation MISLEADS (margin +5.24, formal zero δ′ ≈ 0.6: it counts
   all M-pairs at ALL distances, not unit distance). Kill chain
   (computation-free): (i) φ_{v0}|_N injective for any nonzero O_F-sub
   N of {Tr = 0} (kernel would be finite-index, image torsion-free);
   (ii) per x, per distance r: ≤ 2 differences in N (values ±ir,
   each ≤ once); (iii) trace-counted unit pairs E ≤ 2n (same coset);
   (iv) t cosets raise the UPPER bound (≤ 2tn) but the LOWER bound
   fails — each (i,±) slice is a point (v0 pins m uniquely, no
   h-average to unfold over), so no mechanism produces EXACT unit
   distances (parent sharpening: exact pairs need ±i ∈ φ_{v0}(N), a
   measure-zero coincidence per pair; the unique pinned m has
   uncontrolled other coordinates and escapes the window). So trace
   proves NOTHING (not even δ′ = 0: even linear pairs need m^± in
   the window + exact membership — unprovable, generically false).
   DOUBLE KILL (method failure + generically zero exact pairs). The
   §8 ceiling stands unchallenged: all known frameworks capped
   (norm-one ≤ 0.0440, trace ≤ 0). Lesson (retracts the 20–30%
   prior): polynomial pair lower bounds need CONTINUOUS unfolding
   (the R^c unit-average turning positive-measure overlap into exact
   pairs), not just lattice density. Killed combos re-confirmed:
   odd-p × trace (line in R², δ = 0); fixed-box trace (decays/
   linear).
9. **Alternative dyadic local quotients: CLOSED — D stands (parent-
   verified with one row corrected; v2 RE-RUN by parent).**
   (/tmp/abeldyad/report.md; compute2.py re-executed by parent: pt
   validations 29:0.02883/41:0.00699/47:0.00406/53:0.00148 ✓,
   P_B/d_D/s_D/c4/refinement all reproduce ✓, ab(4,4) Pnew = +0.06320
   INFEASIBLE ✓, ab(4,2) Pnew = +0.12982 ✓.) Full census: 21 abelian (m,n) rows
   (order ≤ 256) + 3 non-abelian rows, exact Fractions at t = 34/117,
   P_B^new = min-grid(PB_old + ΔP) WITH current 3 caps (correct
   feasibility quantity — verified by reading compute2.py). Best NET:
   abelian (4,4) +0.0167 but GS-INFEASIBLE (ΔP_B = +0.067, Pnew =
   +0.063; needs ~13 nonexistent caps) — hand-confirmed at t₀
   (P_B^new = −0.00211 + 0.06688 = +0.0648; infeasibility robust:
   ΔP(t) > 0 ∀t>0 since h_A < h_D ⟺ 1 < 1+t², and ΔP ≈ 0.067 ≫
   |PB_old| ≤ 0.00211 wherever PB_old < 0). All abelian m = 1
   infeasible ∀n (h_A < h_D on (0,1), no twists; margins ≥ 0.05);
   all m ≥ 2 rd-dead (δ2 = m+1 ≥ 3, NET ≤ −0.24); (4,f) 3-gen forced
   abelian (Lemma C). Structural gem: ab(2,2) has EXACTLY D's GS
   cost (h identical: (1+t)³(1+t²)²) but δ2 = 3 — D's
   non-abelian-ness buys shallower ramification at equal GS price.
   CORRECTION (parent): the (8,8)-D8 row (−0.0164) is chimeric —
   Lemma-C-type argument FORBIDS non-abelian 3-gen (8,8) (|G^ab| ≥
   8·2·2 = 64 = |G| ⟹ abelian; the child applied this to (4,f) but
   missed (8,8)): coherent readings are shallow-abelian Gal(M16U8/Q2)
   (h = (1+t)³(1+t²)²(1+t³), NET ≈ −0.0066 — closest call in the
   lane, still dead: needs 60%+ profit error; discrete-cap reality
   ≈ −0.009) and ramified-nonab (16,4) (NET ≤ −0.08). (8,4)-nonab
   gap CLOSED by parent (Jennings maximality: D's (d2=2) shape
   maximizes h among 3-gen order-32 — every (d2<2) shape replaces a
   (1+t²) factor with a smaller (1+t^i); and s_A ≤ t² = s_D+6e-6 —
   so same-(e,f) alternatives tie D at best). G164/M16 dead
   (bounds). Verdict SURVIVES correction: no replacement beats D.
   Scripts: compute2.py (v2, load-bearing), lie_check.py (exact F2
   ranks reproduce 21/142/2⁴⁹), fox8.py (Fox block — for the
   chimeric D8; needs re-targeting if ever used).

## 12. Conclusion

Within the tower + norm-one-unit framework, 1.042901 is optimal up to
~+0.0011 of mutually-inconsistent miracles (≈ 1.0440 ceiling). Closed since: no-dyadic tower (NO-GO, §11.0), weighted GS (negative),
subgroup GS (negative landslide, §11.2), dyadic quotients (D stands, §11.9),
L4/f=8 (≤ ~4e-7, §11.5), all base/signature/transfer
variants, all non-tower methods (§11.7), trace transfer (exact-pairs
obstruction, §11.8). The 4th cap is unrecoverable by any GS
strengthening. Open paths: dihedral engineering (§11.1, #1 +0.000145 →
0.043046 + #2 guaranteed +0.000071 → 0.043117 (σ-gate) + #3
confirmed-available +0.000036 → 0.043153; D4 + conductors + validated
AFE done, coefficient sieve respawned now shell is back, FLINT enclosure
+ integration remain); cubic-order Fox sharing (§11.4, hypothetical
mechanism for the cap miracle, existence unknown, data-blocked).
Combined realistic best ≈ 1.0432 (dihedral #1+#2+#3 → 0.04315 + micro
→ ~0.04317, pending FLINT env);
1.05 and 1.0440 have no open lead in any known framework (norm-one ≤
0.0440 ceiling, trace ≤ 0).
