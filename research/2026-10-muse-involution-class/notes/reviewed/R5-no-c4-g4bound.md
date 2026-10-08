# R5: no C4 quotients (abelian acquisition dead) and g4 in [53,81]

Status: ready for checking. Code: `research/2026-10-muse-involution-class/code/R5/no_c4.py`
(exit 0). Depends on `tower.tex` (tw:quadratic-layer R2, tw:kummer-field,
tw:GB-presentation 30 generators, tw:GB-basic, tw:retained-quotient(b)),
`C16-lie45-upper-bounds.md` (range tightened here),
`C93-quotient-repair-check.md` (§1b/§4a V-shapes, §3c hunch settled),
`C102-section-comparison-check.md` (adopted: fiber invisible, real
T-in-R2 refuted, 248 as bookkeeping). C107 owns Hopf conventions.

## 1. GB has no C4 quotient; GB^ab is C2^8 (proved)

Let q: GB → C4 = ⟨σ⟩ be surjective with gr1-form
φ: F2^8 = GB/D2 → C4/⟨σ²⟩ ≅ C2 (φ ≠ 0). The graded map
λ_φ = (q∘π)_*: L2 = gr2(F) → gr2(C4) = ⟨σ²⟩ ≅ C2 satisfies
λ_φ(S(e_i)) = q(x_i)² = σ^{2φ_i} and λ_φ([e_i,e_j]) = 1 (C4
abelian), so λ_φ(M) = Σ_i M_{ii}φ_i. Every relator initial
r ∈ R2 has λ_φ(r) = q(1) = 0. But diag(R2) over the 22 recorded
initials has rank 8, nullity 0 (computed; hand check: cap squares
pin φ_2..φ_7, real squares pin φ_0 and φ_0+φ_1) — so φ = 0,
contradiction. Hence no abelian quotient has a C4-quotient: no
Z2-summand (Z2 ↠ C4), torsion of exponent ≤ 2. With
GB^ab/2 ≅ GB/D2 ≅ F2^8 (Kummer; N ⊂ D2), GB^ab ≅ C2^8.

Consequences: single-coordinate acquisition via abelian (C4/C8)
quotients is IMPOSSIBLE beyond Kummer gr1 — the realized-abelian
route is dead by theorem, not by failed search. C93 §3c's "may
have C4 factors" hunch is settled negatively (consistent: order-4
Frob/z map to order ≤ 2 in the abelianization, as in D4).
Nonabelian quotients give only conjugacy classes for D1-elements
(place ambiguity); central commutator coordinates see no positions
([ĝ1,ĝ2]_2 = [V1,V2]). 248 kept as bookkeeping per coordinator.

## 2. R4-exhaustion gives g4 ≥ 53 (proved)

Every w ∈ N_B ∩ D4 is a product of conjugates of the 30 normal
generators. Deg-2: quadric exponents vanish mod 2 (R2 21
independent). Deg-3: (w)_3 = 0 is a relation among the 170 R3-rows
in L3, i.e. (f,d) lies in the 28-dim syzygy kernel (170 → 142).
Deg-4: quadric-squares, quartics, [N∩D3,F], [R2,R2] (folding),
conjugate-adjustments and collection all land in I4; only the 28
syzygy-lifts contribute outside: R4 = I4 + span{corr_1..corr_28}
for 28 fixed vectors (fiber-dependence irrelevant to the count).
Hence 963 ≤ dim R4 ≤ 991 and g4 ∈ [53,81] (1044/963/170/142/28
re-verified in code), tightening C16's [0,81]. S_5 ∈ [102,130].

Consequence: g4 > 0 settles V-existence (open per C86): hyperplanes
V (D5 ⊂ V ⊂ D4, [D4:V] = 2) exist, giving 2^50-quotients Q = GB/V
with |cl_Q| ≥ 2^15 (C93 §1b central case). Strict ≥ 2^16 still
needs the lifting defect, hence exact R4 (T' ∈ 214-space unknown).

## 3. Scope

Deg-3 T'-acquisition is complete at 214 (R5-second-cut §4); abelian
acquisition is impossible (§1). Exact R4 = I4 + span(28-corrs(T'))
still needs T'. Next: robust-defect analysis over the 214-space, or
new ideas. No certification (no slack).

## C126 review (2026-10-06)

Checker C126. Verdict: Sec 1 PROVED (terminology nit fixed); Sec 2
PROVED after repair (full exhaustion proof supplied); Sec 3 scoped
(214 conditional). Code: `research/2026-10-muse-involution-class/code/C126/c126_no_c4_check.py`
(stdlib, exit 0, ALL PASS). Reran
`research/2026-10-muse-involution-class/code/R5/no_c4.py` (exit 0, outputs as claimed).

Extracted to corpus:
- `research/2026-10-muse-involution-class/corpus/C126-no-c4-abelianization.md` (Sec 1: no C4
  quotient, GB^ab = C2^8, abelian acquisition dead; diagonal proof with
  hand pins + 255-phi sweep; C93 Sec 3c hunch settled negatively).
- `research/2026-10-muse-involution-class/corpus/C126-g4-lower-bound.md` (Sec 2 repaired: R4 = I4
  + span(28 corrs), dim R4 in [963,991], g4 in [53,81], S5 in
  [102,130], V-hyperplanes exist with 2^50 quotients and class >= 2^15;
  full F/D5 proof with even exponents, f = x.u reduction, [a,bc]
  identity, folding, psi linearity).

Rejected / scoped:
- Sec 1 phrase "cap squares" is a misnomer (read dyadic/tame squares
  x^2, tau^2; caps are quartics); pins themselves verified. Harmless.
- Sec 2 as written is a sketch (omits even-exponent combining,
  conjugator reduction, collection commutators, folding details,
  well-definedness of the 28-image); repaired in the corpus entry with
  no change to the claimed range. The conclusion stands as proved.
- Sec 3 "complete at 214" and "214-space" stay conditional per C117
  (R5-genuine-lift framework unchecked); not needed for Secs 1-2.
  The nonabelian-quotient remarks in Sec 1 are kept as remarks
  ([g1,g2]_2 = [V1,V2] standard, not load-bearing).

Unresolved / open:
- Exact R4 (needs T'); lifting defect for >= 2^16 (needs exact R4);
  any per-layer bound beyond g4; 214-cut validity (C117 conditional).

No previously proved corpus result overturned. C16 g4 [0,81] tightened
to [53,81] (consistent); C93 "GB^ab = F2^8 unproved" superseded by proof
(its no-cyclotomic-Z2 stands strengthened); C86/C93 V-existence (open)
now proved for the >= 2^15 central case.

