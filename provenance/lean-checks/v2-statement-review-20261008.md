> Independent fresh-context review of the version 2 Lean statement (ChallengeZeta241.lean, theorem target_of_wide_zeta_bound), the field E_W, the hypothesis H_W and its external evidence (October 8, 2026, branch lean-1.04317), by an AI agent; read-only. It found no error; its documentation points were applied in 72e4d054. Paths under /tmp are the reviewer's scratch space.

# Independent review: Lean version 2 statement (H_W, exponent 20863/20000)

Date: 2026-10-08. This review was read-only. No repository file was changed, and `git status` is
clean in `lean-1.04317` and in `master`. Worktree: `lean-1.04317` at `3e67ea69`. Paper sources:
`master:papers/0.043171`.
Scratch scripts are in `/tmp/claude-1000/paper-audit/lean-v2-review-scripts/`. They use PARI/GP
2.17.2 and Python, and the receipt was re-run in a scratch copy of the `papers/` tree.

## Verdict

I found no error in the statement, the field, the choice-independence claim, the relation between
the hypothesis and the evidence program, or the axiom footprint. Everything I checked
independently agreed with the documents and the JSON, to every printed digit where that applies.
One input remains unverified by me: the certified values of the 128 degree-8 L-functions and of
430 of the 448 degree-4 L-functions. The receipt takes these from the paper's data. The
degree-8 part contributes 0.019737 to Y_W. The slack 5.19e-5 would be used up by a total error
of +0.106 in the sum of the 128 logarithms of the degree-8 L-values, or +0.21 in the sum of the
448 logarithms of the degree-4 L-values.

## 1. Statement fidelity (ChallengeZeta241.lean)

* **Conclusion.** The theorem asserts
  `∃ U : ℕ → Finset ℂ, Tendsto (|U j|) atTop atTop ∧ Tendsto (unitPairs (U j) / |U j|^exponent) atTop atTop`,
  with `exponent = 20863/20000` (= 1.04315, checked with `norm_num`). This is a sequence
  statement only, as documented.
* **Unit pairs.** `unitPairs U` is (number of ordered pairs at distance 1)/2. Distance 1 excludes
  the diagonal and is symmetric, so this is the number of unordered unit pairs.
  * I checked in Lean that the `dist` used in `orderedUnitPairs` is Euclidean. This is the
    `dist` elaborated under `attribute [-instance] instCommCStarAlgebraComplex`. The check is a
    scratch `example` proving
    `orderedUnitPairs U = (U ×ˢ U).filter (fun e => √((Δre)²+(Δim)²) = 1)`
    (`Dist.lean` in the scripts directory). It compiled without errors.
* **Hypothesis.** It is exactly the H_W display of `docs/ASSUMPTIONS.md` and `README-zeta241.md`:
  ```
  log(Re ζ_{E_W}(1+1/4411))/8192 + (1/4411)((ℓ−γ−log 4π)/4 − Re(logDeriv ζ_{E_W} 2)/8192) < 50969/10^6
  ```
  * `#check` shows that `Real.log (…).re / 8192` parses as log(Re ζ)/8192.
  * `#check` shows no other hypotheses and no extra instance arguments.
  * `ceiling = 0.050969` (checked with `norm_num`). `logRD = (9/4) log 2 + (1/2) log 3615 = log(√241·2^{9/4}·√15)`.
* **dedekindZeta.** `#print NumberField.dedekindZeta` gives `LSeries (n ↦ #{I : absNorm I = n})`.
  For Re s > 1 this is the standard Dedekind zeta function.
  * Both evaluation points are real and > 1, so ζ(σ) is real and positive, and `logDeriv` at 2 is
    the genuine ζ'/ζ(2) (the function is analytic there).
  * Nothing evaluates to a junk value.
* **Definitions match the documentation and the paper.** Checked in PARI:
  * `radicandA` and `radicandB` equal `census241.KB` and the paper's α_0…α_7.
  * Their norms are `[1,−1,−2,−2,−3,−3,−5,−5]`.
  * α_1 is PARI's fundamental unit of B.
  * h(B) = 1.
  * All eight radicands are {2,3,5}-units, and their exponent matrix in a `bnfsunit` basis has
    rank 8 mod 2, which is the full size of (S-units)/squares. So E is the maximal elementary
    abelian 2-extension of B unramified outside 2, 3, 5, ∞, of degree 512, as the docstring says.
  * `rootA` and `rootB` are the products of genus roots over the rows of forms 24, 20, 17, 7 of
    `d4all27.json`. All eight index sets match.
* **No degeneracy.** Lean proves `[E_W:Q] = 8192`. I confirmed independently that the four β_i
  are independent in E*/E*² (§2). The hypothesis is a tight numerical statement (slack about
  5e-5). It is not vacuous and not trivially true or false.

## 2. The field E_W equals the paper's E_{W''}

Each item was checked from the Lean source with PARI (`fields.gp`, `d4.gp`, `qforms.py`, `v0check.gp`):

* **Same β as the paper.** Each Lean β_i is a rational square times the `coords` of
  d4all27.json, with the same coordinate basis (1, √241, √a, √241√a, √b, √241√b, √a√b, √241√a√b):
  * form 24: 576 = 24²
  * form 20: 16
  * form 17: 4
  * form 7: 4
* **D4 structure.** For each Lean β_i and each nonzero σ ∈ Gal(F_0/B), with F_0 = B(√a_i, √b_i),
  I tested squareness of N_σ = β·σ(β) in the quadratic subfield F_σ:
  * D1 holds (σ(β)/β is a square in F_0) iff N_σ or c·N_σ is a square in F_σ.
  * t_σ = +1 iff N_σ is a square in F_σ.
  * Result: D1 holds for all 12 pairs (i, σ), and t_σ = −1 exactly at σ = ρ. Here ρ is (0,1) for
    form 24 and (1,1) for forms 20, 17 and 7.
  * So β_i is not a square in F_0, and B(√a_i, √b_i, √β_i)/B is Galois and dihedral of degree 8
    (the order-8 group argument in Lemma dh:detection(a), which I re-derived).
* **β_i are S-units.**
  * N_{F_0/Q}(β_i) = 2^50·3^18, 2^36, 2^16·3^2, 2^16·3^2.
  * Each β_i is integral, so it is a {2,3}-unit.
  * Hence E_W/B is unramified outside 2, 3, 5.
* **Span.** With q_o(v) = [φ_o(v) = ρ_o] evaluated on all of F_2^8:
  * q24 = q10 + q23, q20 = q10 + q19 and q7 = q17 + q19.
  * The Lean four and the paper's {10, 23, 19, 17} both have rank 4, and their union also has rank 4.
  * The 15 nonzero elements of the span are the 7 listed dihedral forms (polar rank 2) and 8
    elements of polar rank 4.
  * The 8 pair sums used for the degree-8 families are exactly those 8.
  * Since ψ ↦ q_ψ is injective (Lemma dh:quadratic), span{ψ24, ψ20, ψ17, ψ7} = W''.
* **Same check on the actual β.** At all 2456 primes of B of Frobenius vector 0 with norm ≤ 10^7,
  I computed the Legendre bits of β_o modulo a prime of F_{0,o}, using the JSON β for 10, 23, 19.
  * They satisfy ψ24 = ψ10 + ψ23, ψ20 = ψ10 + ψ19 and ψ7 = ψ17 + ψ19 with no failure.
  * The four Lean bits have F_2-rank 4. A product relation among the β_i modulo E*² would force a
    linear relation on these bits at every such prime. So the β_i are independent in E*/E*², and
    [E_W:E] = 16, [E_W:Q] = 8192. This agrees with `Wide.finrank_field`.
* **Consequence.** E_W = E·M_24·M_20·M_17·M_7. It is contained in the paper's E_{W''}, which
  contains the M_o by Lemma dh:EW(a), and both have degree 8192, so they are equal. This relies on
  the paper's Lemma dh:detection(b) (M_o lies in the fixed field of D_3G_B), which I did not
  re-prove.
* **L-functions of the Lean fields.** Independently of that lemma, the L-values of the Lean fields
  match the receipt's data, as reported in §4.

## 3. Independence of the choice of square roots

The docstring claim holds, given D1, which I verified above.

* Let another choice function give baseRoot'. Take τ ∈ Aut(Q̄/Q) with τ(baseRoot) = baseRoot'.
* Then τ(radicand i) = radicand'_i exactly (rational polynomials in baseRoot), so
  τ(genusRoot i) = ±genusRoot'_i.
* So τ(rootA_i) and τ(rootB_i) are rootA'_i and rootB'_i up to independent signs. All four sign
  patterns occur, because each of rootA_i and rootB_i contains a genus root that the other lacks.
* So τ(β_i) is β'_i transformed by some σ ∈ Gal(F'_0/B'). By D1 (an algebraic identity,
  transported by τ), τ(β_i) ∈ β'_i·F'_0*². Hence τ(E_W) = E_W'.
* Signs of `wideRoot` do not matter.
* Isomorphic number fields have the same `dedekindZeta`, so the hypothesis does not depend on the
  choices.

Caveats:

* Without D1 the claim could fail: a non-Galois β would give non-conjugate fields for different
  sign choices.
* E_W is not Galois over Q (`docs/v2/PLAN.md` gives conjugate forms 13, 12, 22, 3). So E_W as a
  subset of Q̄ does depend on the choices. The docstring correctly claims only "image under an
  automorphism".
* The Lean proof does not use this argument.

## 4. Hypothesis versus h_w_receipt.py

* **Matching terms.**
  * SIGMA = 4412/4411 = 1 + 1/4411, and eps = 1/4411.
  * ell = (9/4) log 2 + (1/2) log 3615.
  * Bhalf = (ell − γ − log 4π)/4, using `arb.const_euler`. Its value 0.6369412029213714558 equals
    my PARI value.
  * LHS = Y + eps·(Bhalf + D_W) with D_W = −Re(ζ'/ζ)(2)/8192. This is the Lean sign: −(logDeriv)/8192 = +D_W.
  * The bound uses `Y.upper()` and `lhs.upper()`.
* **Formula for D_W.** −ζ'_K/ζ_K(2) = Σ_𝔓 log N𝔓/(N𝔓² − 1). E_W/B is Galois as a compositum of
  E and the M_i, each Galois over B. A prime P of B with norm N and type (e, f) therefore has
  4096/(ef) primes above it, each of norm N^f. Dividing by 8192 gives log N/(2e(N^{2f} − 1)).
  * This decreases in e and in f, so lower bounds for (e, f) give upper bounds.
  * The types used at 2, 3, 5 are valid lower bounds. E contains √−1, √2, √3, √5 (α_2α_3 = 2,
    α_4α_5 = −3, α_6α_7 = −5, α_0 = −1), so its completions at the split primes over 2, 3, 5 are
    the maximal elementary abelian extensions of Q_2 and Q_3, Q_5, of types (4,2), (2,2), (2,2).
    E ⊆ E_W.
  * The tail bound (1 + 2/X²)(log X + 1)/X is valid. There are at most two primes of B of each
    norm n (two of norm p, or one of norm p² for inert p), log t/t² is decreasing, and
    n²/(n²−1) ≤ 1 + 2/X².
* **Independent recomputation of D_W** (`fcheck.gp`). For every prime of B outside 2, 3, 5 with
  norm ≤ 10^6, I computed the residue degree in E_W/B directly from the Lean β_i. Over
  F_{p^4} it is max(f_E, f_{M_i}), where f_{M_i} = [k_P(√a, √b, √β) : k_P]. This covers all
  78,619 primes, including inert primes and p = 241.
  * The direct f equals the receipt's rule `fW` at all 78,373 primes with vector v ≠ 0: 0 mismatches.
  * Of the 246 primes with v = 0, 243 actually have f = 2. The receipt uses f = 1 for them, which
    is a valid lower bound.
  * D_W upper with the receipt's convention: 0.019724155717999915058317746218954719573. This
    equals the receipt's `D_W_upper` to all 39 printed digits.
  * The prime counts agree: f2 = 31499, f4 = 46874, v0 = 246.
  * With exact f at v = 0, D_W = 0.0197241388.
* **Re-run.** I re-ran the receipt in a scratch copy of `papers/` (58 s, using the master `.venv`
  with python-flint 0.9.0 and the unpacked 0.0418235 cache). The output JSON is identical to the
  committed `h_w_receipt.json`: LHS_upper = 0.0509171472738215, slack 5.185e-5.
* **Y_E** (`ye.gp`). I recomputed log ζ_E(4412/4411)/512 = (log ζ_B + Σ_{255} log L(χ_w))/512 with
  PARI `lfun`, as quotients of quartic Dedekind zetas: 0.0883771251190721632724. This lies inside
  the receipt's interval [0.08837712511907216321, …16334].
* **Degree-4 L-values** (`lspot.gp`, `lspot2.gp`, `twists_r2.gp`). I checked 18 of the 448:
  * w = 0 for each of the four Lean forms, built directly from the Lean β. Each was computed as
    ζ_{K}/ζ_{B_c} with γ = (1+u)²β as in Lemma dh:Lfunctions(a).
    * Form 20 was checked with both choices of τ, which agree.
    * Form 20 has Gamma factor Γ_R(s)Γ_R(s+1)³, as the paper states.
  * Two random twists for each of the 7 orbits.
  * All 18 conductors equal the JSON `Q`. Every PARI value lies inside the receipt's certified
    interval. All 18 functional-equation checks are at 1e-124 or better.
* **Bookkeeping.** I recomputed Y_W from the hp3 files and my Y_E as
  Y_E/16 + 2Σ log L4/8192 + 4Σ log L8/8192 = 0.05076827731778. This lies inside the receipt's
  interval.
  * The multiplicities 2 and 4 follow from the dimensions of the 2- and 4-dimensional
    representations, and the counts 7·64 + 8·16 match the irreducible representations
    (Σ dim² = 4096 − 256).
  * Each orbit file has 64 twists that are pairwise distinct modulo span(r1, r2). Each degree-8
    family has 16 twists that are distinct modulo the span of its four vectors. All rows are at
    σ = 4412/4411.

## 5. Axioms and diff

The scratch file was `/tmp/claude-1000/lean-axioms-check/Axioms.lean`, outside the repository. I
ran it with `lake env lean` from `lean-formalization/` after `lake build --no-build`, which
reported "All targets up-to-date":

```
'UnitDistanceSqrt241Submission.target_of_wide_zeta_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'UnitDistance.Sqrt241.V2.target_of_wide_zeta_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`diff ChallengeZeta241.lean SolutionZeta241.lean` shows only two differences:

* `+public import UnitDistance.Sqrt241.V2.Final`
* `sorry` replaced by `exact UnitDistance.Sqrt241.V2.target_of_wide_zeta_bound hfinite`

`comparator-zeta241.json` permits the same three axioms.

## Minor observations (documentation only, no mathematical error)

* `lean-formalization/docs/v2/W4_ANALYTIC.md:68-72` gives the left side as "about 0.0509152, slack
  about 5.4e-5". That is an uncertified pre-W6 estimate, with D_W ≈ 0.01134 from the actual
  dyadic types. The certified receipt bound is 0.0509171473 (slack 5.2e-5), because it uses the
  E-type (4,2) at 2. Suggested repair: point to the receipt value.
* `docs/v2/PLAN.md:17` still writes E_W = E(√γ_10, √γ_23, √γ_19, √γ_17). This is the same field
  (the spans are equal), but the generators differ from the Challenge's forms 24, 20, 17, 7. Line
  84 of the same file has the current description.
* `h_w_receipt.py`:
  * Its docstring cites "Section 11c" and "Lemma 4''". These are sections of
    `papers/0.043171/README.md`, not of the manuscript, where they are §5, Lemma dh:residue and
    (dh:YW). Suggested repair: say so.
  * When re-run, it overwrites `h_w_receipt.json` in the source tree.
  * It needs `env241`, the 0.0418235 publication cache and about 150 MB of data that the export
    does not ship. The exporter says that the shipped copy is provenance only.

## Not checked

* The certified L-values themselves beyond the 18 degree-4 spot values and Y_E:
  * the remaining 430 degree-4 values;
  * all 128 degree-8 values (conductors 7e17–7e20, beyond PARI `lfun` here).
  * PARI's values are not certified, but they agree with the receipt's intervals.
* The paper's group-theoretic Lemma dh:detection(b) (M_o lies in the fixed field of D_3G_B, via
  the G_B presentation).
* The Lean library proofs themselves, beyond the axiom audit and up-to-date build status. I did
  not rebuild.
* `inertv0`, the census and the parts of `dihedral_ceiling3.py` that the receipt does not use.
