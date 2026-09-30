# Porting the conditional proof to the tower over ℚ(√241)

Started 2026-09-29 on branch `quadratic-base-q-sqrt241`. The research
result is [papers/0.04273](../../papers/0.04273/README.md)
(exponent 1.04273, reviewed, finite replay passing). This file records the
assessment of the existing Lean development, the proposed conditional
statement, the work packages and the current state. It is a plan and progress record; the submission
account is [sqrt241/SUBMISSION.md](sqrt241/SUBMISSION.md).

**Status (2026-09-29): complete.** `SolutionZeta241.lean` proves the statement
of `ChallengeZeta241.lean` from the single hypothesis H, with only `propext`,
`Classical.choice` and `Quot.sound` in the transitive closure; two independent
reviews found no blocking issue. Candidate 4 of this development passed the
complete pinned Palomar pipeline under the 16-CPU/32-GiB profile
(`verification/sqrt241-full-20260929/README.md`). The current sources add
proof-internal certificate splits for the 4-CPU/16-GiB profile
(`verification/sqrt241-bounded-20260929/README.md`). H is not proved in Lean;
its evidence is in [sqrt241/SUBMISSION.md](sqrt241/SUBMISSION.md). The rest of
this file is the plan and progress record as written during the port.

## 1. Proposed statement

Statement: [ChallengeZeta241.lean](../ChallengeZeta241.lean) (placeholder proof); proof:
[SolutionZeta241.lean](../SolutionZeta241.lean).

* Exponent `10427/10000` (the "0.0427 bound"). The research note certifies
  1.04273, but at 1.0427 the geometric margin is 0.000908 instead of
  0.000177, which leaves room for the rational enclosures of a formal proof.
* **H is stated on the genus field E = ℚ(√241, √α₁, …, √α₈)**, degree 512,
  with α ∈ {−1, ε, π₂, π₂′, π₃, π₃′, π₅, π₅′} the Kummer basis of
  `kummer241.gp`. The form is the one of `ChallengeZeta.lean`:

      log ζ_E(1+ε)/512 + ε((ℓ − γ − log 4π)/4 − (ζ_E′/ζ_E)(2)/512) < 0.0852,
      ε = 1/300,  ℓ = (9/4) log 2 + (1/2) log 3615.

* Why E rather than a retained field. E is abelian over B, so ζ_E is a
  product of 256 Hecke L-functions and H is a directly computable
  statement: `afe241.py` encloses (1/512) log ζ_E(301/300) rigorously in
  [0.0826446018, 0.0826446081] (PARI `lfun`: 0.0826446049). With the
  Euler-product value of the log-derivative term, the left side is
  ≤ 0.0848336, so H holds with slack 0.00037. The literal analogue of the
  ℚ statement would put H on the D₃-retained field over B (degree 2²⁴, 15
  further radicals in E), which can only be certified indirectly through E.
* Price: the passage from E to the retained field M_B must be proved in
  Lean instead of being absorbed into H. The numbers
  (`fixedBaseResidueCeiling` with ε = 1/300):

  | term | value |
  |---|---|
  | fixed-base ceiling of E | 0.0848335 |
  | − exact types at 2 [(4,2)→(8,4)], 29 [(1,2)→(1,4)], 7 [rel. (1,2)→(1,4)], log-ζ part | −0.0344534 |
  | − same primes, log-derivative part (×ε) | −0.0000374 |
  | − census, primes of B of norm ≤ 100 (18 primes above 41,…,97; f ≥ 4) | −0.0012628 |
  | = ceiling for the tower fields | 0.0490799 |
  | geometric threshold at δ = 0.0427 (s′ = 1.1·1.0427) | 0.0496208 |

  At δ = 0.04273 the census would have to run to norm ≈ 1000 (≈ 166 primes
  of B) and the total slack is 0.00015. The census to 10⁶ reproduces the
  certified C = 0.0487128429 of `ceiling241.py` exactly.
* The ceiling `852/10000` splits the available 0.00054 between H (0.00037)
  and the Lean threshold (0.00017); the proved corrections leave 5.4·10⁻⁵ of
  the latter.

## 2. What carries over

The assessment made at the start of the port (2026-09-29), kept as a record; the rows
marked **Done** were updated as streams finished, and §4 gives the final state.

Sizes from the import cone of `target_of_canonical_sharper_zeta_bound`:
831 own modules (≈104k lines) plus 1,329 upstream/third-party modules
(≈529k lines).

| Component | Status for the port |
|---|---|
| Upstream: Yamaguchi class field theory, Galois cohomology, pro-C groups, valued fields; AINTLIB; Hadamard; Poisson | Reuse unchanged. Includes, for general number fields, the cyclic Hasse norm principle (`hasseNormPrinciple_cyclic`) and global Artin reciprocity, which the relation bound over B needs. |
| Geometry and transfer (`Geometry*`, local windows/shells/operators, Poisson, S-integer witness layer, relative units and mass, capitulation) | Generic in the fields; reuse. The S-integer/tensor layer reads a global 11-prime witness: see next row. |
| Witness data (`Target`, `Witness`, `Fin 11`, prime tables, 69/32 = Σ1/(ef)) | Reparametrize. ≈108 files mention the witness or `Fin 11`, 34 carry literals. New data: 5 types 2:(8,4), 3:(2,2), 5:(2,2), 29:(1,4), 7:(1,8); Σ1/(ef) = 29/32. Recommended: a witness structure indexed by the number of types, instantiated for ℚ and for B. |
| Numeric margin (111 modules, ≈23.5k lines) | **Done** (stream A1, `UnitDistance/Sqrt241/Numerics/`): `uniform_margin : 1189/10⁷ < margin θ − 4ε` for θ ≥ thetaMin at ceiling 0.0495 (positive for any ceiling < 0.0496189 via `uniform_threshold`). The witness keeps the manuscript's s = 22920117/20000000, so the verified pair-overlap certificate transfers verbatim; the pair mass for the new p is a new generic certificate (any rational q). See `docs/sqrt241/A1_NUMERICS.md`. |
| Signature θ | `complexPlaceRatio_bounds_of_retained_index` is parametric. Needs centralizer index ≥ 2¹⁶ in Gal(K/ℚ) (class of c₁ of size 2¹⁵ in G_B, doubled because c₁ and c₂ are not conjugate), giving θ ≥ 65535/131072. |
| Entireness of ζ_K/ζ_F | Uses √7 ∈ F (unit norms +1, χ₄∘N = sign on odd norms, (√7+i)/2 integral). Generalize to √d with d ≡ 3 (mod 4) prime and use √3 ∈ F: ≈24 files, ≈600 lines specific to 7. |
| Fixed-base analytic step (`eventual_normalized_log_relativeResidue_lt_of_fixed_base`, prime budget, `fixedBaseResidueCeiling_eq_zeta_logDeriv`) | Generic in M and ε; reuse. Only the bridge hard-codes ε = 1/12000 and M = RetainedField. |
| E → M_B corrections | **Done** (stream B, `UnitDistance/Sqrt241/Analytic/`, `Genus/`): `fixedBaseCeiling_lt_of_genus_bound` — from H on the canonical E (ceiling 852/10000) and M's local types at 2, 29, 7 and the census primes, `fixedBaseResidueCeiling M logRD (1/300) < 0.0495`; slack 5.4e-5. Also `Genus.finrank_carrier = 512`, `Genus.isGalois_carrier`, `Genus.exactLocalTypes`. See `docs/sqrt241/B_ANALYTIC.md`. |
| Canonical field and its isomorphism (ℚ: 19 modules, 2.3k lines) | Redo for E: 9 radicals with coefficients in ℚ(√241), degree 512, isomorphism to the actual genus field of G_B. |
| Root discriminant (ℚ: rational genus compositum, explicit dyadic generator √(−2+3i) with 13 ∈ S) | Does not transfer: the radicands of E lie in B and 13 ∉ S. Needs a new argument: disc(E) from its local types, and a dyadic ramified direction in M_B unramified outside S (or a local computation of the D-extension of ℚ₂, which is the same local field as over ℚ). |
| Arithmetic tower, inventory | Tower-side closure without geometry: 1,677 files, 532k lines. Generic: 1,408 files, 505k lines (Yamaguchi 490k; group augmentation, Jennings, class-two, tame, tensor/idele H², specified relators 15k). Reparametrize: 86 files, 10k lines (universal quadratic and retained quadratic groups, truncated Magnus certificates, cut group theory, block costs). ℚ-specific: 183 files, 17k lines, of which 41 files (3.9k lines: `MaximalProP*`, `ProPOpenNormalStage`, `ProPStage*`, `AbsoluteProP*`, `FinitePExtension*`, …) are ℚ only in their typing, and 142 files (13.3k lines) are ℚ arithmetic. Grep-based classification with hand corrections. |
| Relation bound (ℚ: dim H² ≤ 6) | Kummer image of each finite stage ≤ 2^{|S_f|}: finite places detect field-unit H² after adjoining i, because ℚ has one infinite place (`OneInfinitePlaceNorm`, `RationalFiniteFieldUnitsH2`), plus an inertia-correcting quadratic character whose existence is ℚ-specific (ideal-square radical ⟨−1⟩, the ℚ(√−3) character at 3). Over B: the product formula leaves a detection kernel of size ≤ 2 from the two real places, so a bounded-kernel version gives 2⁷; the correction needs radical ⟨−1, ε⟩ (h(B) = 1, N(ε) = −1) and a correcting place in S (a dyadic place, B_v = ℚ₂). Deep inputs (cyclic Hasse norm theorem, Artin product formula, H¹(G, C_L) = 0) are in the upstream library for general number fields. |
| Generators (ℚ: rank 7) | ℚ-specific (quadratic discriminants over ℤ). Over B: Kummer theory (odd valuation ⇒ ramified; upstream tools exist), h(B) = 1 (Minkowski bound 7.76), generators of the six S-primes, units modulo squares, non-squareness of the eight radicands, genus field of degree 2⁸. |
| Relators | ℚ: c² and five tame words; the dyadic place is the omitted one and its relation (initial form a² + [b,c]) is only shown to be a consequence. Over B: 7 of the 8 places, so at least one dyadic relation becomes a presentation relator with its global initial form in the 36-dimensional degree-two space; conjugation vectors become the sign vectors at the two real places; the ℚ_p local files need B_v ≅ ℚ_p bridges at the split places. |
| Levels and local data | The downstream interface needs `IsGalois ℚ K_j` and rational-prime indices. Over B the cut is Gal(B/ℚ)-invariant when the local cuts at conjugate places are defined from ℚ_p itself (the same local generators 5, −1, −2 at both dyadic places), so the levels can be chosen Galois over ℚ; otherwise the interface must be relativized to B. Centralizer index: the ℚ argument is finite group theory (`TruncatedMagnus*`); B needs index ≥ 2¹⁶. |
| Golod–Shafarevich inequality | `optimized_completed_presentation_positive` is generic in the generators and local blocks, with one dyadic slot carrying the saving s_D. Other blocks need injectivity on all layers; for D₃₂ at the second dyadic place the layers from 3 on are trivial, so retention in G/D₃ suffices (as `dyadicMap_comap_dimensionSubgroup` over ℚ). The B polynomial is done: [TowerPolynomial.lean](../UnitDistance/Sqrt241/TowerPolynomial.lean). |

## 3. Work packages

The plan as made at the start of the port, kept as a record. All work packages are
complete; §4 lists the delivered streams.

Estimates are in agent-days (one agent working continuously) and follow the
pace this project has shown. The ℚ presentation, relation bound and retained
family were still open on 2026-09-11. The final tower assembly — dyadic
relation, cut, local costs, field family, infinitude, rebuilt H² bound, full
build and audit — ran from 01:00 to 10:05 UTC on 2026-09-19
(`STATUS-HISTORY.md`). In this session the finite-place certificates for the
new witness went from nothing to compiled in about an hour. Most of the port
follows existing templates; the uncertainty sits in a few new arguments.

Mechanical (≈ 3–5 agent-days):

| WP | Content | Estimate |
|---|---|---|
| 0 | Statement, plan, build set-up | done |
| M1 | Witness data (Fin 11 → Fin 5), regenerated certificates, J_C and J_D enclosures (pair overlap for s′, or the mass chain for q ≠ 6/5), period separation, margin assembly | 1–2 (finite places done) |
| M2 | Entireness with √3 in place of √7 | ≈ 0.5 |
| M3 | Retype the 41 files that are ℚ only in their typing (`MaximalProP*`, `FinitePExtension*`, stages) to a number-field base | 0.5–1 |
| M4 | Regenerate the finite group certificates from the `lie241.py` data: retained quadratic group F₂⁸×F₂¹⁵, cut words, Magnus/centralizer certificates, block costs | ≈ 1 |
| M5 | Assembly, SolutionZeta241, audits, Comparator configuration | ≈ 0.5, plus machine time |

New arguments (≈ 5–8 agent-days):

| WP | Content | Estimate |
|---|---|---|
| N1 | h(B) = 1 (Minkowski bound 7.76), unit ε of norm −1, generators of the six S-primes, V of dimension 8, non-squareness of the radicands | 0.5–1 |
| N2 | Generators: quadratic extensions of B unramified outside S are B(√α), α ∈ V | 0.5–1 |
| N3 | Relation bound dim H² ≤ 7 with two real places: bounded-kernel detection, correction character over B | 1–2 |
| N4 | Relators at the 8 places: B_v ≅ ℚ_p bridges, one dyadic relation as a presentation relator, initial forms | ≈ 1 |
| N5 | Levels Galois over ℚ (local cuts defined from ℚ_p), local indices including (1,8) at 7, separation of c₁, centralizer index ≥ 2¹⁶ | ≈ 1 |
| N6 | Root discriminant ℓ_B | 0.5–1 |
| N7 | Canonical E and its isomorphism; E → M_B corrections; census of 18 primes | ≈ 1 |

Total ≈ 8–13 agent-days. With three or four agents in parallel, about 3–4
days of elapsed time. The chain N2 → N3 → N4 → N5 is the critical path; the
M items and N1, N6, N7 run beside it. N3 and N5 carry the risk: the ℚ proof
avoided real places by adjoining i, and fields over a base other than ℚ may
bring typeclass or elaboration problems. They should be attempted first.

Machine time comes on top: a fresh build takes about 3.6 hours, and the ℚ
package's comparator peaked at 102 GiB, so the final Palomar-style replay
needs a host larger than this one (31 GiB).

## 4. State and resume

Work is split into streams with notes in `docs/sqrt241/` (rules:
`docs/sqrt241/CONVENTIONS.md`; tower design: `docs/sqrt241/TOWER_PLAN.md`).
All delivered theorems use only `propext`, `Classical.choice`, `Quot.sound`.

| stream | scope | state | note |
|---|---|---|---|
| A1 | numeric margin (`Witness.uniform_margin`, κ = 1189/10⁷) | done | `A1_NUMERICS.md` |
| A2 | downstream chain on the new witness (`target_of_growing_galois_fields`, 87 modules) | done | `A2_GEOMETRY.md` |
| B | genus field E (degree 512, Galois, local types) and H → ceiling bridge (`fixedBaseCeiling_lt_of_genus_bound`) | done | `B_ANALYTIC.md` |
| C1 | base field ℚ(√241): h = 1, units, S-units, primes, local embeddings | done | `C1_BASE.md` |
| E | root discriminant: `log_rootDiscriminant_le` (and `…_of_sqrt_beta₁`: needs only √β₁ ∈ K, Galois), route-T variant `log_rootDiscriminant_le_of_retained_comparison` | done | `E_ROOTDISC.md`, `E_RD_DATA.md` |
| T0, T4 | pro-2 machinery over a number field; relation bound `Relation.OmegaB_h2` (H² ≤ 7, two real places via B(i)) | done | `T0_T4.md` |
| T1, T3, T6 | Galois-over-ℚ bridge (`Omega`, `Ghat`, `GB`, `sigmaHat`, `bridge`), generators (`genusLabel`, rank 8, `freeMap`), presentation (`relators_generate`, unconditional; `LocalElements` interface) | done | `T1_T3_T6.md` |
| T5 | local maps, labels, ℚ₂ local cut: `Local.localElements` with `localElements_presentation` (unconditional presentation), c₁/c₂, tame pairs, dyadic local maps, Frobenius at 29 and 7, `inertia_killed`, `localCut` (e = 8, f = 4), route-T kernel comparison | done | `T5_LOCAL.md` |
| T7, T8 | finite group data (Q_B of order 2²³, universal detector, dyadic maps, Magnus certificates: class of c₁ ≥ 2¹⁵), cut, GS; unconditional infinitude `Cut.B.actualQuotient_infinite`, Ĝ-normal `Cut.B.kernelHat` | done | `T7_T8.md` |
| T9, T10 | retained field M, levels, local indices, prime freedom, census | done | `T9_T10.md` |
| T11 | √β₁ ∈ M (route E: Kummer map on the D₄ extension, x₃x₅ vanishes on the 21 cut initials) and `hdiscM`: `DyadicLink.log_rootDiscriminant_input_M` | done | `T11_LINK.md` |
| T12 | assembly `Final.lean`, `SolutionZeta241.lean`, full axiom audit, `comparator-zeta241.json` | done | `SUBMISSION.md` |

Not every stream deliverable is used by the final proof: for example
`Cut.B.actualQuotient_infinite` and `Cut.B.kernelHat` (module `Cut/SigmaB.lean`, outside
the submission closure), `Local.localElements_presentation`, `log_rootDiscriminant_le`
(the proof uses `log_rootDiscriminant_le_of_sqrt_beta₁`) and route T
(`Discriminant/RouteT.lean`). [sqrt241/SUBMISSION.md](sqrt241/SUBMISSION.md) lists the
declarations on the proof path and the eleven modules outside the submission closure.

**Assembly.** `UnitDistance/Sqrt241/Assembly.lean`: `target_of_tower_data` combines the
downstream chain, the margin and the H bridge; its remaining hypotheses are exactly
the tower obligations (M with its local types, √3, √−1, rd(M); the growing family K_j
with local types, conjugation, prime freedom, index ≥ 2¹⁶). Axioms: standard only.

Top-level files: `ChallengeZeta241.lean` (statement), `SolutionZeta241.lean` (proof), `UnitDistance/Sqrt241/`
(`Target`, `Witness`, `CanonicalGenus`, `TowerPolynomial`,
`FiniteFunctionalCertificate`, and the stream directories). Evidence for H:
`papers/0.04273/certificates/h241_receipt.py`
(left side ≤ 0.0848336 < 0.0852).

Build: this worktree's `.lake/build` is a copy of the September 29 integration
build (Lean 4.35.0-rc2), whose 2,160 `UnitDistance` sources are identical to
this checkout; lake reports it up to date, so only new modules compile.
Check a single file with `./.toolchain/bin/lake env ./.toolchain/bin/lean <file>`.
