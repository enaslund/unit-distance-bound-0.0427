# Version 2 of PALOMAR-2026-10-01-000018: plan

Started 2026-10-08. Branch `lean-1.04317` (worktree `../lean-1.04317`).

## Target

Version 1 registers `UnitDistanceSqrt241Submission.target_of_canonical_genus_zeta_bound`:
the planar sequence theorem at exponent 10427/10000, conditional on H241 (a zeta inequality
for the degree-512 genus field E). Version 2 keeps the same repository
(`enaslund/unit-distance-bound-0.0427`), project path (`lean/`) and comparator configuration
path (`lean/comparator-zeta241.json`), as Palomar requires for a new version, and proves:

* exponent **104315/100000 = 1.04315** (paper: 1.043171, `papers/0.043171`), for the
  41-cap tower over B = Q(sqrt 241) (caps at both primes above 29 and at the prime P41[1]
  above 41, none at 7; `papers/0.042901`);
* conditional on one inequality **H_W** of the form of H241 for the explicit field
  E_W = E(sqrt beta_1, ..., sqrt beta_4) of degree 8192, the beta_i of the dihedral forms
  24, 20, 17, 7 of `d4all27.json` (`CanonicalWide.lean`); these span the same space W'' as the
  forms 10, 23, 19, 17, so E_W is the field E_{W''} of the manuscript (Section 5) and of
  `papers/0.043171/README.md` (Sections 8, 11b, 11c; data `certificates/dihedral/vd4_data27.gp`,
  `d4all27.json`, `ddata_orb{10,23,19,17}.json`):

      log(Re zeta_{E_W}(1 + 1/4411))/8192
        + (1/4411)((ell - gamma - log 4 pi)/4 - Re(logDeriv zeta_{E_W} 2)/8192) < X_W.

Not formalized and not needed: the D4 census beyond norm 1000, the adaptive dichotomy
(Props A, B), Prop D, the signed kernel (Prop E), general shell weights.

## Why 1.04315 suffices with a single abscissa

`dihedral_ceiling3.py W4x` (no census credit, no adaptive gains), best sigma 4412/4411:

| primes with known f >= 4 | C over E_W |
| --- | --- |
| norm <= 100 | 0.0425782 |
| norm <= 1000 | 0.0424341 |
| norm <= 10^6 | 0.0424203 |

Lean margin (the paper's `geom241.margin`, which reproduces version 1's 1.1917e-4 at
delta 0.0427, C 0.0495), types 2, 3, 5, 29, 41 with 41 as effective (2,4):

| pair profile | finite shells | delta | margin at C = 0.04243 |
| --- | --- | --- | --- |
| version 1 (0.0418235 manuscript) | optimized at 0.04315 (`opt0.043150`) | 0.04315 | +9.56e-5 |
| version 1 | optimized at 0.043155 | 0.04316 | -1.47e-4 |
| re-optimized (witness_0.043171) | optimized at 0.043155 | 0.04316 | +1.04e-4 |

A new pair profile would need a new pair-overlap lower bound (version 1 reuses the 28 modules
of `UnitDistance.Witness.pairOverlap_coarse_lower`, which have no generator). So version 2
keeps version 1's pair profile and targets delta = 0.04315; the margin stays positive for
ceilings up to about 0.04252, and the ceiling is set to 0.0425.

## Structure (what changes from version 1)

* **M is unchanged.** `Retained.Input.core` is the sigma-core of `retainedKer`, which contains
  D_4(G_B); cap elements are fourth powers, hence in D_4. So the fixed base M = Omega^core is
  the same field for the 41-cap tower and stays Galois over Q; its types at 41 are (1,4) at
  both primes (Frobenius squares outside R2).
* **Levels.** The cut subgroup with the single 41-cap is not stable under sigma-hat, so the
  tower fields K_j are Galois over B only. `Input.frob7_compat` and the sigma-symmetric cap
  data change.
* **Outer planar theorem.** `Geometry/FixedBaseBridge.lean` `target_of_growing_galois_fields`
  assumes `IsGalois ℚ (Ks j)` and rational-prime types. Its inner theorems
  (`target_of_witnessFields_of_residueCap`, `target_of_witnessFields_entire_fixedBase`) do not;
  the 41 windows enter as effective type (2,4) with residue field 41^4 (count d/8 of F-primes),
  exactly matching `hmultiplicity`. Needed: a wrapper for fields Galois over B, with
  theta from the class of c in Gal(K/B) (2^15, theta_min = 65535/131072).
* **Analytic bridge.** `Analytic/Bridge.lean`, `Analytic/GenusBridge.lean` compare zeta_M with
  zeta_E at rational primes. Version 2 compares with zeta_{E_W}; E_W is Galois over B (not
  necessarily over Q), so its Euler factors are evaluated per prime of B. Corrections at the
  dyadic primes, 29, 41, 7 and all primes of B of norm <= 1000 with f_M >= 4 and
  f_{E_W} <= 2.
* **E_W inside M.** Elements of D_4(G_B) fix E_W (Gal(E_W/B) has class 2, exponent 4, so its
  D_4 is trivial). The remaining generators of `core` (dyadic and tame cut elements) must act
  trivially: local compatibility of E_W at 2, 3, 5.
* **Numerics.** New witness at delta = 0.04315 with local types 2, 3, 5, 29, 41 (effective
  (2,4)); version 1's pair profile; finite shells from `opt0.043150` padded to six weights;
  regenerated finite and pair-mass certificates; `Witness.ceiling = 425/10000`.

## Work items

| item | owner | status |
| --- | --- | --- |
| W1 outer wrapper over B | parent | done: `V2.TowerData` with windows (`V2/Interface.lean`), the signature bound through the detector field (`V2.thetaMin_le_signatureRatio`, `V2/Signature.lean`) and `V2.TowerData.target` (`V2/Outer.lean`) |
| W2 41-cap levels, types and freeness at P41[1], theta over B | worker (branch `lean-v2-tower`) | done: `V2.towerDataV2 : V2.TowerData` (`V2/Tower.lean`; cut `V2/Cut41.lean`, levels `V2/Levels.lean`, types `V2/Types.lean`, window at 41 `V2/Cap41Prime.lean`, `V2/Window41.lean`, freedom `V2/Freedom.lean`); axioms propext, Quot.sound, Classical.choice; `V2.TowerData.target towerDataV2` typechecks. Version 1's `Assembly`, `Levels/Export` and `Final` no longer applied to the version 2 `Witness` and were removed (commit `a77b59f8`) |
| W3 E_W: definition, degree 8192, Galois over B, residue-degree bounds, E_W <= M | agent (branch `lean-v2-ew`) | done: `CanonicalWide.field` (forms 24, 20, 17, 7 of `d4all27.json`, spanning W''), `Wide.finrank_field` (8192), `Wide.field_le_M` / `Wide.wideToM I : E_W →ₐ[ℚ] I.M` (every retained input), `Wide.wideLocalTypes : WideLocalTypes CanonicalWide.Carrier` (`Wide/LocalTypes.lean`; dyadic `Wide/Dyadic.lean`, census `Wide/Census.lean`, `Wide/CensusData.lean`); axioms propext, Quot.sound, Classical.choice; `V2.target_of_wide_types Wide.wideLocalTypes` typechecks. Not formalized: Galois over B as an `IsGalois` instance (not needed). E_W is not Galois over Q (the conjugate forms are 13, 12, 22, 3) |
| W4 analytic bridge with E_W; generated corrections | agent | done (branch `lean-v2-analytic`): `Analytic.fixedBaseCeiling_lt_of_wide_types` / `..._425_...`, interface `Analytic.WideLocalTypes`; see `docs/v2/W4_ANALYTIC.md` |
| W5 margin witness and certificates at 0.04315 | parent | done (`Witness`, `Numerics/*`, `FiniteCertificates`) |
| W6 external evidence for H_W (`h_w_receipt.py`) | agent (branch `lean-v2-ew`) | done: `papers/0.043171/certificates/dihedral/h_w_receipt.py` (+ `.json`): certified left side of H_W at 1 + 1/4411 is at most 0.0509171473 < X_W = 0.050969 (Y_W from the certified L-values of `DC3` space W4x; log-derivative term from residue degrees of primes of B up to 10^6 with an explicit tail). Numerical evidence, not a proof |
| W7 Challenge/Solution v2, comparator, axiom audit, pipeline | parent | partly done: `V2/Final.lean` (`V2.target_of_wide_zeta_bound`), Challenge/Solution v2 with `target_of_wide_zeta_bound`, comparator, `lake build` and `lake build UnitDistance`, `#print axioms` (three permitted axioms) (commit `a77b59f8`); exporter, shipped README, metadata and development account for version 2 (exporter needs `papers/0.043171` with the manuscript, so it runs on a commit that carries both). Not done: the full-closure audit, the complete pinned pipeline, publication of the manuscript and package in the public repository (owner's decision), the registry request |
