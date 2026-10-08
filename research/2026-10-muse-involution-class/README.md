# A conditional route to exponent 1.043172 (Muse run of 2026-10-06)

Status: **conditional, and not reviewed outside the Muse run.** This folder keeps the one
lead of the Muse research branch `muse/muse-unit-distance-bound-20261006-025128/main`
(821 commits, deleted on 2026-10-08) that bears on the main result. Everything else on that
branch was dropped; see the last section. The notes and checks are Muse's, with paths
rewritten from `research/muse/` to this folder.

## The claim

At delta = 0.043172 the certificate of [papers/0.043171](../../papers/0.043171/README.md)
fails. With the involution class of size 2^15 used there, theta_min = 1/2 - 1/(4 N) =
65535/131072, and with general shell weights the threshold is C <= 0.0422631. The best
certified ceiling is C_eff <= 0.04226506 (E_W'', 36 abscissae, census to 8.5e14; Section 11c
there).

The Muse run claims the class can be doubled:

> **Claim (uniform defect).** The 41-cap tower group G_B has a quotient Q = G_B/V with
> D5 <= V <= D4 and [D4 : V] = 2, of order 2^50, in which the class of iota_1 has at least
> 2^16 elements. Tower fields of every 2-power degree >= 2^50 map onto Q, so N_iota >= 2^16
> and theta >= 1/2 - 2^-18 = 131071/262144.

At the margin slope dM/dtheta ~ 0.625, the extra 2^-18 in theta adds about 2.4e-6 to the
margin. The threshold at delta = 0.043172 then becomes C <= 0.0422655 (C154: allowable
lower endpoint 0.042265483), above the certified 0.04226506. The margin would be about
+4.3e-7, that is, exponent 1.043172.

## The chain

| step | statement | sources here |
| --- | --- | --- |
| H2, exhaustion | R4 = I4 + span of 28 lift-dependent syzygy corrections; g4 in [53, 81] | `notes/reviewed/R5-no-c4-g4bound.md`; proof in `corpus/C126-g4-lower-bound.md` |
| H1a, H3, containment | the actual R4 lies in TOTAL_full240 (37-dimensional; 33 after the C129 repair) | `notes/reviewed/R5-defect-bundle.md`, `R5-genuine-lift.md`; `corpus/C129`, `C148`, `C161` |
| separator | the ad3 images escape TOTAL (rank 18/18, witness [X_0^2, X_1]), so [s, iota_j] lies in D4 but not D5 for both involutions | `notes/reviewed/R5-uniform-defect.md`; `corpus/C127-*` |
| quotient | the defect gives Q of order 2^50 with class >= 2^16 | `corpus/C93-quotient-repair-check.md` Section 4a; `notes/reviewed/R5-quotient-repair.md` |
| fields and margin | transfer to tower fields (Lemma D) and the threshold table at 0.043172 | `corpus/C86-r5-signature-threshold-check.md`; `notes/reviewed/R5-signature-threshold.md`, `R5-margin-accounting.md`; `corpus/C62`, `C154` |

## Status

* **Checks inside the Muse run.** Each link was checked by an agent of the same run: C126,
  C127, C129, C148, C161 (a second opinion on containment), C86, C93 and C154. None rejected
  the chain. These are not independent reviews in the sense of AGENTS.md.
* **Open by the run's own records:**
  * the exhaustion step H2 rests on the single proof in C126 (C151 rejected a different
    exhaustion argument);
  * the infinitude of the 41-cap tower is taken from papers/0.042901;
  * the field transfer (C86 Lemma D) is checked only as applied here;
  * the margin with general shell weights at the new theta has not been replayed.
* **Reproduced on 2026-10-08 from master.** These scripts all exit 0 when run as
  `.venv/bin/python -B <script>` from the repository root:
  * `code/R5/robust_defect.py` (certificate fingerprint c150066198ceb819);
  * `code/R5/total_margin.py` (fingerprint 0998513c045145e5);
  * `code/R5/validate_chain.py` (12/12), `margin_replay.py`, `no_c4.py`, `collection_check.py`;
  * the checks `code/C161` (76 checks), `code/C148` (65), `code/C127`, `code/C126`, both of
    `code/C86`, and `code/C93`.

  `robust_defect.py` and `total_margin.py` rewrite the two certificates in `code/R5/`
  (byte-identical) and write `.muse-scratch/` at the repository root; delete it afterwards.

## To bank 1.043172

1. A fresh-context review of the chain above, above all C126's exhaustion argument and C93
   Section 4a.
2. A witness at delta = 0.043172 with theta_min = 131071/262144, the E_W'' ceiling of
   `signed3.py W4` (C_eff <= 0.04226506) and general shell weights, with a replay.

## What else the run did (not kept)

* It proved no improvement.
* A fourth cap at the B-prime above 887 with code 31 keeps the tower infinite (P_3 + t^5 < 0;
  Muse's C150), but its profit is negative at delta = 0.043171 (C152).
* Non-normal subfields gave one field with theta = 127/256, and no unbounded family.
* Weighted and subgroup Golod-Shafarevich screens were negative or inconclusive.
* It recomputed one degree-8 L-value: family (19, 23), twist 0, at sigma = 1001/1000, with
  its own sieve and summation, giving 2.2517125696636191 +/- 2.4e-11. Ours is
  2.2517125696434072, with error radius about 2.0e-11, so the two agree within their radii.
  It reuses our `gkernel.py` and tail code, so it is a partial check of the degree-8 pipeline.
