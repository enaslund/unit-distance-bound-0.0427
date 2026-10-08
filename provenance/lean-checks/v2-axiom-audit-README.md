# Version 2 axiom audit, October 8, 2026

> Copied from `lean-formalization/verification/sqrt241-v2-20261008/README.md` of the research repository at commit `a5273110`; links point to the copies in this directory.

Sources: branch `lean-1.04317` after commit `3e67ea69` (the version 2 Challenge and Solution,
theorem `UnitDistanceSqrt241Submission.target_of_wide_zeta_bound`).

`scripts/verify-current.sh` builds the Challenge and Solution of both conditional theorems and
`AuditSupport`, then runs [audit/Sqrt241V2Audit.lean](v2-axiom-audit-Sqrt241V2Audit.lean.txt) and
`verification/ZetaAudit.lean`. Results ([log](v2-axiom-audit-verify-current.log), with build progress
lines and per-declaration progress lines removed):

* `#print axioms` for the Submission theorem, `V2.target_of_wide_zeta_bound`, `V2.towerDataV2`,
  `Wide.wideLocalTypes`, `Analytic.fixedBaseCeiling_lt_425_of_wide_types` and
  `Witness.uniform_margin`: `[propext, Classical.choice, Quot.sound]`.
* `UnitDistanceAudit.audit` over all 59,452 project declarations in the import closure of
  `SolutionZeta241` and over the 55 declarations of `UnitDistanceSqrt241Submission`: complete
  transitive axiom union `[Quot.sound, Classical.choice, propext]`.
* The 1.0418235 theorem (49,302 and 37 declarations): the same three axioms.

These are imported axiom queries on the pinned toolchain, with the cached-summary limitation
described in `verification/hosted-fit-20260929/requirements/axiom-audit-15226.md`. They do not
replace the pinned Palomar pipeline (protected export comparison, con-ron, NanoDa, Lean's
kernel), which has not been run on version 2.
