# Local verification of the 1.0427 conditional package (2026-09-29)

Scope: the pair `ChallengeZeta241.lean` / `SolutionZeta241.lean` and the new
modules under `UnitDistance/Sqrt241/`. Only local checks were run; no Palomar
verifier and no remote action. H is an explicit hypothesis and is not checked
here.

Environment:

* Lean `4.35.0-rc2` (commit `11acb17ec6b07a8f9e9173e6845197929540936b`)
* Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, from the shared read-only
  package set
* 8 CPUs, 31 GiB RAM

Source digests: `source-hashes.txt`. The hashes of `SolutionZeta241.lean` and
`ChallengeZeta241.lean` in the fresh copy equal those of the worktree:
`bca8b73b…62f4` and `f5568120…6358`.

## 1. Fresh build

`lake build SolutionZeta241 ChallengeZeta241` ran in a clean copy of the sources,
made by `tar` with `.lake`, `.cache`, `verification`, `dist` and `research`
excluded, and with no project build artifacts.

* **BUILD_OK:** 6,960 jobs in 59 min 41 s wall (428 min CPU).
* **Errors:** 0.
* **Warnings:** 2,433 in the whole closure. Almost all are Mathlib deprecation
  and style lints in inherited modules. The Challenge's only warning is its
  placeholder `sorry`.

Summary: `fresh-build-summary.txt`.

## 2. Axiom audit on the fresh build

The script `import SolutionZeta241`, `import AuditSupport` ran:

* `#print axioms UnitDistanceSqrt241Submission.target_of_canonical_genus_zeta_bound`
* `UnitDistanceAudit.audit` for `UnitDistance`
* `UnitDistanceAudit.audit` for `UnitDistanceSqrt241Submission`

Results:

* The theorem depends on `[propext, Classical.choice, Quot.sound]`.
* All 56,018 `UnitDistance` declarations in the closure, including private
  auxiliaries and attributed ports, have exactly that transitive axiom union.
* So do all 32 submission declarations.

Log: `full-audit.log`.

## 3. Kernel replay

`lake env leanchecker <module>` ran one module at a time on the fresh build.

* All 239 modules pass (`rc=0`): the 237 `UnitDistance.Sqrt241.*` modules in the
  closure of `SolutionZeta241`, plus `ChallengeZeta241` and `SolutionZeta241`.
* 12 modules are outside the closure and have no build artifacts: the 11 extras
  listed in `docs/sqrt241/SUBMISSION.md` and the umbrella `UnitDistance.Sqrt241`.

The inherited ℚ-package modules in the closure are unchanged. They were
replayed in the ℚ package's own verification (`verification/migration-20260929/`).

Log: `replay.log`.

## 4. Not run here

* Comparator statement/definition comparison. The configuration is
  `comparator-zeta241.json`; the ℚ package's comparator peaked at 102 GiB,
  above this host's memory.
* NanoDa, con-ron and the protected export/replay pipeline of the Palomar
  verifier.

These remain to be run on a suitable host before any submission.

## 5. Independent reviews

Two fresh-context reviews (statement; code) are summarized in
`docs/sqrt241/REVIEWS.md`.
