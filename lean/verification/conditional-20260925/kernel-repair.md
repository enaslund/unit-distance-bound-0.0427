# Independent-checker repair, September 26

Candidate 19 completed its fresh Lean build, proof export, structural
comparison and configured axiom check. Lean's default kernel accepted the
exported solution. Its full verifier result was nevertheless a failure:
con-ron terminated with exit 143 and NanoDa aborted with a stack overflow.
These are distinct failures, not evidence of a completed independent check.

## Diagnoses

The host journal identifies con-ron's termination at September 25 18:49:31
UTC: earlyoom sent SIGTERM when available memory reached 3,093 MiB and no
swap was configured. con-ron's resident memory was 24,447 MiB. The phase's
zero cgroup OOM count did not detect this host-level termination. See
[the journal extract](independent-checker-earlyoom.log).

A diagnostic build of the exact pinned NanoDa source added declaration-entry
and exit logging, without changing checking rules. It identifies the
overflowing declaration as
`UnitDistance.Witness.pairMassBracketScalarsQ_eq_data._proof_1_1`.
The other workers were checking adjacent generated proofs of the same lemma.
The diagnostic build is evidence about the failure location, **not an accepted
checker for submission**. Its source patch, digest and execution receipt are
in [kernel-repair](kernel-repair/nanoda-diagnostic-run.json).

## Source change

In `UnitDistance/PairMassDegree3DenseComputationCertificate.lean`, the proof
of `pairMassBracketScalarsQ_eq_data` is assembled from 256 private scalar
equalities. Each scalar proof rewrites the already-proved cell center or
radius, selects the existing table entries by a definitional `change`, and
uses `norm_num` to produce an exact rational-arithmetic proof. The final
vector equality uses those scalar lemmas structurally. Previously, each
vector case asked `decide +kernel` to recompute the rational expressions.
A preliminary rewrite-only variant compiled but still exhausted memory in
NanoDa; that failed experiment motivated the scalar split.

The bracket replacement exposed a second reduction bottleneck in
`pairMassCellRadiusQ_eq_data`, which the original failing export had not yet
checked. Its 64 cell equalities now select their table values definitionally
and prove the polynomial arithmetic with `norm_num`. The existing center
proof remains unchanged. Thus the final repair contains 320 scalar
certificates, with no changes to the input tables.

The lemma statement, numerical data, target theorem, hypothesis H and allowed
axioms are unchanged. The complete revised module compiled with Lean
4.35.0-rc2 in 145 seconds; see the
[compile receipt](kernel-repair/candidate20-cell-module-compile.json) and
[source promotion receipt](kernel-repair/candidate20-cell-source-promotion.json).
The tested module SHA-256 is
`6d7b6d6f8f8a3213da3edd4556076da0ea27bb9aa59a9a49c33c3377a82d90d0`.
The [bracket generator](kernel-repair/generate-bracket-certificates.py) and
[cell generator](kernel-repair/generate-cell-certificates.py) also compare
the existing numerical entries using Python fractions. Those computations
are diagnostic; the exported Lean proofs do not trust them.

The [focused replay](kernel-repair/candidate20-focused-check.json) used the
unchanged bundled checker binaries on an export of the bracket theorem and
its complete dependencies. **Both passed:** NanoDa in 9.09 seconds and con-ron
in 33.10 seconds, with 6,775 declarations accepted by con-ron. The scope's
peak memory was 661,966,848 bytes (about 631 MiB), without cgroup memory-limit
events. This confirms the repair on that dependency closure. A fresh full
submission run remains a separate obligation.

## Resource setup for the rerun

The repair uses a temporary 16 GiB swap file; earlyoom remains enabled and
persistent swap configuration is unchanged. Other workloads are currently
active on this host. The rerun's outer scope exposes 20 GiB of RAM to the
unmodified standard verifier, whose phase limits are 95%/98% of that amount.
Two inherited CPUs reduce con-ron's automatic worker count. This changes
available resources, not checking rules. The host memory guard still stops
the owned build if available RAM falls below 2 GiB.

The launcher permits the standard 19,800-second execution window, followed
by the existing auxiliary axiom audit only on success. The cleanup script
disables and removes only this run's temporary swap file when the build lock
is free and sufficient RAM is available. Otherwise it retains the file and
an explicit cleanup-required receipt. No official Palomar submission is made.

The authoritative full-run verdict belongs to the exact archive's execution
receipt, not to an incremental build or a diagnostic checker run.
