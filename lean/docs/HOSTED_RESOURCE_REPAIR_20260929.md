# Proof changes for hosted verification

The source snapshot contains proof-only changes in
`UnitDistance/RetainedDiscriminantBridge.lean`. Its nine existing public theorem
statements and the definition `expectedAbsoluteDiscriminant` are unchanged.
It also subdivides the finite checks in `UnitDistance/DyadicCertificates.lean`;
all 42 theorem statements and 33 definitions, including certificate data,
remain unchanged, and its generator reproduces the revised file exactly.
The selected Challenge, geometric definitions, exponent and explicit hypothesis
H are also unchanged. H remains unproved in Lean.

The preceding source archive,
`ce3efb15aa685b27c4a86ac9d9b34f0f998c11f01c12241301e5dba7ca2bcaf0`,
passed the complete protected Palomar pipeline locally on September 29,
2026. That run used a host with approximately 121.9 GiB of RAM and reached a
102.04-GiB comparator peak. It did not establish fit on hosted runners.

A separate diagnostic used the same official con-ron binary and accepted
export, with progress logging enabled. Of 149,182 pending checks, 149,180
finished while the two root-discriminant bridge proofs remained. Anonymous
memory subsequently reached approximately 97.3 GiB. The last outstanding
declaration was
`UnitDistance.CanonicalRetained.log_rootDiscriminant_le_logRD_of_genus_and_relativeDifferent`.
This diagnostic was intentionally stopped after attribution; it was not a
new terminal verification verdict.

An initial symbolic refactor still forced con-ron to compare a named natural
discriminant bound with its expanded product of huge powers. Its separate
four-CPU replay failed at the Standard memory limit after 149,177 of 149,179
checks. This failed candidate and its receipts remain preserved.

The revised selected proof establishes and composes cast and power-product
inequalities first for variable natural numbers. It then substitutes the
required constants and carries the bound directly into the real-valued
logarithmic argument. This avoids the named natural-bound conversion in the
selected proof's dependency closure.
Separate elementary equalities check
`131072 + 256 * 4096 = 1179648` and `64 * 4096 = 262144`, allowing the proof to
retain symbolic powers instead of normalizing huge closed natural numbers.
The private helpers use ordinary Lean proofs and introduce no axioms or
unverified computation.

The finite dyadic checks are split into 544 individual row/action cases using
`fin_cases` and ordinary `decide +kernel`. Previously each complete finite
universal statement was discharged in one kernel reduction. The subdivision
is intended to reduce transient verification memory; it does not change the
certificate data or replace kernel checking with a trusted computation.

This document describes the source change, not its final verification result.
The source archive must be frozen before its new full run, so subsequent
receipts are distributed separately and identify the archive and exact source
hashes they certify. A complete result requires a fresh project build,
protected Challenge and Solution exports, statement/definition comparison,
the permitted-axiom check, and con-ron, NanoDa and Lean kernel replay. The
earlier successful archive does not certify a changed proof export.

For the current published profiles, local capacity reproduction targets four
CPUs and aggregate 16 GiB for Standard, or 16 CPUs and aggregate 32 GiB for
Namespace. These are deliberate hosted-capacity tests, not general research
limits. Every phase must share the bounded ancestor: bounding only an outer
systemd scope is insufficient because the official verifier starts sibling
scopes. The verifier and its protected kernel commands remain unchanged.

The module-system migration records under `third-party/module-system-20260928`
describe the preceding compatibility layer. This later, project-owned proof
refactor is separate from that historical layer and does not modify vendored
upstream sources or attribution.
