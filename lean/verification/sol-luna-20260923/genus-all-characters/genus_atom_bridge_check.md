# Finite atom/Kronecker bridge check

## Purpose and status

`genus_atom_bridge_check.py` is a stdlib-first finite checker for the
paper-level local factorization in `kronecker-factorization-argument.md`.
It enumerates all 128 seven-bit masks and every residue representative
`n = 0, …, |D|-1` for that mask's expected fundamental discriminant `D`.
For each pair it compares the explicitly computed 2-primary atom times the
selected Legendre atoms against a separate algorithm for the Kronecker
symbol. When python-flint is installed, it also compares every value against
the Conrey character selected by `genus_full_direct.py`.

The checker passed under the guarded shared-resource policy. Its result is
`genus_atom_bridge_check.json`: all 128 masks and 677,376 residue classes
passed against the standalone Kronecker implementation, and all 677,376
values passed against python-flint's Conrey characters. This is finite
evidence over these conductor periods. It does not establish the missing
all-mask Lean theorem `(assembledDatum m).χ n = (D/n)` or the analytic
correctness of FLINT's computation.

## Formula checked

For mask bits `a,b,c,d,e,f,g`, the checker uses

```text
O = 3^c 5^d 7^e 11^f 13^g
r = a + c + e + f (mod 2)
D = δ if δ = (-1)^a 2^b O is 1 mod 4, and 4δ otherwise.
```

Its odd factor is the product of Euler-criterion Legendre values `(n/q)` for
selected `q ∈ {3,5,7,11,13}`. Its 2-primary factor is `1`, `χ₄`, `χ₈`, or
`χ₈′` in the four cases `(b,r)=(0,0),(0,1),(1,0),(1,1)`. Euler's modular
exponentiation returns zero at odd selected divisors. The two-primary cases
also return zero on even `n` whenever the discriminant is even. At `n=0`,
the independent symbol routine uses Dirichlet-character period semantics:
value one only for `D=1` (conductor one), and zero for every other row.

The reference Kronecker routine strips powers of two from the denominator,
applies the supplementary factor determined by `D mod 8`, then evaluates a
standalone Jacobi-symbol loop on the positive odd part. It does not use the
local-atom formula. The optional FLINT comparison uses the existing
`conrey_number(D)` label routine, whose source is independently pinned.

## Pinned inputs

Before enumerating, the script verifies SHA-256 hashes for the paper-level
factorization note and existing Conrey reference script, which must always be
present. It also verifies the local atom, conductor, primitive assembly,
character-bridge, and reciprocity Lean source hashes whenever those files are
present. Any present-file mismatch fails the run. Extracted candidate
packages may omit research Lean files: in that package-only mode the result
records the absent Lean pins and explicitly says they were not re-verified.
The reference script and factorization note are resolved beside the checker,
while Lean pins are resolved only for the full checkout layout. This avoids
treating an extraction parent as the repository root.
The exact expected hashes are recorded in `SOURCE_SHA256` in the checker; the
final JSON records the hashes verified in the run. This binds the finite
comparison to the inspected inputs; it does not prove the Lean statements.

The total expected period size is `677376`, matching the conductor-sum
identity in `GenusDirichletRowDataRun20260920.lean:108` and its conductor
wrappers. The checker asserts this total and records per-mask residue counts
and value digests.

## Evidence boundary

Lean source already proves that the primitive family character agrees
pointwise with `assembledDatum` (see
`GenusDirichletRootNumbersActualRun20260920b.lean:1047–1055`). The paper note
explains the local-atom/Kronecker identity and labels the general
all-integer identity as not yet formalized. This script can test all values
on the finite conductor periods; it cannot replace the missing Lean theorem
or prove equality for all integer arguments. In particular, a pass should be
reported as finite arithmetic evidence, while the formalization gap remains
open.

## Result and worker usage

Syntax and source-pin checks passed in the full checkout (12/12 pins). A
simulated extracted-package layout also passed: it verified the two mandatory
adjacent inputs and explicitly reported 10 absent Lean source pins.

Three guarded attempts deferred with exit 75 before the checker launched; the
guard reported shared-lock or host/cgroup headroom insufficiency. The first
admitted attempt had 16.5 GiB host available and 1.13 GiB cgroup headroom but
exited 1 immediately: python-flint returns an `acb` from `char(n)`, so the
initial checker's `int(char(n))` conversion was invalid. The checker was
corrected to compare the `acb` directly with the expected integer and hash
the already-matched integer. The successful run below used this corrected
source.

The final guarded run used the shared lock
`/tmp/lean-formalization-1000.build.lock`, host thresholds 10 GiB admission / 6
GiB stop, and cgroup thresholds 1 GiB admission / 0.5 GiB stop. It was admitted
with 16.5 GiB host available and 1.13 GiB cgroup headroom and completed with
exit code 0. It checked all 128 masks and 677376 residue classes, including
512211 zero values, against the standalone Kronecker routine and all 677376
values against the Conrey characters from python-flint 0.9.0. Python was
3.13.5; the checker-reported wall time was 4.261 seconds. The exact per-mask
counts and digests are in the JSON result.

The final checker source SHA-256 is
`a3200ec3b0ce2a3f73efb4c840043dfa0484318d3b4372e9d3f00330d90857ef`; the result
JSON SHA-256 is
`98780685630ce51bfef3eb1bb4d39b67c313095e7f028d1f35e782dde33ed6de`. All 10
pinned Lean source hashes and both mandatory local reference hashes verified
in the final run. The script wall time is available; per-worker CPU time and
peak memory are unavailable because external process telemetry was not
recorded. This finite result does not close the all-integer Lean proof gap
described above.
