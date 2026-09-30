# Candidate 15 package and preflight record

Status: **local candidate prepared and archive-only checks passed**. This is
not a Lean build, proof audit, fixed-field zeta verification, official Palomar
result, or submission. The selected project proof inputs are byte-identical
to both sealed candidate 14 and candidate 07.

## Frozen archive

- Archive: `dist/conditional-20260923/conditional-source-15.tar.gz`
- SHA-256: `7585c6dcd7806503237142df9a8544561a08d2cb9291e684991981d6b6cf4632`
- Archive bytes: 6,991,706; snapshot SHA-256:
  `5e4f0b6986b0be2180a73dae3a20fb8cf96b411611199c7b83c2eaeee8e94c3d`
- Inventory: 2,409 files (2,163 project modules, 172 referenced records, 6
  external-zeta records, and 14 manuscript files); 34,982,615 source bytes.
- Selected configuration: `comparator-zeta.json`; no missing references;
  export did not perform proof verification or remote submission.

The exporter starts from the import closure of `ChallengeZeta`,
`SolutionZeta`, and `AuditSupport`, then adds the fixed package surface,
curated manuscript files, third-party provenance, and explicitly referenced
records. It rejects dangling references and excludes `dist/`, `.lake/`,
`.cache/`, build outputs, symlinks, compiled artifacts, and research files
outside the import/reference closure. Candidate 15 includes the finalized H7
mixed-quartic evidence, the all-mask atom checker and report, and the current
policy compatibility note through existing document globs. The standalone
`ZetaLuna*` and `ZetaSolGenus*` research Lean modules remain outside the
selected proof closure.

## Checks

`check-15.json` passed archive extraction, deterministic re-export, source
manifest checks, and the pinned metadata contract. The archive SHA and
snapshot SHA match the export receipt; sources were unchanged during the
check. No Lean build, axiom audit, or independent kernel replay ran.

`proof-input-identity-15-vs-14.json` and
`proof-input-identity-15-vs-07.json` both report `passed: true`,
`lean_files_identical: true`, `proof_input_files_identical: true`, and an empty
`changed_proof_inputs` list. Documentation and metadata changed; these
comparisons do not claim proof verification.

The extracted candidate's metadata loaded successfully under the current
Palomar `submission_contract` at commit
`e48a86d0495356b5131a92c9406aa6e27cf99e56`. A direct current policy smoke on
candidate 15 records `toolchain.unsupported`: project Lean `v4.32.0` is below
the current `v4.35.0-rc2` floor. Metadata validation passed separately. This
is a bounded policy check only; the full verifier, Lean build, and registration
were not run. Candidate 15 is not ready for current full intake until migrated
to a supported Lean/Mathlib pair.

Two package-only finite numeric checks passed on the extracted archive with
python-flint 0.9.0:

- The full-genus Arb replay checked all 128 mask rows and 677,376 character
  period values against its portable comparison fixture. All values lie in
  the fixture intervals, and the aggregate is below the stored linear
  allowance. It ran in fixture-only mode: inherited research archive data and
  Lean modules were absent from the extraction, and therefore not re-verified
  in that run.
- The atom checker checked all 677,376 residues across 128 conductor periods
  against its independent Kronecker routine and all 677,376 FLINT Conrey
  coefficients. It explicitly records 10 absent research Lean source pins;
  its adjacent script and factor note hashes were verified. This is finite
  arithmetic evidence, not the missing all-integer Lean character identity.

The extracted package's September 22 supplemental smoke also passed all 17
finite scripts: the 10 base scripts, optional one-factor AFE script, and all
6 extended checks (H7 suffix, quartic composites, three genus-13 checks, and
Hecke all-row prefix). Each exited 0. The driver was
`verification/conditional-20260922/package-smoke.py`, SHA-256
`86c7db41866b6712ffe78efdab2e4ccc6f366b3947022f23ff51bdec9ad48dea`; it ran
against the extracted candidate with `--include-afe --include-extended`,
`PYTHONPATH=/tmp/unit-distance-flint`, and the frozen archive hash pinned.
The receipt is `package-smoke-15.json`. This exercises only the listed
external finite scripts; it does not perform Lean verification or prove H.

The candidate's portable comparison fixture and scripts are shipped. The
candidate-specific export, check, identity, current-policy, and extracted
package-smoke receipts below were written after export and are local
verification records, not members of the already frozen archive.

## Receipts

- `export-15.json`
- `check-15.json`, plus `check-15-determinism.log` and
  `check-15-metadata.log`
- `proof-input-identity-15-vs-14.json`
- `proof-input-identity-15-vs-07.json`
- `current-policy-smoke-15.json`
- `genus-full-package-smoke-15.json`
- `genus-atom-package-smoke-15.json`
- `package-smoke-15.json`

The archive SHA-256 is also recorded above. Archives 14 and 07 were not
modified.

## Commands and resource accounting

Export, check-only, both identity comparisons, the current-policy smoke, and
both package-only numerical runs were executed serially through
`automation/lean-formalization/guarded_build.py` with a 900-second timeout and
the shared slot. No thresholds were changed and no Lean compilation was run.
The two numerical outputs report wall times of 19.896 seconds and 4.501
seconds. Other short guarded operations completed in under five seconds each.
The 17-script package smoke completed under the 900-second guard; the wrapper
did not retain per-process CPU/RSS telemetry for that run.
Guard admission snapshots reported host availability between 15.9 and 16.2
GiB and cgroup headroom from 1.00 to 2.50 GiB. Per-process CPU time and peak
RSS were not collected by the available wrapper, so those measurements are
**unavailable**, not zero.

The export/check reports are generated after package capture. The receipts
listed above therefore bind the frozen archive from outside the archive;
they do not alter it or its proof-input identity.
