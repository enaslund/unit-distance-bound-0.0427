# Scope of Lean issue #15226

The current [Lean issue #15226](https://github.com/leanprover/lean4/issues/15226)
is open. It reports imported `Lean.collectAxioms` / `#print axioms` results that
omit dependencies reached through inductive constructors. The documented
mechanism is a traversal-in-progress sentinel being retained as a completed
per-declaration result in the exported axiom cache. Reported affected versions
include 4.35.0-rc2. The issue concerns an audit query, not a demonstrated kernel
proof-checking failure. The maintainer's
[September 25 comment](https://github.com/leanprover/lean4/issues/15226#issuecomment-5830759814)
discusses the inconsistency and distinguishes the newer Lake checking tools.
The raw issue and comments are retained with hashes in
[axiom-issue-and-cgroup-recheck.json](axiom-issue-and-cgroup-recheck.json).

The passed Palomar pipeline follows a different code path at the exact rc2
commit `11acb17ec6b07a8f9e9173e6845197929540936b`:

1. [LeanExport's entry point](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/LeanExport.lean)
   imports the modules using `importModules` defaults. Its default is
   [private import level with all module data available](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Lean/Environment.lean#L2423-L2449),
   rather than consulting the exported axiom-summary cache.
2. [The exporter](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/LeanExport/Basic.lean#L252-L426)
   traverses actual types and values. Its inductive branch includes mutual
   inductive members, constructor types and recursor dependencies, with a visited
   set. It does not call `Lean.collectAxioms` or `exportedAxiomsExt`.
3. [Comparator's `verifyMatch`](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/lake/Lake/CLI/Check.lean#L512-L527)
   parses the protected Challenge and Solution exports, compares the selected
   statements/definitions, calls its own `checkAxioms`, then runs the independent
   kernels and Lean's kernel.
4. [Lake.Check.checkAxioms](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/lake/Lake/Check/Axioms.lean)
   starts a fresh worklist from the selected targets and follows the parsed
   export's constant map. It rejects referenced axiom records outside the
   allowlist and errors on missing constants. Its
   [`runForUsedConsts`](https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/lake/Lake/Check/Util.lean)
   follows type expressions, bodies including opaque values, inductive
   constructors and mutual siblings, constructor parents, and recursor rules.

Therefore the protected-export allowlist check avoids the **specific cached
summary mechanism** in #15226. This is a source-level assessment of that defect,
not a blanket claim that the checker has no other bugs. No new reproducer or
proof run was performed for this note, and old receipts were not changed.

Standalone imported `#print axioms` or `Lean.collectAxioms` receipts should be
described as those queries' reported results, not treated as independent proof
of an exhaustive axiom set on rc2. The existing full Palomar pass has the stronger
separate export traversal and all three kernel acceptances. Updating to rc3 is
not a fix for this issue: the rc2-to-rc3 comparison changes neither the affected
collector nor the independent comparator/exporter paths. This issue provides no
reason to weaken, remove, or replace any of the full pipeline checks.
