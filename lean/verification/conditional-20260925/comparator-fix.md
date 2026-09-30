# Candidate 19: finite-dimensional instance comparison

Candidate 18 finished its fresh Lean 4.35 build and both proof exports on
September 24, then failed the structural comparator at
`UnitDistanceZetaSubmission.CanonicalRetained.finite`. The failed archive and
reports remain preserved under `verification/conditional-20260924/`.

The Challenge and Solution had identical source for this instance, but their
different imports selected different implicit `AddSubmonoidClass` arguments
in its type. The Challenge used `AddSubgroupClass.toAddSubmonoidClass`; the
Solution used `SubsemiringClass.toAddSubmonoidClass`. The difference appears
both in fully printed declarations and in the preserved exports. These
arguments prove the same proposition, so Lean regards them as definitionally
equal by proof irrelevance. The pinned comparator compares dependency
declarations structurally, which is a stronger requirement.

Both submission files now locally prioritize
`AddSubgroupClass.toAddSubmonoidClass` for this one declaration. The scope ends
with the declaration. The field generators, H, exponent, conclusion, proof
body, comparator configuration, and permitted axioms are unchanged. Removing
only the competing subsemiring instance was insufficient: another instance
path then became available in the Solution.

The two corrected wrappers compiled separately using the retained Lean
4.35 artifacts. The actual toolchain routine `Lake.Check.compareAt` then
accepted the theorem statement and its complete structural dependency
closure in the independently imported environments. The
[focused check receipt](focused-fix-check.json) binds the checked source to
the canonical files, up to an explanatory comment and diagnostic printing.
The diagnostic source is preserved in `diagnostics/`.

This focused check is not a fresh package build, an exported-proof check,
an axiom audit, or an independent kernel replay. Candidate 19 needs its own
full verifier result. The new export is not represented as the exact source
tree of the earlier pass-50 migration build. H remains unproved in Lean.
