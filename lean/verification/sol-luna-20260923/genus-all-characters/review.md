# Static review of `genus_full_direct.py`

## Assessment

I found no mathematical error in the signed fundamental-discriminant formula, the handwritten positive-denominator Kronecker/Jacobi routine, or the CRT construction of the Conrey label. The full-period check is a strong check of the computed label: for each mask it compares every residue class modulo `|D|`, including nonunits, against `(D/n)`. The direct interval comparisons are outward and oriented correctly. No numeric run was performed for this review.

## Character construction

- The seven radicands `(-1,2,3,5,7,11,13)` are distinct signed squarefree integers. Their product for a mask is signed squarefree, and a quadratic fundamental discriminant is `D=d` for `d ≡ 1 (mod 4)`, otherwise `D=4d`. Python's modulo convention for negative integers gives the intended congruence classes.
- `jacobi` implements the standard factor-of-two sign and quadratic reciprocity steps for a positive odd denominator. The final `odd_n == 1` branch handles denominator 1; a nontrivial common factor returns zero. `kronecker_positive_denominator` handles `n=1`, all powers of 2 for odd `D`, and returns zero whenever even `D` divides the denominator by 2.
- For odd `q`, the label `q−1` gives the product of quadratic characters at its odd prime factors. For `q=4m`, `q−1` has the odd quadratic labels and the nontrivial modulo-4 component. For `q=8m`, the label is assembled with residues `-1 mod m` and the selected quadratic label mod 8; the multiplier formula is the CRT solution. The choice between labels 5 and 3 tracks `D/8 mod 4`, including negative `D`.
- The checks `conductor()==q`, `is_real()`, and `order()<=2`, followed by equality over the full period, catch a wrong local label or CRT assembly. The inherited row comparison additionally checks mask, signed `D`, and label against the archived row.

## Interval and deletion direction

`dirichlet_char.l` and the correction factors are evaluated as Arb balls at the rational point `12001/12000`. The correction is the product of `1−χ(p)p^(−σ)`, which removes the selected Euler factors from the primitive `L`-value; when `p | D`, `χ(p)=0` and the factor is correctly 1. At `σ>1`, every factor and the real quadratic primitive value are positive, so taking the real logarithm is valid.

`inside_archived_interval` requires the freshly computed ball to lie strictly between the archived lower and upper dyadic endpoints. Conversion of the exact dyadic endpoints to Arb balls is outward; the strict interval ordering only accepts a result whose full enclosure is inside the stored enclosure. At the aggregate, `total_log/128` is compared to the archived normalized upper endpoint, then `total_log` to the rounded rational linear allowance. Those directions match the intended upper-bound claims. The final conductor sum assertion is absent, but per-mask checks against every archived `D` already determine the same conductor list.

## Independence and binding

The numerical calculation does not read saved L-value endpoints: it constructs each character, checks its period independently with the handwritten Kronecker code, and evaluates the L-value and selected-prime correction afresh. The archived receipt is only used for mask/D/label correspondence and interval comparison. The character construction also differs from the inherited producer's explicit-generator construction.

The L-value computation itself is not an independent numerical implementation from the inherited producer. `genus_full_direct.py` calls `character.l(sigma_complex)`, while `h7-majorant.py` calls `acb(s).dirichlet_l(chi)`; both use the same FLINT Dirichlet-L backend. Therefore this is a fresh input/character reconstruction and endpoint replay against saved intervals, with an independently coded finite-period check, but the L-value algorithm is shared through FLINT. State this when describing the result; matching 128 stored intervals is not an independent validation of FLINT's analytic enclosure algorithm.

All five currently embedded hashes (four Lean files plus the inherited JSON) match the workspace. The Lean hashes bind the mask-radicand data, actual conductor transport, actual factorization, and primitive-character result. They do not by themselves prove that the external Conrey character is the Lean character; the period check proves the Conrey character is `χ_D`, and the Lean bridge must still supply the mathematical identification of its genus character with that same Kronecker character. The script correctly names the Lean-to-Conrey identity as outside its scope.

For stronger reproducibility/provenance, consider adding hashes for the inherited producer `publication/six-dimensional-lower-bound/research/h7-majorant.py` and the imported pure conductor source `lean-formalization/UnitDistance/GenusDirichletConductorsRun20260920.lean`, and record the FLINT version in the output. These are provenance improvements, not blockers to the arithmetic checks already present: the archived data itself is SHA-256 bound, and the direct computation does not import the producer.

## Scope

A successful full run would give strong finite numerical evidence for the 128 primitive character values, their seven-prime-deleted values, and the aggregate comparison. It would not prove FLINT's analytic algorithm, the Lean-to-Conrey identity, other analytic factor families, or (H).
