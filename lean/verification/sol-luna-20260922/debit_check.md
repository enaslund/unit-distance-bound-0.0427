# Exact-rational check of the local-floor slope debit

The companion [`debit_floor_check.py`](debit_floor_check.py) reconstructs the
prime floors in `analytic.tex` from the literal twelve masks for the full
central quotient in `retained-field.tex`, evaluates the displayed formula for
`R`, and evaluates both the tight printed slope/debit and a relaxed-threshold
version using the Lean-proved bound `gamma >= 5767/10000`.

## Finite reconstruction and rational method

For each odd prime through 10,000 outside the ramified set, the script forms
the seven-bit vector

\[
 f_p=\sum_i \frac{1-(a_i/p)}2 e_i,
 \qquad (a_i)=(-1,2,3,5,7,11,13),
\]

using exact modular Legendre-symbol tests. It evaluates the manuscript's
12 quadratic masks in its stated 28-coordinate convention (seven diagonal
coordinates followed by the lexicographic cross terms), then applies the
explicit exceptional floors at 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, and 31.
The computed vectors at 17, 19, 23, 29, and 31 are respectively
60, 71, 57, 38, and 101, agreeing with the manuscript's displayed local
vectors. The reconstruction gives 1,229 prime rows, and all rows match the
separate `finite-ceiling.json` receipt exactly. The script hashes the two
manuscript source files and checks that its hard-coded full masks equal the
literal `\mathcal B` table.

Every logarithm is bounded by the positive atanh expansion after exact binary
range reduction. The omitted tail is bounded by a rational geometric tail.
Each prime contribution and the integer tail are rounded upward to a multiple
of \(10^{-70}\), preserving a rational upper bound while keeping the output
compact. The lower bound on \(\log(4\pi)\) uses a rational lower enclosure
for \(\pi\) from Machin's identity and alternating-series bounds. The script
obtains

\[
R < 0.009517185284096792159453308167815584834733359132442\ldots.
\]

This is the same finite-prime floor model and numerical `R` enclosure as the
existing external receipt; the exact output rationals are in
[`debit_check.json`](debit_check.json).

## Two gamma inputs and what they establish

For the tight manuscript display, the script conditionally supplies the
explicit rational input

\[
\gamma_E \ge 0.57721566490153286060651209008240243104215933593992.
\]

With this input, the exact-rational logarithm calculation gives

\[
L < 0.824453118933538946712643997040378956971732510362494\ldots,
\]

and

\[
\frac{L}{12000}
<0.000068704426577794912226053666420031579748\ldots.
\]

Both are strictly below the printed caps
`0.824453118933538946712643997041` and `0.00006870442657779491222606`.
This tight comparison is conditional on that 50-decimal gamma lower bound;
the Python replay does not prove the gamma enclosure. The separate existing
Arb-based finite-ceiling receipt is evidence for the same tight calculation,
but it is not a Lean theorem.

For the selected H ceiling, the script also uses the Lean theorem
`UnitDistance.eulerMascheroniConstant_lower_5767` from
`EulerMascheroniLowerCertificate.lean`, namely
\(\gamma_E\ge5767/10000\). It yields the weaker but independently
Lean-supported estimate

\[
L < 0.824582035158922161864272019561\ldots,
\qquad
\frac L{12000}<0.000068715169596576846822022668297\ldots.
\]

Using the other four manuscript allowances as rational inputs, this gives

\[
Y+B_D-S_4-S_{\rm cen}+L/12000
<0.042161829682499731260353101263\ldots
<0.042165819.
\]

The exact positive slack to `0.042165819` is recorded in the JSON receipt.
This check removes the 50-digit gamma input from the *relaxed selected-ceiling
comparison*. It does not freshly prove the other four allowances.

## Scope and trust boundary

This is an independent exact-rational finite reconstruction, not a Lean proof.
The script verifies the manuscript masks, finite prime rows, rational series
arithmetic, and final comparisons. It does not prove the field-theoretic claim
that each manuscript floor is bounded above by the corresponding actual
local degree; that identification remains in the manuscript's finite-field
argument and the existing separate reviews. It also does not recompute
`Y`, `B_D`, `S_4`, or `S_cen`.

The `union_forms_hex` masks in the H7 census artifact are expressed in the
new tower's raw-word/form coordinates; they are not the 28-coordinate
quadratic masks printed for \(M\), so their hexadecimal strings should not be
compared directly. This check instead computes the manuscript-basis floors
and compares the entire resulting prime table with the independent preserved
finite-ceiling receipt. Matching that receipt is a cross-check, not a proof of
the actual-field local-degree premise.

The replay is package-portable: it treats the parent of `verification/` as
`PROJECT`, looks for research TeX under `PROJECT.parent/publication/...` first,
then falls back to `PROJECT/docs/manuscript/sections/`. The reference receipt
is read from `PROJECT/verification/external-zeta-20260921/finite-ceiling.json`.
The script pins SHA-256 hashes for both TeX inputs and the reference receipt,
following the source-pinning pattern in `field_bridge_audit.py`; a package
replay checks that its copied source inputs are byte-identical to the reviewed
versions before doing the numerical work.

The replay refuses Python `-O` and hard-fails unless the finite receipt has
floor rows, the reconstructed rows match, the tight slope and debit are below
their printed caps, and the coarse-gamma allowance sum is below the selected
H ceiling. Thus a zero exit certifies those recorded rational comparisons
under the stated numerical inputs.

The final guarded portability replay exited 0, admitted at 14.3 GiB, and
reconfirmed all three pinned hashes and all 1,229 floor rows. The first
portability attempt exited 1 immediately after admission at 13.1 GiB: the new
hash assertion passed a `Path` object to `hashlib.sha256` instead of its file
bytes. That call was corrected before the successful rerun. The extracted
candidate package's `docs/manuscript` fallback is to be exercised separately
against that candidate.

After the certificate checks were strengthened to hard-fail on missing or
mismatched receipt rows and on any of the three displayed numerical
comparisons, the guarded replay exited 0 at 12.3 GiB. The mandatory floor
comparison, both tight printed caps, and the Lean-gamma relaxed H ceiling all
passed. This is the final hard-failure version; its zero exit certifies those
comparisons rather than merely reporting their boolean values.
