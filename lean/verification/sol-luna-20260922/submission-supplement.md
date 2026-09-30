# Supplemental checks for the conditional zeta submission

These are independent finite checks added after the existing local pinned
Palomar verifier pass on source archive 07. They are **not** part of the
selected Lean theorem's proof and do not discharge its fixed-field zeta
hypothesis (H). The prior pass and the proof-input identity of later
documentation revisions are recorded separately in the submission handoff.

## What the included records check

| Record | Checked scope | Principal remaining boundary |
| --- | --- | --- |
| `field_bridge_audit.py` / `.json` / `.md` | Compares the literal Challenge field and manuscript catalog to the sealed source hashes, verifies all 17 norm identities, 19 quadratic masks and ranks, and reconstructs the 45-prime order-four list from Legendre tests through `10^4`. The research-checkout execution also compared the Challenge and TeX bytes directly to archive 08. | Kummer and local-index interpretation of the forms is a separate mathematical claim. The standalone script uses pinned source hashes when archive 08 is absent. |
| `order_four_log_check.py` / `.json` / `.md` | Exact rational series lower bound for the 45-prime order-four saving: `S4 ≥ 0.0000372474118954427480744667051484`, above the published allowance. | Assumes the reconstructed list has the stated local Euler meaning. |
| `exceptional_euler_log_check.py` / `.json` / `.md` | Exact rational series upper bound for the seven restored Euler terms: `B_D ≤ 0.0417270231508987854209556`, below the published allowance. | Takes the seven actual local residue degrees as inputs. |
| `debit_floor_check.py`, `debit_check.json` / `.md` | Reconstructs all 1,229 displayed local floor rows through 10,000, with exact rational series upper bounds for `R`, the slope, and the debit. Using the Lean-proved coarse `γ ≥ 5767/10000`, its debit with the other four manuscript allowances remains below the selected H ceiling by more than `0.0000039893`. | Actual-field local-degree floors and the other four allowances are still external inputs. The tighter printed debit comparison separately assumes a 50-digit gamma lower bound. |
| `numerics_h7_prefix_check.py`, `numerics_h7_census_prefix.txt` | Re-enumerates all 4,980 genus-split primes below `10^7`, evaluates 17 forms each, and matches every count and floor reciprocal sum in 2,308 nonempty bins. | Does not enumerate primes from `10^7` to `10^12`. |
| `h7_census_suffix_check.py` / `.json`, `h7-census-suffix-review.md` | Independently regenerates all 2,303 complete bins inside `[10^7,10^8)`, both straddling bins, and one distant complete bin around `10^10`; all 2,306 compared rows match count, reciprocal-floor and class splits. | A finite sample of the stored `10^12` census; the rest of the suffix and infinite tail remain open. The research-tree full-table path and archive-11 extracted-package fallback both passed. |
| `central_bin_interval_check.py` / `.json` / `.md`, `numerics_h7_census_full.txt` | Independently checks 13,825 stored full-census bins and gives an exact rational central-saving interval strictly inside both manuscript endpoints. The 2,307 complete prefix rows match the independently regenerated prefix. | The remainder of the full prime census is stored input, not regenerated. |
| `numerics_hecke_coeff_check.py`, compact fixtures | Regenerates the complete 981-coefficient mixed quadratic row and the first 128 coefficients in one pure quartic, one mixed quartic and one mixed octic row. It matches the complete-vector hash or displayed prefixes; the research run compared every copied field with six pinned full source tables. | The remaining rows, higher coefficients in the three prefix rows, moment integrations and analytic tails are unchecked here. |
| `hecke_all_rows_prefix_check.py` / compact fixture / reports / `hecke-all-rows-prefix-source-review.md` | Independently recomputes the first 128 coefficients in all 222 H7 quartic and octic analytic rows: 28,416 exact entry comparisons, including 38 quartic-phase rows. Fixture generation hash-checks 3 arithmetic and 64 moment tables plus four Euler receipts; ordinary replay validates the pinned compact fixture. Another agent reviewed the recurrence and row census at source level. | Finite prefixes only; no analytic moment integration, tail bound, global Hecke/Artin identification, or full 836-factor allowance. |
| `quartic_field_trace_check.py` / `.json` / `.md`; `quartic-field-review.md` | Derives the quartic polynomial `X⁴ + 34X² + 429` from the mixed quadratic radicand and twist, then matches its root-count trace against the selected row at all 159 unramified primes through 981 and all five eligible prime-square coefficients. A separate agent checked the field-side argument at source level. | Finite good-prime and prime-square check only; no global Artin identity or moment bound. |
| `quartic_field_composites_check.py` / `.json` / `.md`; `quartic-composites-review.md` | Reconstructs all 186 `n≤981` coefficients supported away from the six ramified primes from those root-count traces and Euler multiplicativity; the complete pinned row hash matches. The nonsquare norm 429 witnesses quartic irreducibility. | The representation-to-analytic-row identification, ramified factors, global Artin product and AFE remain open. |
| `genus13_lvalue_interval.py` / fixture / `.md` / `genus13_lvalue_interval-review.md` | Exact rational period-series enclosure `0.662607499048622 < L(χ₁₃,12001/12000) < 0.662915167689497` for the actual primitive conductor-13 character, using a bounded period tail. A separate agent reviewed coefficient signs, indexing, directed enclosures and the tail. | No pinned per-row allowance comparison, Lean proof of this interval, completion integral or genus aggregate. |
| `genus13_short_upper_certificate.py` / `.json` / `.md` / source review | A second, shorter exact-rational route uses 52 terms, the period-tail bound `<2/53`, and a separate rational selected-prime correction bound to show the deleted conductor-13 value is strictly below 1. Its exact upper is `4689291963776399684905241675231/4745938638374004765750000000000`, with exact margin below 1 `56646674597605080844758324769/4745938638374004765750000000000`. A separate agent reviewed the inequality directions, period tail, correction positivity and sign split and found no substantive flaw. The checker pins the character-defining Lean source hashes when present; package-only mode reports the embedded hashes and period because those research sources are absent. | No pinned manuscript row allowance, Lean interval theorem, completion integral or genus aggregate. This is a strict `<1` check only. |
| `genus13_common_level_interval.py` / `.md` / review | Applies exact rational directed Euler corrections at the seven selected primes to the preceding primitive interval, enclosing the deleted/common-level conductor-13 value in `[0.932999359249997,0.933432578984470]` and its log modulus in `[-0.069350764898162,-0.068886542513859]`. The value identification reuses checked Lean Euler/common-level equalities; the numerical bounds are external. | No fixed manuscript factor slot, per-row allowance comparison, Lean interval or 128-row aggregate bound. |
| `numerics_afe_one_factor.py` / fixture / report; `afe-one-factor-review.md` | Uses Arb's direct exponential-integral kernels and an elementary divisor-function tail to give an independent upper bound for the same mixed quadratic factor at `12001/12000`, below its pinned printed allowance. A separate agent reviewed the formulas and interval direction. | One row only; the functional equation, row identity, conductor, root-number phase, bad Euler factors and global coefficient bound are mathematical inputs. This does not validate the remaining factor table. |
| `numerics_check.py` | Exact rational reassembly of five replay allowances, degree/count weights, dyadic endpoint and ceiling slack. | It reads reported group endpoints; it does not recalculate analytic factor bounds. |
| `geometry_margin_audit.py` / `.json` / `.md` | Exact rational recombination of pinned Lean endpoint constants leaves a positive margin after the relaxed H ceiling. | The underlying Lean endpoint theorems are inherited, not reproved by this script. |
| `fresh-proof-review.md` | Independent source-level review of exponent, unordered-pair normalization, signs and Artin weights, with vulnerable external links named. | It is not kernel checking or human refereeing. |

Except for the direct one-factor AFE check, the numerical scripts use the
Python standard library. The AFE check needs `python-flint` for Arb ball
arithmetic (local run: `python-flint 0.9.0`, FLINT `3.6.0`). Run a checker
from the package root with
`python3 verification/sol-luna-20260922/<script>.py` in an environment
with its dependencies installed.
The required small inputs are included beside the scripts; the replay JSON
is under `verification/external-zeta-20260922/` and the debit script's earlier
finite-floor receipt is under `verification/external-zeta-20260921/`. The original 16 MiB full
Hecke moment table is not included. A guarded simulated-package run passed
the three standard-library `numerics*` checkers, and a separate guarded
run passed the direct AFE checker in both full-source and compact-package
modes with the local python-flint installation. The suffix-bin, genus-13,
quartic-composite, full-bin, order-four, exceptional Euler, field-bridge,
debit, quartic-trace and geometry scripts passed in the research checkout.
All fourteen scripts included in source archive 11 passed in its extraction
under one guarded smoke run; this exercised the suffix checker's bundled-table
fallback. Candidate 13 then passed all 16 scripts in its guarded extraction
smoke, including the common-level interval and all-row coefficient checkers.
Candidate 14 adds the short exact-rational conductor-13 checker to the
research smoke list, for a 17-script smoke when that candidate is assembled.
These checks do not build Lean or replay the pinned verifier.
The
guarded build helper and the local theorem/axiom audits are research-run
records, not scripts this source package needs to execute.

These checks increase confidence in the finite source bridge and several
printed numerical allowances. They do not independently establish the
global Artin/Hecke factor identifications, regenerate the entire census suffix or
all sector moments, or prove (H) in Lean. No unconditional `1.0418235`
theorem is claimed by this package.
