# A 41-cap variation over Q(sqrt 241): exponent 1.042901 (research result)

This directory records a variation of the
[Q(sqrt 241) construction](../0.04273/README.md) (exponent
1.04273) found on 2026-10-03. It swaps the C4 cap at the inert prime 7 for a
C4 cap at one prime above the split prime 41. The cap count (3), the
Golod-Shafarevich value, the retained Lie layers, the genus field, and the
analytic ceiling are unchanged; the finite-places profit roughly doubles on
the swapped cap, lifting the certified exponent to **1.042901**. Its swap
argument has had two fresh-context reviews, which found no error that
invalidates the exponent: [research/review-41cap.md](research/review-41cap.md),
and a second one in §8 of the
[design-search note](../../research/2026-10-design-search/README.md), which
lists its remaining write-up items. The certificate has not had a full
independent review, and the result is not Lean-formalized.

The D4 refinements in [../0.043171](../0.043171/README.md) keep this
construction (tower, caps, local types) and lower its analytic constant,
which raises the exponent to 1.043171, the main result of this repository.

## Idea in one paragraph

A C4 cap costs the same Golod-Shafarevich budget c4(t) at any unramified
prime, but its geometric profit falls with the norm. The 241 design spends
one cap on the inert prime 7 (norm 49, absolute f=8, profit ~0.0035). The
prime 41 is the next split prime after 29; capping one of its two B-primes
costs the same c4 and yields absolute f=4 on half the F-primes above 41
(effective (e,f)=(2,4), profit ~0.0073). The swap keeps 3 caps, so
P_B(34/117)<0 still holds with the identical polynomial; fourth powers do
not enter the quadratic/cubic Lie layers, so L2/L3 and the retained quotient
are unchanged; and the analytic excess-plus-census total is termwise
identical (7 moves selected->census, one 41-prime moves census->selected,
same f=4 formulas), so C<=0.04871285 still holds with the same endpoint.
Fresh archimedean and shell profiles at the new delta certify margin
5.78e-6 at delta=0.042901.

## Contents

| Path | Contents |
| --- | --- |
| [research/construction-41cap.md](research/construction-41cap.md) | Statement, tower compatibility, analytic recomputation, geometric margin, transfer assumptions |
| [research/cap-search.md](research/cap-search.md) | Candidate search (why 41) and negligible refinements |
| [certificates/](certificates/) | Finite computations and the replay driver `reproduce41.py` |

## Key numbers

| Quantity | Value |
| --- | --- |
| rd(K) = rd(F) | sqrt(241)*2^{9/4}*sqrt(15) ~= 286.0 (unchanged) |
| Golod-Shafarevich | P_B(34/117) = -187433948535241/88772225460489675 (unchanged; 3 C4 caps) |
| retained quotient | order 2^49, L2=15, L3=26; class of c1 of size 2^15 (unchanged) |
| new cap | one B-prime above 41, Frob vector [0,0,1,1,1,0,0,0], S(frob) outside R2, c1 separated |
| analytic ceiling | C = 0.04871285 (recomputed; upper endpoint bit-identical) |
| certified margin | >= 5.779e-6 at delta = 0.042901 (>= 2.970e-5 at 0.04290) |

## Reproduce

```sh
cd certificates
python3 reproduce41.py        # needs PARI/GP, mpmath 1.3.0, python-flint 0.9.0
```

The replay hash-checks the shared 241 inputs (Kummer/Lie/CE data), replays
PARI Kummer vectors for 41, the cap-compatibility checks, the Lie/GS steps,
the recomputed ceiling, and the geometric margin. It reuses the 241
genus-field AFE value (caps do not enter E_B) and the certified profile,
shell-window, and degree-two AFE modules unchanged.
