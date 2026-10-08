# Review record: 41-cap swap (2026-10-03)

## Independent fresh-context review of the swap argument

A fresh-context referee (no access to author confidence or prior verdicts)
was given claims A-D (local types, splitting, counting, GS cost) with
definitions and asked to report gaps. Finite computations were taken as
given; the review checked logic and factors of 2.

**Verdict: no arithmetic miscount and no fatal gap.** The counts d/8,
41^4, logF/8, (log 41)/2, and effective (2,4) are consistent. Findings were
unstated hypotheses, all addressed in `construction-41cap.md`:

1. "Exactly 4" needs K retaining D3 plus the new relation not killing g^2
   mod D3 (follows from the D4 depth fact plus D4-retaining layers).
   Fixed: section 3 now states (g-1)^4=g^4-1 in characteristic 2, G/D3
   unchanged, and D4-retaining layers from 241 section 3.6.
2. Absolute (1,4) needs Claim B plus e=1 (dependency ordering). Fixed:
   section 3 derives K/B f=4 first, then splitting, then absolute types.
3. "Unbounded degree" for the uncapped prime does not follow from S(v)
   outside R2 (only f>=4). Fixed: the note no longer claims unboundedness;
   uncapped primes carry no windows because f is not uniformly 4, and only
   f_min=4 (for the census) is used.
4. "Every prime splits" needs conjugacy invariance across decomposition
   groups above the capped prime. Fixed: one sentence added (K/B Galois,
   V abelian so same vector, Phi normal so squares stay).
5. d/8 integrality needs 8|d. Fixed: noted that d runs over large 2-powers
   retaining D4 (241 section 6.2 / Q-manuscript central-subgroup argument).
6. Effective (2,4) vs true (1,4) must stay distinguished. Fixed: explicit
   counting-device language with true type (1,4), e=1.
7. Claim D needs the D4 characteristic property stated. Fixed in section 3
   and assumption 1.

## Scope and remaining review needs

The review covered the swap logic (A-D) only. It did not re-audit the 241
tower presentation, the per-prime-of-B analytic transfer, the AFE modules,
or the interval routines (all inherited). A full independent review of the
41-cap certificate (PARI outputs, census code path for half-selected 41,
shell/arch witness sanity) has not been done. The finite replay
(`reproduce41.py`) passes.
