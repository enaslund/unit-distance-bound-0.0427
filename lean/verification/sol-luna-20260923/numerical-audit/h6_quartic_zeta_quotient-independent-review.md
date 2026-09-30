# Independent review: H6 quartic zeta quotient replay

## Scope and pinned result

I reviewed the checker, the plan, attempt 4's guarded output, and its saved
result JSON. I did not run PARI or regenerate any coefficients. The attempt 4
result reports `PASS finite coefficient equality`, 3,922 matching integer
coefficients, zero mismatches, and matching target/PARI vector SHA-256
`b9317cb66d83f606dbbeeecd2ad40f4e805afbfbda7bd04383b28b7e7f1e3489`. All
seven bad-prime cross-products report true. It records 543 prime
decompositions through 3922. The result JSON SHA-256 is
`5d568a5830300ce24b1bb1411bc35c146f0241d414ba0832bd7db8d1d0d64f41`.

The PASS JSON pins checker SHA
`7139eb656580755af33ece151acb072bdc76ef3d8af60e47b6118cfd22f39a5f`.
The current checker file is SHA
`1643a51379688ba6c1df0aee178f1759e16b8b4016e09c1394e648eabeee7905`; it has
since been changed to query GP with `--version-short`, so it is not the exact
source used for attempt 4. Attempt 4's GP version field contains the output of
`gp -v` (usage text), not a version number. Separately, `gp --version-short`
reports `2.17.2`, but this later observation does not retroactively bind that
version to attempt 4. The provenance-only attempt 5 was deferred before
running, so the existing PASS remains the preserved finite result, with this
version-field limitation.

## Mathematical and implementation checks

The local zeta quotient direction is correct. For a number field `F`, its
local zeta denominator is `D_F(T)=∏_{𝔭|p}(1−T^{f(𝔭/p)})`; hence
`ζ_K/ζ_B = D_B/D_K`. The checker passes `D_B` as numerator and `D_K` as
denominator to exact formal-series division. It uses residue degrees, as
required for the Dedekind zeta Euler factor; ramification indices are retained
in the recorded decomposition profile but do not enter that denominator.

The global coefficient assembly is multiplicative and handles prime powers
correctly: for each `n`, it extracts the least prime `p` and its full
exponent `v`, then multiplies the local coefficient of `p^v` by the already
computed coefficient at `n/p^v`, which is coprime to `p`. The formal quotient
recurrence has constant denominator coefficient 1 and computes each
coefficient using only preceding coefficients. The bad-prime comparison
checks `D_K=E_p D_B`; its degree-4 truncation suffices because `K` has degree
four and the target bad polynomials have degree at most two.

I independently checked that the JSON has exactly the 543 prime keys from 2
through 3922 (by trial division), matching `prime_pi(3922)`; a missing prime
would also prevent the checker from assembling the coefficient at that prime.
The GP source uses `forprime`, and both number-field structures pass
`nfcertify` before decompositions are printed. The field relation is
algebraically consistent: for a root `u` of `u^4−34u^2+429`, setting
`β=(u^2−17)/2` gives `β^2=−35` and `u^2=17+2β`. Thus, once the quartic is
viewed as irreducible, `B=Q(β)` is its quadratic subfield and the quotient is
the relative quadratic zeta quotient. The checker itself labels that field
identification as an assumption; it does not claim a separately formalized
field-isomorphism theorem.

The comparison target is reconstructed by a different implementation from
the PARI side: the pinned Hecke recurrence uses the quadratic residue-symbol
recipe at good primes and the pinned Euler polynomials at the seven bad
primes; the comparison side uses PARI maximal-order prime decompositions in
both fields and multiplies the local zeta quotient coefficients. The target
and input data are shared, and this finite agreement is not a proof that the
two Euler factors agree at every prime. The seven direct bad-factor checks
are useful independent local checks, but are still only at
`2,3,5,7,11,13,17`.

## Scope

The PASS is finite exact evidence for coefficients through 3922 and for the
seven explicit bad-prime denominator identities. It does not prove the
all-prime Artin/Hecke identity, conductor, root number, functional equation,
analytic continuation or growth hypotheses, an AFE, or the desired global
bound. No resource counters are reported here; this was a read-only source
and receipt audit.
