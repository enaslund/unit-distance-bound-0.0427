# Fresh review: quartic field trace check

## Mathematical argument

The selected fixture row is mask 1586, dimension two, twist \(-1\), with
base field \(F=\mathbb Q(\sqrt{-35})\) and
\(\eta=17+2\sqrt{-35}\). Put \(u^2=-\eta\). Since

\[
N_{F/\mathbb Q}(-\eta)=17^2+35\cdot 2^2=429
\]

is not a square in \(\mathbb Q\), \(-\eta\) is not a square in \(F\), so
\([F(u):F]=2\). Also \(\sqrt{-35}=-(u^2+17)/2\in\mathbb Q(u)\), hence
\([\mathbb Q(u):\mathbb Q]=4\). Eliminating \(\sqrt{-35}\) gives

\[
X^4+34X^2+429.
\]

For a monic depressed quartic \(X^4+bX^2+c\), the polynomial discriminant
is \(16c(b^2-4c)^2\). Here it is

\[
16\cdot429\cdot560^2
=2^{12}\cdot3\cdot5^2\cdot7^2\cdot11\cdot13
=2{,}152{,}550{,}400.
\]

Thus every rational prime outside \(\{2,3,5,7,11,13\}\) is unramified
for both fields, and does not divide the index of the displayed quartic
order. Dedekind factorization identifies roots modulo \(p\) with degree-one
prime counts. If \(p\) splits in \(F\), the quartic root count minus the
quadratic root count is the sum of the two relative quadratic-character
values at primes above \(p\). If \(p\) is inert in \(F\), both root counts
are zero and the induced character has trace zero. Therefore the stated
difference equals the trace of
\(\operatorname{Ind}_{G_F}^{G_{\mathbb Q}}\chi_{F(u)/F}\) at every such
prime. The sign of the twist is incorporated in \(u^2=-\eta\), consistent
with the row's twist \(-1\).

## Source and code review

The compact family fixture binds mask 1586, \(N=981\), the radicands and
coefficients, twist, local-factor data, and the complete signed coefficient
vector hash. The two referenced full research files are present in this
checkout; their SHA-256 values match the fixture's hashes. The checker
compares every fixture row/sector key against the hash-bound full tables.
Its finite loop sieves all primes through 981, excludes exactly the six
discriminant divisors, directly counts roots of the two displayed
polynomials, and compares each difference with the regenerated \(a_p\).
Prime 17 is correctly included: it is unramified for this quartic even
though its Hecke row has an explicit local factor.

No mathematical or root-loop defect was identified. This is finite evidence
for one row at unramified primes through 981. It does not prove the global
Artin/Hecke identification, check ramified factors against local Artin
invariants, or verify the AFE/moment bounds.

The initial version imported `numerics_hecke_coeff_check.py` without pinning
the helper's own SHA-256. The current source adds a direct hash assertion and
records the helper hash in its output. I checked that the asserted hash,
`3759f993a31a0df05241d8faa546950dcf68b49ad4768339e4f56da4e7846329`, matches
the current helper file. This resolves the source-binding caveat at source

## Prime-square extension

I reviewed the later \(p^2\) check in `quartic_field_trace_check.py` at
source level. For each eligible prime \(p\in\{17,19,23,29,31\}\), it picks
a quadratic nonresidue \(d\) and represents \(\mathbb F_{p^2}\) as
\(\mathbb F_p[w]/(w^2-d)\). The tuple multiplication reduces both
coordinates modulo \(p\); exhaustive enumeration of the \(p^2\) pairs
counts roots of both defining polynomials. The difference is the trace of
Frobenius squared, since each root count is the fixed-point count of the
corresponding permutation representation under \(\mathrm{Frob}_p^2\).
For a two-dimensional representation,

\[
a_{p^2}=\operatorname{tr}(\mathrm{Frob}_p)^2-\det(\mathrm{Frob}_p)
=\frac{\operatorname{tr}(\mathrm{Frob}_p)^2+
\operatorname{tr}(\mathrm{Frob}_p^2)}2.
\]

The script checks parity before division and compares to the full
coefficient vector at index \(p^2-1\), which corresponds to \(a_{p^2}\).
I found no arithmetic or indexing flaw in these operations. This adds five
finite coefficient checks only; it does not extend the global or AFE scope
above. I reviewed the implementation and formula without rerunning the script.
