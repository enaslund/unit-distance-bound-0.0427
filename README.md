# Planar unit distances: exponent 1.04273

Lower bounds for the number of unit-distance pairs among points in the
Euclidean plane, by Eric Naslund. Each result constructs finite sets `U_j`
with `|U_j| → ∞` and `u(U_j)/|U_j|^(1+δ) → ∞`, where `u` counts unordered pairs
at distance one; equivalently, `u(n) ≥ n^(1+δ)` for arbitrarily large `n`. No
bound is asserted for every sufficiently large `n`.

| Result | Source | Status |
| --- | --- | --- |
| **Exponent 1.04273** (main result) | [papers/0.04273](papers/0.04273/README.md) | September 29, 2026: the tower of the 1.0418235 construction built over the real quadratic field ℚ(√241). Research note with a computer-assisted certificate and a finite replay; three independent AI referee reviews reported no mathematical error within their scopes. Not yet a self-contained manuscript. |
| Exponent 1.0418235 | [PDF](papers/0.0418235/main.pdf) · [sources and certificate](papers/0.0418235/README.md) | Manuscript with a computer-assisted certificate. |
| Exponent 1.0358324 | [PDF](papers/0.0358324/main.pdf) · [sources](papers/0.0358324/README.md) | Historical manuscript, kept for the record. |

## Checks

```sh
python3 papers/0.0358324/certificates/verify_t38_certificate.py  # historical T38 certificate
python3 papers/0.0418235/certificates/reproduce.py --check        # identity of the sealed package
python3 papers/0.0418235/certificates/reproduce.py                # finite replay (--analytic also re-evaluates the analytic factors)
cd papers/0.04273/certificates && python3 reproduce241.py         # finite replay at delta = 0.04273
```

The 0.04273 replay reuses certified modules from the 0.0418235 data archive;
it needs PARI/GP and the Python packages in
[papers/0.04273/requirements.txt](papers/0.04273/requirements.txt).

## Formalization

A Lean formalization of the main result, conditional on one explicit
numerical inequality, is described in
[docs/FORMALIZATION_STATUS.md](docs/FORMALIZATION_STATUS.md).

## Authorship and provenance

The papers and the research note were written with AI tools under Eric
Naslund's direction; each carries its own disclosure. The
[provenance manifest](provenance/papers.json) records the source and hash of
every copied file.
