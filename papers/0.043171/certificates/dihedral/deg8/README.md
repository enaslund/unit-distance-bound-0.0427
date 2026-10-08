# L-values for the field E_W' (third D4 form)

These programs compute certified values L(sigma) for the L-functions of E_W' that
are not already in `hp/`, at the abscissae sigma = 1 + 1/n of `hp3/sigma_set3.txt`:

* the 64 + 64 dihedral twists of orbits 19 and 20 (degree 4);
* the 2 x 16 functions L(s, rho_19 (x) rho_o (x) lambda_w), o = 23, 24 (degree 8).

The results go to `../hp3/` (one JSON file per family and abscissa, with rows as
`dafe.py` writes them).

## Pipeline

1. **Exports (PARI/GP).**
   * `exportg.gp` is `export.gp` without the gamma-factor assertion. It records r1(K_w) and r1(Bc), so the gamma
     factor of zeta(K_w)/zeta(Bc) is known, and Euler factors up to `PSMALL` (3000).
   * `export8.gp` builds F_L = B(sqrt c_19, sqrt c_o) and F'_w = F_L(sqrt(gamma_19 gamma_o alpha^w)). It writes the
     conductor |d(F')|/|d(F_L)| and the Euler factors at every p <= 2^18. It asserts:
     * that F_L and F'_w are totally complex, giving gamma factor Gamma_C(s)^4;
     * that the discriminants are {2, 3, 5, 241}-units, which certifies the maximal orders computed from that
       partial factorization (`polredbest` models).
2. **Coefficients and moments (C).**
   * `dcoef4.c` (degree 4) uses the rule of `dcoeffs.py` for p > PSMALL.
   * `octcoef.c` (degree 8) uses the trace rule: a_P = 4 eps_19 eps_o lambda_w(P) if Frob_P is central in both D4
     quotients, else 0. It enumerates the n <= N with a_n != 0: PSMALL-smooth n depth-first, and n = m q with a
     segmented sieve over the primes q > PSMALL.
   * Both programs compare their rule with the PARI Euler factors at every unramified prime 1000 < p <= PSMALL,
     for all twists, before they start.
   * They write, per twist and per kernel cell i, the moments M_ij = sum_{n in cell i} a_n u_n^j (Kahan sums),
     A_i = sum |a_n|, and the Rankin sums used for the tail.
3. **Kernels (Arb).**
   * `gkernel.py` gives certified Taylor polynomials, with remainder bounds, of
     K_{s/d} + K_{(1-s)/d}, where K_b(x) = x^-b int_x^oo v^(b-1) H(v) dv and H is the Mellin inverse of
     prod_j Gamma(u + a_j).
   * It covers four types: 'octic' Gamma_C(s)^4; 'quartic' Gamma_C(s)^2; 'mixed31' Gamma_R(s)^3 Gamma_R(s+1);
     'mixed13' Gamma_R(s) Gamma_R(s+1)^3.
   * The docstring gives the AFE identity, the residue series with its tail bound, the remainder from complete
     monotonicity, and the Dirichlet tail bound.
4. **Evaluation.**
   * `leval.py` turns moments and kernels into L(sigma) balls. It accounts for the floating-point errors of the
     moments and adds the Rankin tail. For degree 8 the tail uses the Euler product of |a_n| (PARI factors, plus
     the octcoef sums, plus explicit bounds beyond N).
   * Inputs are prepared by `dprep4.py` and `octprep.py`.

## Checks

| check | result |
| --- | --- |
| `gkernel.py` against PARI `lfun`, products of 4 or 8 quadratic Dirichlet L-functions, one per gamma type, at s = 801/800 | agreement within the certified radii: quartic 4.6e-15, mixed31 5e-16, mixed13 3e-14 |
| `dcoef4.c` moments against `dcoeffs.py` coefficients, orbit 19, n <= 999999, 5 twists | counts and sums of \|a_n\| exact; moments within 2.2e-16 of A w^j |
| `octcoef.c` moments against an independent Python implementation (PARI factors to 3000 and the trace rule beyond), n <= 2e6 | exact counts; moments within 3.6e-16 of A w^j |
| orbit 19 via `dafe.py` (the reviewed pipeline, `nonpositive-afe.py` kernels, M = 999999) against `leval.py`, sigma = 801/800 | all 64 balls overlap; where dafe is accurate (48 twists) midpoints agree to 3.7e-16 |
| `octcoef.c` trace rule against PARI, all 16 twists, every unramified prime in (1000, 2^18] (family 23) | 22,832 primes, 1395 central sides, 21 primes with both sides central |
| `octtest.py`: the degree-8 AFE value at s = 19/10 against the absolutely convergent Euler product | detects a wrong conductor, gamma factor, root number or coefficient rule |
