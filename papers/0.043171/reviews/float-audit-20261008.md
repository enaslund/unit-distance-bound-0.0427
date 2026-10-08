> Fresh-context audit of the floating-point arithmetic in the L-value, kernel and receipt programs (October 8, 2026, research commit c6ec5e39), by an AI agent; read-only. It found no non-rigorous bound. Its hardening suggestions applied in d3b77917: the bound of Lemma ce:values stated with margin, Arb tails, and the fail-closed H_W receipt. Paths under /tmp are the auditor's scratch space.

# Floating-point rigor audit of the L-value and kernel certificates (papers/0.043171)

Date: 2026-10-08. Read-only audit: no repository file was edited. Scratch scripts and logs are in
`/tmp/claude-1000/-home-naslund-eric-src-enaslund-unit-distance-bound-master/cdb0bbeb-b1c7-4474-8201-6a29f162e43c/scratchpad/fa/`
(`decomp8.py`, `decomp4.py`, `stepsim.py`, `sens.py`, `rkshare.py` and their outputs). The audit covers the
committed code (HEAD `c6ec5e39`). The working tree also has uncommitted edits to `signed.py`, `lptv.py`,
`dihedral_ceiling.py` and `dihedral_ceiling3.py`, listed under items 23, 24 and 32.

## 1. Verdict

I found no non-rigorous floating-point bound in the chain that produces the enclosures used by
Proposition lv:values, Lemma ce:kernel, Lemma ce:values, Theorem an:ceiling and `h_w_receipt.py`.

* **Defect classes (1) and (2): present, but slack covers them.** Every bound computed in IEEE doubles,
  and every `float(x.upper())` conversion, is covered by an explicit slack that exceeds the possible
  rounding error by a factor of 10^2 to 10^9. Examples are `+1e-4` in a logarithm, `*1.0001`, `*(1+1e-6)`,
  `*(1+1e-9)`, `*(1+1e-12)`, `+1e-300`, or a mathematical overestimate of at least 16 times.
* **Class (3): not found in the certified path.** Comparisons use full Arb balls, or the exact rationals
  mid + rad parsed from a printed ball (`reproduce_w3.py:314-315`).
* **Class (4): not present.** The endpoint strings are Arb ball strings `"[m +/- r]"` (`leval.py:172`,
  `dafe.py:40`, `afe241.py` for `normalized_log_zeta_EB`). Each one contains the exact endpoint. Every
  consumer reads them back with `arb(...)` and takes the union (`dihedral_ceiling3.py:86,141`). I checked
  this directly: `arb(str(x.upper())).contains(x.upper())`.
* **Arb throughout.** The final quantities are formed in Arb: Y_W'' and Y_cor in `dihedral_ceiling3.main`,
  then the combination, `census_tau` and B_r in `signed.certify`, then `ce_values_digits.py`, then the
  receipt (Y via DC3 W4x, D_W and its tail in Arb).
* **Bit-identical reproduction.** With the committed code on this machine I recomputed bit-identically the
  stored `hp3` rows of:
  * degree-8 family (19,23), 16 twists, at sigma = 511/510 and 43692/43691;
  * degree-4 orbit 19, 64 twists, at the same two abscissae (`dcoef4.c` rebuilt with the replay flags).

  This confirms that the audited code is the code that produced the data.

**No repair is required for rigor.** The working-tree edits replace two float tails by Arb tails. Neither
changes a stored L-value enclosure, and neither changes any digit used in Lemma ce:values or Theorem
an:ceiling (Section 5).

**Fragility of the displayed constant.** The constant displayed in Lemma ce:values (slack 8.03e-15) is
extremely sensitive to the L-value radii, although nothing currently undercuts it. Section 5 quantifies
this and suggests a looser display.

## 2. How the enclosures reach the lemmas (all Arb)

1. **Degree 4 (orbits 19, 20, 17, 7) and degree 8 (8 families): `deg8/leval.py`.** The enclosure is
   `pref * (sum q_ij * M_ij + arb(0, (sum A_i R_i + tail).upper()))` (`gkernel.evaluate_moments`, l. 357-370).
   * The kernel coefficients q_ij and the remainders R_i are Arb balls (`gkernel.Kernel`).
   * The moments M_ij are Arb balls around the C doubles, with a radius from an explicit error model
     (`leval.moment_balls`).
   * The tail comes from Lemma lv:remainders(b) with Arb Gamma and zeta values. For degree 8, log E(beta)
     is computed in Arb (`logE_octic`) from:
     * PARI Euler factors;
     * the `octcoef.c` double sums rk, times (1+1e-6);
     * the bound 36.01/p_0;
     * the Rosser–Schoenfeld term.
2. **Orbits 10, 23, 24: `dafe.py`.** The value is `A.real + B.real + arb(0, 2*err.upper())`, from the
   archive's `nonpositive-afe.py`. That code uses exact integer moments and Arb; floats appear only in
   `min(..., key=float(mid))` for the choice of beta.
3. **Y_E: `ye_hp.py` -> `afe241.py` (0.04273) -> archive, in Arb.** The value is stored as ball strings.
   The pre-repair per-row JSON floats `"L"`, `"zeta_B"`, `"L_chi241"` in `hp/afe241hp_*.json` are rounded
   to nearest, not outward. **No 0.043171 program reads them** (grep: only `normalized_log_zeta_EB` is
   consumed).
4. **`dihedral_ceiling3.main` (space W4 in `witness_0.043171.json`).** It reads the balls, then computes
   `sum4 += L.log()`, `sum8 += L.log()`, `Y_W = Y_E/16 + 2*sum4/8192 + 4*sum8/8192`, and Delta_sel,
   Delta_P4 and census_small, all in Arb.
5. **`signed3.py` / `signed.certify`.** It computes `total = sum c_j * E_j` in Arb, with balls passed
   between processes exactly as (mantissa, exponent). Then `census_tau` (Arb, mean value theorem), `B_r`
   (Arb) and `C = zsel(1) + combo + b*B_r`. The replay checks `Q(mid)+Q(rad) <= Q(C_eff)` on the printed
   ball.
6. **`h_w_receipt.py`.** Y comes from DC3 W4x (all L-values from leval). D_W is an Arb sum with the Arb
   tail `(1+2/X^2)(log X+1)/X`.

## 3. Findings

Class (a): only a heuristic parameter, whose effect is covered by a separate rigorous bound. Class (b):
part of a bound that enters an enclosure. Line numbers refer to HEAD.

### 3.1 Kernels: `deg8/gkernel.py`

1. **`gkernel.py:76-84`.** `_prec_for` and `_n0` choose the working precision and the residue truncation
   index. **Class (a), rigorous.** The truncated tail is bounded separately, and the ratio r <= 1/2 is
   asserted. **Impact:** none.
2. **`gkernel.py:112-132`.** `_cauchy_logbound` computes the log of the Cauchy bound for the residue
   coefficients with `math.gamma`, `log`, `lgamma` and `cos` in doubles. **Class (b), rigorous.** The
   function adds `+1e-4` to the log. The float error in the log is at most about 1e-12 (|log| <= about
   2000). I checked the mathematics independently (Section 4.1). **Impact:** all kernel-coefficient radii,
   these residue tails included, contribute <= 1e-43 (degree 8) or <= 5e-23 (degree 4) relative to L
   (`rel_arb_mid`, Section 5). An error even of factor 2 would be invisible.
3. **`gkernel.py:135-155`.** `_tail_bound` sums the geometric tail in doubles (`exp`, ratio), multiplies by
   `*1.0001`, and floors the result at 1e-300. **Class (b), rigorous.** The slack is 1e-4 relative against a
   float error of about 1e-13. An underflowed bound (l0 < -708) is at most 4.4e-308 and is dominated by the
   1e-300 floor. **Impact:** same as item 2.
4. **`gkernel.py:187-191`.** The falling-factorial `extra` is computed in doubles
   (`k! * xf^k`, xf^21 >= 2^-861). **Class (b), rigorous** (inside the 1e-4 slack). **Impact:** same.
5. **`gkernel.py:231`.** `tb = _tail_bound(...) * xf ** float(b)`, where b = s/d or (1-s)/d is rounded to a
   double. **Class (b), rigorous.** The relative error is <= |log x||b - fl(b)| + 2u <= 1e-14, inside the
   slack of `_tail_bound`. **Impact:** same.
6. **`gkernel.py:288, 370`.** `arb(R.upper())` and `arb(0, (err+tail).upper())`. These are Arb operations:
   `upper()` rounds outward at the current precision (tested). **Rigorous.**
7. **`gkernel.py:315`.** The guard `float(v.lower()) <= 0` checks b + mu_j + c > 0. **Class (a) guard,
   rigorous:** rounding preserves sign, and the values are >= 0.98.
8. **`gkernel.py:321`.** `max(sig, key=float(upper))` chooses sigma_max in A_c. **Class (b) selection,
   rigorous here.** The candidates are equal or differ by exactly 1/2, so the float order is exact. It is
   fragile only in principle.
9. **`gkernel.py:323`.** The rejection test `ex <= bA` is an Arb comparison. **Rigorous for every used
   (sigma, beta):** ex - beta = d*c - 1/n or more is never 0. An Arb ball straddling beta would fail open, so
   writing `not (ex > bA)` is a cosmetic hardening.

### 3.2 Moments and Rankin sums: `leval.py`, `dcoef4.c`, `octcoef.c`

10. **`leval.py:72-80`.** `eps_t = float(upper) * (1+1e-6) + 1e-300`. **Class (b), rigorous**
    (1e-6 >> half an ulp). **Impact:** eps_t is about 2e-16, so the error in du is <= 2e-32.
11. **`leval.py:86`.** `w = float(1 - c_{i+1}/c_i) * (1+1e-12)`. **Class (b), rigorous.**
12. **`leval.py:89-93`.** The moment radius is computed in doubles, times `(1+1e-9)`. **Class (b),
    rigorous**; the float error is <= about 30 ulp. **Impact:** the moment floating-point part of the
    radius is:
    * degree 8: <= 1.8e-13 relative to L, <= 4.4e-4 of the radius;
    * degree 4: <= 4.3e-14 relative to L, about 20% of the radius.
13. **`dcoef4.c:216-224` and `octcoef.c:276-287, 430-434`.** The moments M_ij are computed in doubles with
    Kahan summation and per-thread accumulators. **Class (b), rigorous.** The leval model matches the code:
    * x = fl(t_d n), and fl(x^2) for d = 2;
    * fl(x/c_i), then the subtraction of 1, which is exact by Sterbenz;
    * j roundings per term;
    * Kahan error 2u + O(n u^2);
    * merges: a0 plus nth threads need (2*nth+1)u, against the (2*nth+4)u allowed.

    About 6u of the allowance is unused. Requirements: IEEE double with no `-ffast-math`. The replay builds
    with `-O3 -march=native`; FMA contraction of `av*pw - C` only reduces the error.
14. **`leval.py:118`.** `rk * (1+1e-6)`, where rk are the `octcoef.c` naive double sums of |a_q| q^-beta.
    There are 1.33e8–2.58e8 nonzero terms over 6 threads. **Class (b), rigorous.**
    * The summation error is <= gamma_{4.3e7} + 6u, about 5e-9 relative; |a_q| is 4 or 8, so the product
      is exact.
    * `pow` errs by <= 1 ulp.
    * `fl(1.05)` and `fl(1.1)` exceed 21/20 and 11/10, an underestimate of <= 1e-15 relative.

    All of these are << 1e-6. **Impact:** the margin itself accounts for <= 9.6e-16 of the upper end in
    Lemma ce:values (Section 5). The float error it covers is <= about 5e-18 there.
15. **`leval.py:172` and `dafe.py:40`.** `str(L.lower())` and `str(L.upper())` produce ball strings,
    re-read with `arb()`. **Not a class (4) defect; rigorous.**
16. **`octcoef.c:48-54`** (`mulm`: float quotient estimate with exact integer correction) and
    **`octcoef.c:364`** (`sqrt` for the sieve limit, +2). **Class (a), exact.**
17. **`octcoef.c:400-401`** (`eul`), **`octtest.py`**, and **`dcoef4.c:228-229`** (rk for degree 4, unused
    there: zeta(beta)^4 is used instead). These are checks only and not in the proof. **Impact:** none.
18. **`deg8/octic.py`.** The float remainders `remG` and `remI` are covered by `*1.0001` and by a factor 2
    over a geometric ratio of 1/16. The module is **not imported by any program** and is not used for
    stored data. **Impact:** none.

### 3.3 Orbits 10, 23, 24 and Y_E: `dafe.py`, `dcoeffs.py`, archive, `afe241.py`

19. **`dafe.py:38`** forms A + B + 2 err in Arb. **`dafe.py:41`**: `float(err)` is informational only.
    **`dcoeffs.py`** uses exact integers. **Rigorous.**
20. **`afe241.py` (0.04273, via `ye_hp.py`).** Y_E is computed in Arb. The per-row floats were
    round-to-nearest before the repair, and the stored `hp/` files still have them. **Defect class (2)**,
    but not consumed. **Impact:** none. Cosmetic: regenerate, or note that they are informational.

### 3.4 Tails and checks in `signed.py`, `lptv.py`, `dihedral_ceiling*.py`, `h_w_receipt.py`, replay

21. **`signed.py:45` and `signed.py:131-140`, `293-374`; `signed3.py:43-63`.** `LH`, `census_float` and
    the LP. **Class (a):** the certification is independent of them.
22. **`signed.py:391-392`.** xmin is `float(lower)` truncated to 6 decimals, then asserted `<= log q_min` in
    Arb. **Class (a), rigorous.**
23. **`signed.py:71` (`w_arb`).** The tail is `arb(0, 2*float(term.upper()))`. **Class (2) defect type,
    but rigorous:** the true tail is <= term*(q^m+1)/(q^m(q-1)) <= term/8 for q >= 9, so the factor 2 gives
    16x slack. **Impact:** term < 1e-70, so the effect on B_r is < 1e-85. The working-tree edit is cosmetic.
24. **`lptv.py:50`** (same tail as item 23) and **`lptv.py:139-144`** (xmin from `math.log(qmin) - 1e-9`).
    **Rigorous:** the 1e-9 margin applies, and [2, 2 q_min] is also covered by `kernel_small_ok`. **Not
    used for 1.043171**, which uses Proposition E rather than D.
25. **`signed.py:188, 202`.** KTR = 10 and the radius 1e-55 form a mathematical truncation bound.
    **Rigorous.** Recomputed in Arb at x = log q_min = 14.854 with sum|c| = 3844: the remainders of S1, S2,
    S3 and their first three x-derivatives are <= 9.0e-59. With sum|c| = 1e6, the code's assertion, they are
    <= 2.3e-56. However, the docstring's "x >= 14 (y <= 4e-7)" is internally inconsistent:
    e^-14 = 8.3e-7, and at x = 14 with sum|c| = 1e6 the bound would be 1.3e-52. This is wording only, since
    xmin = 14.854288.
26. **`signed.py:251-274` (`check_kernel`).** The cells are Arb balls. **Rigorous.** A simulation of the
    stepping shows 1950 top-level cells; the last h is `xbig - x`, so the final x ball contains 2e6
    (radius 5.6e-51), and the cover [xmin, xbig] has no gap.
27. **`signed.py:277-289` (`check_tail`).** Arb throughout. **Rigorous:** I re-derived the inequalities
    (Section 4.4).
28. **`signed.py:143-184` (`census_tau`) with `census_kv4.c:320`.** The float bin index has an error of
    about 1e-10 bins, inside the slack of one bin on each side. **Rigorous.**
29. **`dihedral_ceiling3.py:205` and `dihedral_ceiling.py:122`.** The tail
    `arb((math.log(X)+1)/X)*(1+1e-6)` is a **class (1) defect type, but rigorous:** 1e-6 exceeds the float
    error (4e-16) plus 1/(X^2-1) (1e-12). **Impact:** R does not enter Proposition E or Lemma ce:values;
    `exact_part3` uses Y_W - sel - sav - census_small - Z_sel. It enters only C_W (the 0.0425629 of Remark
    ce:comparison), by <= 1.5e-11*eps.
30. **`dihedral_ceiling3.py:239`.** `int(round(N**0.5))` is used as a dictionary key. **Class (a), exact**
    (a wrong key would raise `KeyError`).
31. **`h_w_receipt.py:86`.** Arb tail. **Rigorous.**
32. **`reproduce_w3.py:314-315`.** The final check `Q(mid) + Q(rad) <= Q(C_eff)` uses the full printed
    ball. **Rigorous.**

## 4. Mathematical remainder bounds checked

1. **Cauchy and residue tail (`gkernel._cauchy_logbound`, `_tail_bound`).**
   * |Gamma(1+e)| <= Gamma(Re(1+e)) <= Gamma(1-rho) on |e| = rho, since Gamma decreases on (0, 1.46).
   * |1-e/k| >= 1 - rho/k.
   * For the other class, Gamma(-n+d+e) with d = ±1/2, by reflection:
     * |sin(pi z)| = |cos(pi e)| >= cos(pi rho);
     * |Gamma(sig+iy)| >= Gamma(sig) (pi y/sinh(pi y))^(1/2) >= 0.951 Gamma(sig) for sig >= 1 and
       |y| <= 1/4;
     * Gamma increases beyond 1.4616, and sig >= 1.5 is asserted.
   * Cauchy: divide by rho^(m-1). |x^-e| <= exp(rho |log x|).
   * The circle avoids every pole: rho = 1/4 < 1/2 with two classes, and n + a + b - rho > 0 is asserted.
   * Each factor of the consecutive ratio decreases in n, including the falling-factorial ratio for
     n >= k. So the ratio at n0 bounds all later ratios, and the tail is <= first/(1-r). Correct.
2. **Lemma lv:kernel(d) and A_c (`gkernel.tail_bound`).**
   * |Gamma(s+iy)/Gamma(s)|^2 = prod_k (1 + y^2/(s+k)^2)^-1 <= (1+y^2/s^2)^-1.
   * Bounding 1/|eta+iy| <= 1/eta:
     * m = 4: int (1+y^2/S^2)^-2 dy = pi S/2, so the bound is S/(4 eta);
     * m = 2: the bound is S/(2 eta).
   * This matches `mfac` (4 for octic, mixed31, mixed13; 2 for quartic).
   * The contour Re u = c >= 1 lies right of the pole at u = -b > 0 when b < 0. Correct.
3. **Lemma lv:remainders(b) (Rankin) and the degree-8 log E(beta).**
   * The local factors give |a_{p^k}|; beyond K0 = 60, |a_{p^k}| <= binom(k+7,7), with ratio <= 2x.
     2x <= 0.966 at p = 2, beta = 1.05.
   * The bound uses log(1+y) <= y.
   * Prime powers of q > p0: 36 sum n^-2 + 120 sum n^-3 + ... <= 36.01/p0 for p0 >= 2^18.
   * q > N: Stieltjes integration with pi(x) <= 1.25506 x/log x and the boundary term dropped gives
     8 * 1.25506 beta N^(1-beta)/((beta-1) log N).
   * Correct. Degree 4: |a_n| <= d_4(n) and zeta(beta)^4. Correct.
4. **`check_tail` (Lemma ce:kernel, x >= X).**
   * sum y^(k-1)/k <= 1+y and 1/(1-y) <= 1+2y for y <= 1/2.
   * e^-((sigma_j - sigma_1) x) decreases.
   * 2bX > 1 + 3e^-X implies 2bX(1-e^-X) > 1 + e^-X.
   * Correct.
5. **Archive majorants (only the short ones).**
   * `quadratic_majorant`: int_1^oo t^(b-1) e^-(xt) dt <= e^-x (1+1/x)/x for b <= 2.
   * `majorant`: K_0(y) <= sqrt(pi/2y) e^-y with t^(b-1/2) <= t.
   * The monotonicity conditions in `evaluate` are x > b - 1 and x > 2b - 3/2.
   * These looked right. I did not check them further.
6. **Kahan.** Higham's (4.8) has an unspecified O(n u^2) constant. leval uses 10 cnt u^2.
   * The counts per accumulator are <= about 1e8, so n u^2 <= 1.2e-24.
   * The unused 6u = 6.7e-16 absorbs any constant up to about 5e8.
   * This is a minor formal point, not a numerical risk.

## 5. Size of the slack, and whether a repair would matter

**Radius decomposition.** The computation is in `decomp8.py` and `decomp4.py`; the recomputed values are
bit-identical to `hp3`.

| source | relative radius of L | Dirichlet tail | moment float-error model | cell remainder | Arb rounding and kernel radii |
| --- | --- | --- | --- | --- | --- |
| degree 8, (19,23), 32 values | 7.8e-12 .. 4.9e-10 | > 99.95% | <= 1.8e-13 (<= 4.4e-4 of radius) | about 3e-30 | about 1e-43 |
| degree 4, orbit 19, 128 values | about 2.1e-13 | about 80% | <= 4.3e-14 (about 20%) | about 1e-30 | about 5e-23 |

**Half-width of sum_j c_j Y_W''(sigma_j).** From the stored data (`sens.py`) the total is 2.98e-7, split
as follows:

| source | contribution |
| --- | --- |
| `dafe.py` (orbits 10, 23, 24) | 2.84e-7 (95%) |
| degree 8 | 1.48e-8 |
| leval degree 4 | 1.5e-11 |
| Y_E | 1.5e-17 |

This agrees with the stored enclosure [0.000561206655994, 0.000561803331934].

**Sensitivity.** The upper end moves by 660.7*delta if all 576 L-balls are widened by a relative delta
(660.7 = sum|c_j| (448*2 + 128*4)/8192, with sum|c_j| = 3844.25).

* **Lemma ce:values.** Its displayed bound has slack 8.03e-15. It is consumed at delta = 1.2e-17, about
  0.1 ulp. Any regeneration that widens every L-ball by a tenth of an ulp would make the displayed digits
  0.00060783605369 false.
* **Theorem an:ceiling.** Its slack is 7.99e-8. It is consumed only at delta = 1.2e-10, which is as large as
  the degree-8 radii themselves.
* **The rk margin.** The (1+1e-6) margin on rk alone contributes <= 9.6e-16 to the upper end (`rkshare.py`).
  A tenfold larger margin (1e-5) would add about 8.6e-15 and exceed the displayed bound of Lemma ce:values.

**Assessment of repairs.**
* **Current edits.** None of the working-tree edits changes a stored L-value enclosure:
  * `w_arb` and `lptv.w`: < 1e-85;
  * Rsum: not used by the Lemma.
  
  The total upper end 0.00060783605368197 and C_eff,upper = 0.04227632008582 are unaffected.
* **Defensive repairs of the float bounds in `gkernel.py` and `leval.py`.** Recomputing those bounds in Arb
  would move the stored radii by at most:
  * kernel parts: <= 5e-23 relative;
  * moment-radius slack: <= 1e-9 * 1.8e-13 relative.
  
  The upper end would move by <= 1e-19, within the 8e-15 slack.
* **Recommendation.** For robustness, the displayed bound of Lemma ce:values could be loosened to
  0.000607837 (or 0.0006078361). Then:
  * 0.0416684840321405 + 0.000607837 = 0.04227632103 < 0.0422763211 < C_eff = 0.0422764;
  * the theorem keeps a slack of 7.9e-8.

## 6. Minimal repairs and hardening

None of these is needed for rigor.

1. **`signed.py:71`, `lptv.py:50`, `dihedral_ceiling.py:122`, `dihedral_ceiling3.py:205`.** Replace the
   float tails with Arb tails, as the working tree already does (`arb(0,1)*(2*term.upper())`,
   `interval241.logderiv_tail_bound`). The impact is nil.
2. **`gkernel.py:323`.** Write `if not ex > bA:` so that the test fails closed.
3. **`gkernel.py:321`.** Choose sigma_max exactly: the sig are A(b) + A(a_j) + cc, so take the largest
   a_j, or the union's upper end.
4. **`leval.py`.**
   * State the Kahan O(n u^2) constant with a reference, or note that the 6u spare covers any constant up to
     about 5e8.
   * Optionally compute eps_t, w and rad in Arb (no effect beyond 1e-19).
5. **Manuscript (Subsection lv:computation).** Add one sentence on the (1+1e-6) margin for the double sums
   of `octcoef.c` in the Rankin tail.
6. **`signed.py`.** Fix the docstring: "x >= log q_min = 14.85 (y <= 3.6e-7)".
7. **Fail-closed checks.**
   * Add an Arb check in `ce_values_digits.py` and/or `reproduce_w3.py` that `total_upper < 0.00060783605369`
     and `C_upper < 0.0422763201`, the displayed constants. Today only `C <= C_eff` is asserted.
   * Add `require_strict_upper_bound(lhs, 0.050969)` in `h_w_receipt.py`, as the 0.04273 repair did for
     `h241_receipt.py`.
8. **`hp/afe241hp_*.json`.** Regenerate the per-row informational floats with `outward_float_bounds`, or
   label them as informational. They are not consumed.

## 7. Not checked

* **The 1.0418235 archive.** I did not check `nonpositive-afe.py`, `hecke_afe.py` or their Section 4.7–4.9
  bounds, beyond reading `evaluate`, `finite_sum`, `majorant` and `quadratic_majorant`. These produce the
  `dafe` values (95% of the enclosure width) and Y_E.
* **The analytic formulas in `gkernel.py`.** I did not verify the residue-series formula F_{a,n}, the
  Taylor recursion constants, or the complete monotonicity proof beyond reading them. I relied on the
  manuscript's checks against PARI `lfun`.
* **Arithmetic inputs.** I did not check:
  * the PARI exports (Euler factors, conductors, gamma types, `export8.gp`, `exportg.gp`);
  * Lemma lv:coefficients;
  * the completeness of the n-enumeration in `octcoef.c` and `dcoef4.c`, beyond reading.
* **`octcoef.c` was not rerun.** The moments come from `deg8/data/*.mom.gz`; I did not verify their pinned
  hashes myself.
* **Coverage of the radius decomposition.** Only family (19,23) and orbit 19, at two abscissae, were
  recomputed and decomposed. The other families use the same code, and their stored radii have the same
  tail-dominated profile.
* **Runs not repeated.** I did not rerun `signed3.py certify`, `ce_values_digits.py` (it writes into the
  repository) or the full replay. Lemma ce:kernel's 1976 cells were not re-evaluated; only the stepping and
  the truncation bounds were.
* **Other parts.** I did not check the census programs beyond the bin-index slack, the combinatorics of D_W
  (residue degrees) in `h_w_receipt.py`, or the Lean side.
* **Assumptions.** IEEE-754 binary64 with round-to-nearest, glibc `log`/`pow` errors <= 1 ulp, and no
  `-ffast-math` in the original production builds. The flags were checked only in `reproduce_w3.py`.
