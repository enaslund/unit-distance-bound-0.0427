#!/usr/bin/env python3
"""Independent verification of the T38 finite certificate in the paper.

Checks, from first principles (exact integer/rational arithmetic where
possible, high-precision mpmath-free floats with generous margins elsewhere):

  1. T = first 38 odd primes; |T| = 38; D mod 8 = 3; #{q in T : q=3 mod 4} = 21.
  2. Ramified-prime witnesses (Appendix B): for each q in T there is q' in T
     with Legendre(q',q) = -1, and the listed witness works.
  3. S built from the stated rules; |S| = 314; U_S = 114; type counts
     (dyadic 1, ramified 38, inert 161, split 114); weight histogram;
     every odd prime in the two selection intervals is admissible;
     largest selected prime = 2267.
  4. Appendix A table matches the computed S exactly (p, k, e, status, witness
     validity).
  5. Exact rational check P(6/115) = -101/1520875 < 0 for
     P(t) = 1 - 38 t + 355 t^2 + 114 t^3, and the quadratic coefficient
     355 = g + |S| + 3.
  6. Sigma = sum log(k(p)+1)/(4 e(p)) and log A = sum k(p) log p / (2 e(p))
     against the displayed decimals; log(lambda^2) = log(16 D).
  7. N(R), M(R) at R = 2.688292831485591 with log B < 0.09, and
     N(R)/M(R) > 0.0358324.
"""
from fractions import Fraction
import math, os, re, sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

ok = True
def check(name, cond, detail=""):
    global ok
    status = "PASS" if cond else "FAIL"
    if not cond: ok = False
    print(f"[{status}] {name}" + (f"  {detail}" if detail else ""))

def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d, s = n-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def legendre(a, p):
    a %= p
    r = pow(a, (p-1)//2, p)
    return -1 if r == p-1 else r

# ---- 1. T ----
primes = [p for p in range(3, 2000) if is_prime(p)]
T = primes[:38]
check("T is the first 38 odd primes ending at 167", T[-1] == 167 and len(T) == 38, str(T[-5:]))
D = 1
for q in T: D *= q
check("D mod 8 == 3", D % 8 == 3, f"D mod 8 = {D%8}")
n3 = sum(1 for q in T if q % 4 == 3)
check("#{q=3 mod 4} = 21 (odd)", n3 == 21, f"count = {n3}")

# ---- 2. witnesses for q in T ----
wit_ok = all(any(legendre(qp, q) == -1 for qp in T if qp != q) for q in T)
check("every q in T has a witness q' in T with (q'/q) = -1", wit_ok)
appB = {3:5,5:3,7:3,11:7,13:5,17:3,19:3,23:5,29:3,31:3,37:5,41:3,43:3,47:5,53:3,
        59:11,61:7,67:3,71:7,73:5,79:3,83:5,89:3,97:5,101:3,103:3,107:5,109:11,
        113:3,127:3,131:17,137:3,139:3,149:3,151:3,157:5,163:3,167:5}
check("Appendix B witness table entries all satisfy (q'/q) = -1",
      set(appB) == set(T) and all(legendre(w, q) == -1 for q, w in appB.items()))

# ---- 3. build S ----
def admissible(p):
    if p % 4 == 1: return True
    return any(legendre(q, p) == -1 for q in T if q != p)

def status(p):
    if p == 2: return "dyadic"
    if p in T: return "ramified"
    return "split" if legendre(D, p) == 1 else "inert"

S = [2]
for p in range(3, 2268):
    if not is_prime(p): continue
    if p <= 283:
        S.append(p)
    else:
        st = status(p)
        if st == "split" and p <= 1973 and admissible(p): S.append(p)
        elif st == "inert" and p <= 2267 and admissible(p): S.append(p)

check("|S| = 314", len(S) == 314, f"|S| = {len(S)}")
check("largest selected prime = 2267", max(S) == 2267, str(max(S)))
U_S = sum(1 for p in S if p != 2 and status(p) == "split")
check("U_S = 114", U_S == 114, f"U_S = {U_S}")
tc = {"dyadic":0,"ramified":0,"inert":0,"split":0}
for p in S: tc[status(p)] += 1
check("type counts dyadic/ramified/inert/split = 1/38/161/114",
      (tc["dyadic"],tc["ramified"],tc["inert"],tc["split"]) == (1,38,161,114), str(tc))
all_adm = all(admissible(p) for p in range(284, 2268) if is_prime(p) and (
    (status(p)=="split" and p<=1973) or (status(p)=="inert" and p<=2267)))
check("every odd prime in the selection intervals is admissible", all_adm)
# also the claim: for this T, EVERY odd prime in (283,1973] resp (283,2267] is admissible
all_adm2 = all(admissible(p) for p in range(284, 2268) if is_prime(p))
check("in fact every odd prime in (283,2267] is admissible", all_adm2)

def weight(p):
    if p == 2: return 19
    if p == 3: return 12
    if p == 5: return 8
    if p == 7: return 6
    if p == 11: return 5
    if p in (13,17,19): return 4
    if 23 <= p <= 53: return 3
    if 59 <= p <= 283: return 2
    return 1

hist = {}
for p in S: hist[weight(p)] = hist.get(weight(p), 0) + 1
expect_hist = {1:253,2:45,3:8,4:3,5:1,6:1,8:1,12:1,19:1}
check("weight histogram matches", hist == expect_hist, str(sorted(hist.items())))

# ---- 4. appendix table ----
tab = open(os.path.join(REPO_ROOT, "appendices", "selected_prime_certificate.tex")).read()
rows = re.findall(r"^(\d+) & (\d+) & (\d+) & (\w+) &\s*(\d*)\s*\\\\", tab, re.M)
check("appendix table has 314 rows", len(rows) == 314, f"{len(rows)} rows")
tab_ok, wit_tab_ok = True, True
seen = []
for (ps, ks, es, st, w) in rows:
    p, k, e = int(ps), int(ks), int(es)
    seen.append(p)
    e_exp = 4 if p == 2 else (2 if p in T else 1)
    if not (p in S and k == weight(p) and e == e_exp and st == status(p)):
        tab_ok = False; print(f"   row mismatch: {p} {k} {e} {st}")
    if p == 2:
        if w != "5": wit_tab_ok = False
    elif p % 4 == 1:
        if w != "": wit_tab_ok = False; print(f"   unexpected witness for {p} = 1 mod 4: {w}")
    else:
        if not w or int(w) not in T or (int(w) != p and legendre(int(w), p) != -1):
            wit_tab_ok = False; print(f"   bad witness for {p}: '{w}'")
check("appendix rows match computed (p,k,e,status)", tab_ok and sorted(seen) == sorted(S))
check("appendix witnesses valid ((q/p)=-1 for p != 1 mod 4)", wit_tab_ok)

# ---- 5. exact GS polynomial ----
g = 38
c2 = g + len(S) + 3
check("degree-2 coefficient = g+|S|+3 = 355", c2 == 355, str(c2))
t = Fraction(6, 115)
P = 1 - g*t + c2*t*t + U_S*t**3
check("P(6/115) = -101/1520875 exactly", P == Fraction(-101, 1520875), str(P))
check("P(6/115) < 0", P < 0)
# stated real minimum
tau0 = 0.05220818647952869
Pmin = 1 - 38*tau0 + 355*tau0**2 + 114*tau0**3
check("P(tau0) approx -6.68471161139e-5", abs(Pmin + 6.68471161139e-5) < 1e-15, f"{Pmin:.6e}")

# ---- 6. logarithmic sums ----
def e_of(p): return 4 if p == 2 else (2 if p in T else 1)
Sigma = sum(math.log(weight(p)+1)/(4*e_of(p)) for p in S)
logA  = sum(weight(p)*math.log(p)/(2*e_of(p)) for p in S)
check("Sigma = 56.2819843775269...", abs(Sigma - 56.2819843775269) < 1e-10, f"{Sigma:.13f}")
check("log A = 1093.4272954355824...", abs(logA - 1093.4272954355824) < 1e-9, f"{logA:.10f}")
loglam2 = math.log(16*D)
check("log(lambda^2) = 154.01230121116885...", abs(loglam2 - 154.01230121116885) < 1e-10, f"{loglam2:.14f}")

# ---- 7. master exponent ----
loglam = loglam2/2
logB = 0.09
R = 2.688292831485591
lam_over_2A = math.exp(loglam - math.log(2) - logA)
N = 0.5*math.log(1-1/(4*R*R)) + Sigma + 0.5*math.log(2*math.pi) - 0.25*loglam - 0.5*logB
M = logA + math.log(R + lam_over_2A) + 0.5*math.log(2*math.pi*math.e) - 0.5*loglam
check("N(R) > 37.8867825632423", N > 37.8867825632423, f"N = {N:.13f}")
check("M(R) < 1057.332065023008", M < 1057.332065023008, f"M = {M:.13f}")
check("N/M > 0.0358324", N/M > 0.0358324, f"N/M = {N/M:.10f}")
check("log(lambda/(2A)) approx -1017.114292", abs((loglam - math.log(2) - logA) + 1017.114292) < 1e-5,
      f"{loglam - math.log(2) - logA:.6f}")
# R optimality sanity: is stated R near the argmax of N/M?
best = max(((0.5*math.log(1-1/(4*r*r)) + Sigma + 0.5*math.log(2*math.pi) - 0.25*loglam - 0.5*logB) /
            (logA + math.log(r + lam_over_2A) + 0.5*math.log(2*math.pi*math.e) - 0.5*loglam), r)
           for r in [R*(1+eps) for eps in (-1e-3,-1e-4,-1e-5,0,1e-5,1e-4,1e-3)])
check("stated R is a local optimum of N/M to ~1e-5", abs(best[1]-R)/R < 2e-4, f"best r = {best[1]:.9f}, ratio {best[0]:.10f}")

print()
print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
sys.exit(0 if ok else 1)
