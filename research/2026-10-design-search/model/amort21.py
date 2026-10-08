import _paths  # noqa: F401
import sys, numpy as np
import optimize, fastopt
from design import c1, dyadic, PD, pt
ORIG = optimize.options
def options(delta, t, q, allow_f1=False, **kw):
    o = ORIG(delta, t, q, allow_f1)
    if q <= 41:
        rdc = -(0.5 - delta) * 0.5 * np.log(q)
        o.append((t*t/(1+t), rdc + pt(delta, q, 2, 1), "R:1"))
    return o
fastopt.options = options
def sD(t): return t*t*(1-t**7/PD(t))
def best(m, ell_extra, primes=optimize.PR[:14], ts=np.arange(0.18, 0.40, 0.01)):
    lo, hi = 0.03, 0.12; info = None
    for _ in range(14):
        mid = (lo+hi)/2; bM = -np.inf; bi = None
        for t in ts:
            M, ch = fastopt.solve_fast(mid, t, 0.0, extra_base=-(1-sD(t))*(1-1/m), primes=primes, allow_f1=True)
            M -= (0.5-mid)*ell_extra
            if M > bM: bM, bi = M, (t, ch)
        if bM > 0: lo = mid; info = bi
        else: hi = mid
    return lo, info
if __name__ == "__main__":
    for m, rd in [(2, 241**0.5), (4, 38.7), (4, 45), (8, 60), (8, 80), (1e9, 60)]:
        d, info = best(m, np.log(rd))
        print("m", m, "rd(B)", rd, "delta", round(d, 5), info, flush=True)
