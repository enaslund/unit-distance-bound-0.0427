import sys
import numpy as np
from design import c1, dyadic, block, uncapped, pt, arch, C_SLACK, LOG2
from optimize import options, PR


def solve_fast(delta, t, rho, JRi=0.0, res=2e-4, primes=PR, extra_base=0.0, allow_f1=False):
    base = 1 - 2 * t + dyadic(t) + c1(t) + rho * (t - c1(t)) + extra_base
    Mbase = pt(delta, 2, 8, 4) - (0.5 - delta) * 2.25 * LOG2 - C_SLACK + arch(delta, rho, JR_improve=JRi)
    items = [options(delta, t, q, allow_f1) for q in primes]
    lo = sum(min(o[0] for o in opts) for opts in items)
    hi = sum(max(o[0] for o in opts) for opts in items)
    off = int(np.floor(lo / res)) - 2
    n = int(np.ceil(hi / res)) - off + 3
    best = np.full(n, -np.inf)
    best[-off] = 0.0
    choice = []
    for opts in items:
        new = np.full(n, -np.inf)
        arg = np.zeros(n, dtype=np.int16)
        for j, (dP, dM, lab) in enumerate(opts):
            s = int(np.ceil(dP / res - 1e-12))
            sh = np.full(n, -np.inf)
            if s >= 0:
                sh[s:] = best[:n - s]
            else:
                sh[:n + s] = best[-s:]
            cand = sh + dM
            m = cand > new
            new[m] = cand[m]
            arg[m] = j
        choice.append(arg)
        best = new
    idx = np.arange(n)
    feas = (idx + off) * res < -base
    if not feas.any():
        return -np.inf, None
    b = int(np.argmax(np.where(feas, best, -np.inf)))
    M = best[b]
    if not np.isfinite(M):
        return -np.inf, None
    ch = []
    for q, opts, arg in zip(reversed(primes), reversed(items), reversed(choice)):
        j = arg[b]
        dP, dM, lab = opts[j]
        if lab != '-':
            ch.append((q, lab))
        b -= int(np.ceil(dP / res - 1e-12))
    return Mbase + M, ch[::-1]


def best_delta(rho, ts, lo=0.034, hi=0.05, JRi=0.0, **kw):
    info = None
    for _ in range(16):
        mid = (lo + hi) / 2
        bestM, bi = -np.inf, None
        for t in ts:
            M, ch = solve_fast(mid, t, rho, JRi, **kw)
            if M > bestM:
                bestM, bi = M, (t, M, ch)
        if bestM > 0:
            lo = mid
            info = (mid,) + bi
        else:
            hi = mid
    return lo, info


if __name__ == "__main__":
    import time
    rhos = [float(x) for x in sys.argv[1:]] or [0.0, 1.0]
    ts = np.arange(0.24, 0.42, 0.0025)
    for rho in rhos:
        t0 = time.time()
        d, info = best_delta(rho, ts)
        print("rho", rho, "delta", round(d, 6), "t", round(info[1], 4), info[3], "(%.0fs)" % (time.time() - t0), flush=True)
