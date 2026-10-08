import _paths  # noqa: F401
import sys, numpy as np
import quadbase, quad21
from design import c1, dyadic, pt, arch, C_SLACK, LOG2, PD
from optimize import PR
from util import L
def sD(t): return t*t*(1-t**7/PD(t))
def solve(delta, t, D, rho, res=2e-4, primes=PR):
    # per-copy base; killing the second real place: +(t - c1)/2 per copy, arch with split-real fraction rho
    base = 1 - 2*t + dyadic(t) + c1(t) - (1 - sD(t))/2 + rho*(t - c1(t))
    Mbase = pt(delta, 2, 8, 4) - (0.5-delta)*(2.25*LOG2 + 0.5*np.log(D)) - C_SLACK + arch(delta, rho)
    items = []
    for q in primes:
        if D % q == 0: continue
        items.append((q, quadbase.opts_split(delta, t, q) if L(D, q) == 1 else quadbase.opts_inert(delta, t, q)))
    lo = sum(min(o[0] for o in op) for _, op in items); hi = sum(max(o[0] for o in op) for _, op in items)
    off = int(np.floor(lo/res)) - 2; n = int(np.ceil(hi/res)) - off + 3
    best = np.full(n, -np.inf); best[-off] = 0.0; choice = []
    for q, op in items:
        new = np.full(n, -np.inf); arg = np.zeros(n, dtype=np.int16)
        for j, (dP, dM, lab) in enumerate(op):
            s = int(np.ceil(dP/res - 1e-12)); sh = np.full(n, -np.inf)
            if s >= 0: sh[s:] = best[:n-s]
            else: sh[:n+s] = best[-s:]
            cand = sh + dM; m = cand > new; new[m] = cand[m]; arg[m] = j
        choice.append(arg); best = new
    idx = np.arange(n); feas = (idx + off)*res < -base
    if not feas.any(): return -np.inf, None
    b = int(np.argmax(np.where(feas, best, -np.inf))); M = best[b]
    ch = []
    for (q, op), arg in zip(reversed(items), reversed(choice)):
        j = arg[b]; dP, dM, lab = op[j]
        if lab != '-': ch.append((q, lab))
        b -= int(np.ceil(dP/res - 1e-12))
    return Mbase + M, ch[::-1]
def best_delta(D, rho, ts=np.arange(0.12, 0.40, 0.005), lo=0.03, hi=0.09):
    info = None
    for _ in range(15):
        mid = (lo+hi)/2; bM, bi = -np.inf, None
        for t in ts:
            M, ch = solve(mid, t, D, rho)
            if M > bM: bM, bi = M, (t, ch)
        if bM > 0: lo, info = mid, bi
        else: hi = mid
    return lo, info
if __name__ == "__main__":
    for D in [int(x) for x in sys.argv[1:]]:
        for rho in (0.0, 0.5):
            d, info = best_delta(D, rho)
            print("D", D, "rho", rho, "delta", round(d, 5), info, flush=True)
