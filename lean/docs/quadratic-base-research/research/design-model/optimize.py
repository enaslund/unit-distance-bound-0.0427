"""Multiple-choice knapsack over primes for the GS/margin model."""
import sys
import numpy as np
from design import (c1, dyadic, block, uncapped, pt, arch, C_SLACK, LOG2)

PR = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
      101, 103, 107, 109, 113, 127, 131]


def options(delta, t, q, allow_f1=False, ram_types=(0, 2, 4, 8), unram_f=(2, 4, 8)):
    """list of (dP, dM, label)."""
    opts = [(0.0, 0.0, "-")]
    rdc = -(0.5 - delta) * 0.5 * np.log(q)
    if q <= 41:
        for ty in ram_types:
            if ty == 0:
                opts.append((-t + uncapped(t), rdc, "R:U"))
            else:
                opts.append((-t + block(t, 2, ty), rdc + pt(delta, q, 2, ty), f"R:{ty}"))
    for f in unram_f:
        opts.append((block(t, 1, f), pt(delta, q, 1, f), f"u:{f}"))
    if allow_f1:
        opts.append((t, pt(delta, q, 1, 1), "u:1"))
    return opts


def solve(delta, t, rho_r, allow_f1=False, JR_improve=0.0, fixed=None, primes=PR, grid=4000):
    base = 1 - 2 * t + dyadic(t) + c1(t) + rho_r * (t - c1(t))
    Mbase = pt(delta, 2, 8, 4) - (0.5 - delta) * 2.25 * LOG2 - C_SLACK + arch(delta, rho_r, JR_improve=JR_improve)
    # exact DP on discretised cost (budget must make total P < 0)
    items = []
    for q in primes:
        opts = options(delta, t, q, allow_f1)
        if fixed and q in fixed:
            opts = [o for o in opts if o[2] == fixed[q]]
        items.append((q, opts))
    # cost range
    lo = sum(min(o[0] for o in opts) for _, opts in items)
    hi = sum(max(o[0] for o in opts) for _, opts in items)
    # we need base + sum dP < 0  => sum dP < -base
    cap = -base
    # DP over cost buckets with resolution
    res = (hi - lo) / grid
    if res <= 0:
        res = 1e-6
    NEG = -1e18
    dp = {0: (0.0, [])}  # bucket(sum of rounded-up costs) -> (M, choices)
    for q, opts in items:
        nd = {}
        for b, (m, ch) in dp.items():
            for dP, dM, lab in opts:
                nb = b + int(np.ceil(dP / res - 1e-12))
                val = m + dM
                if nb not in nd or nd[nb][0] < val:
                    nd[nb] = (val, ch + [(q, lab)] if lab != "-" else ch)
        # prune dominated: keep for each bucket best, and remove buckets with lower value than a cheaper bucket
        keys = sorted(nd)
        best = NEG
        pr = {}
        for k in keys:
            if nd[k][0] > best + 1e-12:
                pr[k] = nd[k]
                best = nd[k][0]
        dp = pr
    bestM, bestch = NEG, None
    for b, (m, ch) in dp.items():
        if b * res < cap - 1e-9:
            if m > bestM:
                bestM, bestch = m, ch
    return Mbase + bestM, bestch


def best_delta(rho_r, allow_f1=False, JR_improve=0.0, ts=np.linspace(0.22, 0.42, 21), lo=0.035, hi=0.07, fixed=None):
    bestd, bestinfo = None, None
    for _ in range(18):
        mid = (lo + hi) / 2
        ok = None
        for t in ts:
            M, ch = solve(mid, t, rho_r, allow_f1, JR_improve, fixed)
            if M > 0:
                ok = (t, M, ch)
                break
        if ok:
            lo = mid
            bestinfo = (mid,) + ok
        else:
            hi = mid
    return lo, bestinfo


if __name__ == "__main__":
    rho = float(sys.argv[1]) if len(sys.argv) > 1 else 0.0
    f1 = len(sys.argv) > 2 and sys.argv[2] == "f1"
    d, info = best_delta(rho, f1)
    print("rho_r", rho, "allow_f1", f1, "best delta", d)
    print(info)
