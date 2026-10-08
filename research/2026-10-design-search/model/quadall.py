import _paths  # noqa: F401
import sys, numpy as np
from fieldopt import solve, compress
def kron(D, p):
    if D % p == 0: return 0
    if p == 2: return 1 if D % 8 in (1, 7) else -1
    return 1 if pow(D % p, (p-1)//2, p) == 1 else -1
def isfund(D):
    if D % 4 == 1:
        f = D
        for q in range(2, int(f**0.5)+1):
            if f % (q*q) == 0: return False
        return True
    return False
PR = [3,5,7,11,13,17,19,23,29,31,37,41,43,47]
def fieldD(D):
    sp = {2: [(1,1)]*2}
    for p in PR:
        k = kron(D, p)
        sp[p] = [(1,1)]*2 if k == 1 else ([(1,2)] if k == -1 else [(2,1)])
    return dict(m=2, r1=2, r2=0, logrd=0.5*np.log(D), split=sp)
def margin_at(fd, delta, ts=np.arange(0.16, 0.36, 0.02)):
    best = (-np.inf, None)
    for t in ts:
        M, ch = solve(delta, t, fd)
        if M > best[0]: best = (M, (round(t,3), ch))
    return best
def bisect(fd, lo=0.03, hi=0.08, iters=12):
    info = None
    for _ in range(iters):
        mid = (lo+hi)/2
        M, bi = margin_at(fd, mid)
        if M > 0: lo, info = mid, bi
        else: hi = mid
    return lo, info
if __name__ == "__main__":
    Dmax = int(sys.argv[1])
    res = []
    for D in range(17, Dmax, 8):
        if not isfund(D): continue
        fd = fieldD(D)
        M, _ = margin_at(fd, 0.04, ts=np.arange(0.18, 0.34, 0.04))
        res.append((M, D))
    res.sort(reverse=True)
    for M, D in res[:15]:
        d, info = bisect(fieldD(D))
        ram = [p for p in PR if D % p == 0]
        print(f"D {D} rd {D**0.5:.1f} ram {ram} M04 {M:+.4f} delta {d:.4f} t {info[0] if info else ''} {compress(info[1]) if info else ''}", flush=True)
