import _paths  # noqa: F401
import sys, numpy as np
from fieldopt2 import margin_at, bisect
from fieldopt import compress
from quadall import kron, PR
def isfund_neg(d):
    D = -d
    if D % 4 != 1: return False
    for q in range(2, int(d**0.5)+1):
        if d % (q*q) == 0: return False
    return True
def fieldI(d):
    D = -d
    sp = {2: [(1,1)]*2}
    for p in PR:
        k = kron(D % (p if p > 2 else 8) if False else D, p) if p != 2 else 1
        if D % p == 0: sp[p] = [(2,1)]
        else:
            k = 1 if pow(D % p, (p-1)//2, p) == 1 else -1
            sp[p] = [(1,1)]*2 if k == 1 else [(1,2)]
    return dict(m=2, r1=0, r2=1, logrd=0.5*np.log(d), split=sp, cm=True)
if __name__ == "__main__":
    dmax = int(sys.argv[1])
    res = []
    for d in range(7, dmax, 8):
        if not isfund_neg(d): continue
        fd = fieldI(d)
        M, _ = margin_at(fd, 0.04, ts=np.arange(0.18, 0.36, 0.03))
        res.append((M, d))
    res.sort(reverse=True)
    for M, d in res[:15]:
        dd, info = bisect(fieldI(d), lo=0.03, hi=0.08)
        print(f"d {d} rd {d**0.5:.1f} M04 {M:+.4f} delta {dd:.4f} t {info[0] if info else ''} {compress(info[1]) if info else ''}", flush=True)
