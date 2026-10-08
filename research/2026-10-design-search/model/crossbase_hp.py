"""Same-model comparison of the best bases with weighted (six-shell) local functionals."""
import _paths  # noqa: F401
import functools, numpy as np
import fieldopt as FO
from fieldopt import compress
from fieldopt2 import bisect
from model import best_local
@functools.lru_cache(maxsize=None)
def logF_w(dkey, Q):
    v, k, _ = best_local(dkey/1e9, float(Q), kmax=60, shells=True)
    return v + np.log(1 - 1/Q)
FO.logF = logF_w      # pt() looks up logF by name at call time
def kron(D, p):
    if D % p == 0: return 0
    return 1 if pow(D % p, (p-1)//2, p) == 1 else -1
PR = [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53]
def quad(D, cm=False):
    sp = {2: [(1,1)]*2}
    for p in PR:
        k = kron(D, p)
        sp[p] = [(1,1)]*2 if k == 1 else ([(1,2)] if k == -1 else [(2,1)])
    if cm: return dict(m=2, r1=0, r2=1, logrd=0.5*np.log(-D), split=sp, cm=True)
    return dict(m=2, r1=2, r2=0, logrd=0.5*np.log(D), split=sp)
cands = [('Q(sqrt 241)', quad(241)), ('Q(sqrt 41)', quad(41)), ('Q(sqrt 1009)', quad(1009)),
         ('Q(sqrt -31)', quad(-31, cm=True)), ('Q(sqrt -311)', quad(-311, cm=True))]
for name, f in cands:
    d, info = bisect(f, lo=0.038, hi=0.046, iters=20, ts=np.arange(0.20, 0.34, 0.005))
    print(f"{name:14s} delta = {d:.6f}  t = {info[0]}  {compress(info[1])}", flush=True)
