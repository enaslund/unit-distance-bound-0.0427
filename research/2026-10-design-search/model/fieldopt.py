"""General per-field design optimizer (model, not proof).
Field data: m=[B:Q], r1, r2, logrd, splitting {q: [(eB, fB), ...]} for primes of B above q.
GS: P = 1 - s_D + sum beta(places) < 0 ; margin per degree of F."""
import _paths  # noqa: F401
import numpy as np, functools
from model import best_local, JD_gauss, JR_gauss, JC_gauss, LOG2, LOGPI
from design import JD_IMPROVE
C_SLACK = 0.0070444

@functools.lru_cache(maxsize=None)
def logF(dkey, Q):
    v, k, _ = best_local(dkey/1e9, float(Q), kmax=60, shells=False)
    return v + np.log(1 - 1/Q)
def pt(delta, q, e, f):
    return logF(int(round(delta*1e9)), q**f) / (e*f)

def hD(t): return (1+t)**3*(1+t*t)**2
def sD(t): return t*t*(1-t**7/hD(t))

def place_options(delta, t, q, eB, fB, m):
    """options for one prime of B: list of (beta, dmargin, label). dmargin per degree of F."""
    w = eB*fB/m        # fraction of degree above this prime
    lq = np.log(q)
    o = []
    if q == 2:
        if eB == 1 and fB == 1:
            o.append((2*t-1+1/hD(t), w*pt(delta, 2, 8, 4) - (0.5-delta)*w*2.25*LOG2, 'D'))
        else:
            o.append((None, None, 'unsupported'))
        return o
    o.append((0.0, 0.0, '-'))
    if eB == 1:
        ram = -(0.5-delta)*w*0.5*lq
        o.append((t-1+1/(1+t)**2, ram + w*pt(delta, q, 2, 2*fB), 'R22'))
        o.append((t*t/(1+t),      ram + w*pt(delta, q, 2, fB), 'R21'))
        o.append((t-1+1/((1+t)**2*(1+t*t)), ram + w*pt(delta, q, 2, 4*fB), 'R24'))
        o.append((t,              w*pt(delta, q, 1, fB), 'u1'))
        o.append((t*t/(1+t),      w*pt(delta, q, 1, 2*fB), 'u2'))
        o.append((t**4/((1+t)*(1+t*t)), w*pt(delta, q, 1, 4*fB), 'u4'))
    else:
        # ramified in B (tame, e=2): tower unramified; caps
        o.append((t,              w*pt(delta, q, eB, fB), 'u1'))
        o.append((t*t/(1+t),      w*pt(delta, q, eB, 2*fB), 'u2'))
        o.append((t**4/((1+t)*(1+t*t)), w*pt(delta, q, eB, 4*fB), 'u4'))
    return o

def arch_terms(delta):
    JD = JD_gauss(delta) + JD_IMPROVE
    SR = LOG2 + JR_gauss(delta)
    CX = (1-delta)*LOG2 + (LOGPI + JD)/2
    return SR, CX

def solve(delta, t, field, res=1e-4):
    m, r1, r2, logrd, split = field['m'], field['r1'], field['r2'], field['logrd'], field['split']
    SR, CX = arch_terms(delta)
    base = 1 - sD(t) - r2*t     # complex places
    Mbase = -(0.5-delta)*logrd - C_SLACK + (2*r2/m)*CX
    items = []
    # real places: keep (beta=-t/(1+t), CX) or kill (beta=0, SR); at least one kept -> force first kept
    base += -t/(1+t); Mbase += CX/m
    for i in range(r1-1):
        items.append(('real', [(-t/(1+t), CX/m, 'keep'), (0.0, SR/m, 'kill')]))
    for q, pl in split.items():
        for (eB, fB) in pl:
            opts = place_options(delta, t, q, eB, fB, m)
            if any(o[0] is None for o in opts): return -np.inf, None
            items.append((q, opts))
    lo = sum(min(o[0] for o in op) for _, op in items); hi = sum(max(o[0] for o in op) for _, op in items)
    off = int(np.floor(lo/res)) - 2; n = int(np.ceil(hi/res)) - off + 3
    best = np.full(n, -np.inf); best[-off] = 0.0; choice = []
    for q, op in items:
        new = np.full(n, -np.inf); arg = np.zeros(n, dtype=np.int16)
        for j, (dP, dM, lab) in enumerate(op):
            s = int(np.ceil(dP/res - 1e-12)); sh = np.full(n, -np.inf)
            if s >= 0: sh[s:] = best[:n-s]
            else: sh[:n+s] = best[-s:]
            cand = sh + dM; mk = cand > new; new[mk] = cand[mk]; arg[mk] = j
        choice.append(arg); best = new
    idx = np.arange(n); feas = (idx + off)*res < -base
    if not feas.any(): return -np.inf, None
    b = int(np.argmax(np.where(feas, best, -np.inf))); M = best[b]
    ch = []
    for (q, op), arg in zip(reversed(items), reversed(choice)):
        j = arg[b]; dP, dM, lab = op[j]
        if lab not in ('-',): ch.append((q, lab))
        b -= int(np.ceil(dP/res - 1e-12))
    return Mbase + M, ch[::-1]

def best_delta(field, ts=np.arange(0.10, 0.42, 0.01), lo=0.02, hi=0.15, iters=14):
    info = None
    for _ in range(iters):
        mid = (lo+hi)/2; bM, bi = -np.inf, None
        for t in ts:
            M, ch = solve(mid, t, field)
            if M > bM: bM, bi = M, (round(t, 3), ch)
        if bM > 0: lo, info = mid, bi
        else: hi = mid
    return lo, info

def compress(ch):
    from collections import Counter
    return dict(Counter(ch))

if __name__ == "__main__":
    # sanity: Q(sqrt241)
    f241 = dict(m=2, r1=2, r2=0, logrd=0.5*np.log(241),
                split={2: [(1,1)]*2, 3: [(1,1)]*2, 5: [(1,1)]*2, 7: [(1,2)], 11: [(1,2)], 13: [(1,2)], 17: [(1,2)],
                       19: [(1,2)], 23: [(1,2)], 29: [(1,1)]*2, 31: [(1,2)], 37: [(1,2)], 41: [(1,1)]*2, 43: [(1,2)], 47: [(1,1)]*2})
    d, info = best_delta(f241)
    print("Q(sqrt241) model:", round(d, 5), info[0], compress(info[1]))
