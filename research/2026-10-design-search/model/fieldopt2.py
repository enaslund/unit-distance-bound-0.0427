"""fieldopt with support for totally complex (CM) bases: iota from a subfield, no kept real place."""
import _paths  # noqa: F401
import numpy as np
import fieldopt as FO
from fieldopt import place_options, arch_terms, sD, C_SLACK

def solve(delta, t, field, res=1e-4):
    if not field.get('cm'):
        return FO.solve(delta, t, field, res)
    m, r2, logrd, split = field['m'], field['r2'], field['logrd'], field['split']
    SR, CX = arch_terms(delta)
    base = 1 - sD(t) - r2*t
    Mbase = -(0.5-delta)*logrd - C_SLACK + CX     # all of F's degree complex-type
    items = []
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

def margin_at(fd, delta, ts=np.arange(0.14, 0.36, 0.02)):
    best = (-np.inf, None)
    for t in ts:
        M, ch = solve(delta, t, fd)
        if M > best[0]: best = (M, (round(t, 3), ch))
    return best

def bisect(fd, lo=0.03, hi=0.1, iters=12, ts=np.arange(0.14, 0.36, 0.02)):
    info = None
    for _ in range(iters):
        mid = (lo+hi)/2
        M, bi = margin_at(fd, mid, ts)
        if M > 0: lo, info = mid, bi
        else: hi = mid
    return lo, info
