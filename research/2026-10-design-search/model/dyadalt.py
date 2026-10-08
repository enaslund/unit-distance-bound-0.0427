import _paths  # noqa: F401
import numpy as np
import fieldopt as FO
from fieldopt import pt, compress, LOG2
from fieldopt2 import bisect
# dyadic options: (label, e, f, ordDiff, jennings dims list)
DY = [('D', 8, 4, 2.25, [3, 2]), ('M16', 8, 2, 2.25, [3, 1]), ('E2', 4, 2, 2.0, [3]),
      ('Z8U4', 4, 4, 2.0, [3, 1]), ('Z8', 4, 1, 2.0, [2]), ('Z16', 8, 1, 3.0, [2, 1]),
      ('Z16r5', 8, 2, 3.0, [3, 1]), ('DU8', 8, 8, 2.25, [3, 2, 0, 1])]
def hil(dims, t):
    h = 1.0
    for i, d in enumerate(dims): h *= (1 + t**(i+1))**d
    return h
orig = FO.place_options
def place_options(delta, t, q, eB, fB, m):
    if q != 2: return orig(delta, t, q, eB, fB, m)
    w = eB*fB/m
    if not (eB == 1 and fB == 1): return [(None, None, 'unsupported')]
    o = []
    for lab, e, f, od, dims in DY:
        beta = 3*t - 1 + 1/hil(dims, t) - t
        o.append((beta, w*pt(delta, 2, e, f) - (0.5-delta)*w*od*LOG2, lab))
    return o
FO.place_options = place_options
# NB: the rd contribution of 2 must be removed from logrd model: fieldopt adds dyadic ell inside options (as before)
f241 = dict(m=2, r1=2, r2=0, logrd=0.5*np.log(241),
            split={2: [(1,1)]*2, 3: [(1,1)]*2, 5: [(1,1)]*2, 7: [(1,2)], 11: [(1,2)], 13: [(1,2)], 17: [(1,2)],
                   19: [(1,2)], 23: [(1,2)], 29: [(1,1)]*2, 31: [(1,2)], 37: [(1,2)], 41: [(1,1)]*2, 43: [(1,2)], 47: [(1,1)]*2})
d, info = bisect(f241, lo=0.035, hi=0.07)
print("241 with dyadic alternatives:", round(d, 4), info[0], compress(info[1]))
for x in (0.05, 0.1, 0.2):
    o = FO.sD; FO.sD = lambda t, x=x, o=o: o(t) + x
    d, info = bisect(f241, lo=0.035, hi=0.1)
    FO.sD = o
    print(" extra", x, round(d, 4), info[0], compress(info[1]))
