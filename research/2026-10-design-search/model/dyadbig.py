import _paths  # noqa: F401
import numpy as np, sys
import fieldopt as FO
from fieldopt import pt, compress, LOG2
from fieldopt2 import bisect
def hil(dims, t):
    h = 1.0
    for i, d in enumerate(dims): h *= (1 + t**(i+1))**d
    return h
def run(diffs, label):
    # diffs: dict w -> ord2(Different) for a dyadic group with Jennings [3, w] (e=8,f=4 assumed for selected value)
    orig = FO.place_options
    def place_options(delta, t, q, eB, fB, m):
        if q != 2: return orig(delta, t, q, eB, fB, m)
        w_ = eB*fB/m
        o = []
        for w, dd in diffs.items():
            beta = 3*t - 1 + 1/hil([3, w], t) - t
            o.append((beta, w_*pt(delta, 2, 8, 4) - (0.5-delta)*w_*dd*LOG2, f'G{w}'))
        return o
    FO.place_options = place_options
    f241 = dict(m=2, r1=2, r2=0, logrd=0.5*np.log(241),
                split={2: [(1,1)]*2, 3: [(1,1)]*2, 5: [(1,1)]*2, 7: [(1,2)], 11: [(1,2)], 13: [(1,2)], 17: [(1,2)],
                       19: [(1,2)], 23: [(1,2)], 29: [(1,1)]*2, 31: [(1,2)], 37: [(1,2)], 41: [(1,1)]*2, 43: [(1,2)], 47: [(1,1)]*2})
    d, info = bisect(f241, lo=0.035, hi=0.09)
    FO.place_options = orig
    print(label, round(d, 4), info[0], compress(info[1]), flush=True)
for step in (0.15, 0.25, 0.35, 0.5):
    run({2: 2.25, 3: 2.25+step, 4: 2.25+2*step, 5: 2.25+3*step}, f"step {step}:")
print("exact dyadic differents:")
run({2: 2.25, 3: 2.625, 4: 3.0625, 5: 2 + 196/128}, "exact:")
