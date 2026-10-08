import _paths  # noqa: F401
import numpy as np
import fieldopt as FO
from fieldopt import compress
from fieldopt2 import bisect
f241 = dict(m=2, r1=2, r2=0, logrd=0.5*np.log(241),
            split={2: [(1,1)]*2, 3: [(1,1)]*2, 5: [(1,1)]*2, 7: [(1,2)], 11: [(1,2)], 13: [(1,2)], 17: [(1,2)],
                   19: [(1,2)], 23: [(1,2)], 29: [(1,1)]*2, 31: [(1,2)], 37: [(1,2)], 41: [(1,1)]*2, 43: [(1,2)], 47: [(1,1)]*2})
orig_sD = FO.sD
for x in (0.0, 0.05, 0.1, 0.2, 0.3, 0.5, 0.8):
    FO.sD = lambda t, x=x: orig_sD(t) + x     # free budget x
    d, info = bisect(f241, lo=0.035, hi=0.09)
    print(f"extra budget {x:.2f}: delta {d:.4f} t {info[0]} {compress(info[1])}", flush=True)
