import _paths  # noqa: F401
import numpy as np
from fieldopt import best_delta, compress
def mk(m, rd, r2):
    split = {2: [(1,1)]*m, 3: [(1,1)]*m, 5: [(1,1)]*m}
    for q in [7, 11, 13, 17, 19, 23, 29, 31]: split[q] = [(1, m)]
    return dict(m=m, r1=m-2*r2, r2=r2, logrd=np.log(rd), split=split)
for (m, r2) in [(4,1), (6,1), (6,2), (8,2), (8,3)]:
    for rd in (30, 45, 60, 80):
        d, info = best_delta(mk(m, rd, r2))
        print(f"m {m} r2 {r2} rd {rd}: delta {d:.4f} t {info[0]} {compress(info[1])}", flush=True)
