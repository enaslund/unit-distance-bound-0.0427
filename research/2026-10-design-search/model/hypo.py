import _paths  # noqa: F401
import numpy as np
from fieldopt import best_delta, compress
def field(m, rd, extra=None, r2=0):
    r1 = m - 2*r2
    split = {2: [(1,1)]*m, 3: [(1,1)]*m, 5: [(1,1)]*m}
    # other primes: generic: one prime of degree m (inert-ish) -> useless; give them as (1,m)
    for q in [7, 11, 13, 17, 19, 23, 29, 31]:
        split[q] = [(1, m)]
    if extra: split.update(extra)
    return dict(m=m, r1=r1, r2=r2, logrd=np.log(rd), split=split)
for m in (4, 6, 8):
    for rd in (40, 60, 80, 100, 130):
        d, info = best_delta(field(m, rd))
        print("m", m, "rd", rd, "delta", round(d, 4), info[0], compress(info[1]), flush=True)
