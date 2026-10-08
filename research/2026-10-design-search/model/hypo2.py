import _paths  # noqa: F401
import numpy as np
from fieldopt import best_delta, compress
def mk(m, rd, sp, r2=0):
    split = {q: [(1, m)] for q in [7, 11, 13, 17, 19, 23, 29, 31]}
    split.update(sp)
    return dict(m=m, r1=m-2*r2, r2=r2, logrd=np.log(rd), split=split)
cases = {
 'a 2,3,5 split':        {2: [(1,1)]*4, 3: [(1,1)]*4, 5: [(1,1)]*4},
 'b 5 = two f=2':        {2: [(1,1)]*4, 3: [(1,1)]*4, 5: [(1,2)]*2},
 'c 5 inert':            {2: [(1,1)]*4, 3: [(1,1)]*4, 5: [(1,4)]},
 'd 3 = two f=2':        {2: [(1,1)]*4, 3: [(1,2)]*2, 5: [(1,1)]*4},
 'e 5 = 1,1,2':          {2: [(1,1)]*4, 3: [(1,1)]*4, 5: [(1,1),(1,1),(1,2)]},
 'f 3 = 1,1,2':          {2: [(1,1)]*4, 3: [(1,1),(1,1),(1,2)], 5: [(1,1)]*4},
 'g 3 = 1,1,2; 5=1,1,2': {2: [(1,1)]*4, 3: [(1,1),(1,1),(1,2)], 5: [(1,1),(1,1),(1,2)]},
 'h 5 ramified e2 x2':   {2: [(1,1)]*4, 3: [(1,1)]*4, 5: [(2,1)]*2},
 'i 3 ramified e2 x2':   {2: [(1,1)]*4, 3: [(2,1)]*2, 5: [(1,1)]*4},
}
for name, sp in cases.items():
    for rd in (40, 60):
        d, info = best_delta(mk(4, rd, sp))
        print(f"{name:24s} rd {rd}: delta {d:.4f} t {info[0]} {compress(info[1])}", flush=True)
