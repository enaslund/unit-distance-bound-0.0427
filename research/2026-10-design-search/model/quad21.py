"""quadbase with the (2,1) option for split ramified primes and inert ramified primes."""
import _paths  # noqa: F401
import sys
import numpy as np
import quadbase
from design import c1, dyadic, block, uncapped, pt, LOG2
from util import L

def opts_split(delta, t, q):
    o = quadbase.opts_split.__wrapped__(delta, t, q) if hasattr(quadbase.opts_split, '__wrapped__') else ORIG_SPLIT(delta, t, q)
    rdc = -(0.5 - delta) * 0.5 * np.log(q)
    if q <= 61:
        o.append((-t + 2*t - 1 + 1/(1+t), rdc + pt(delta, q, 2, 1), "R:1"))
    return o

ORIG_SPLIT = quadbase.opts_split
quadbase.opts_split = opts_split

if __name__ == "__main__":
    for D in [int(x) for x in sys.argv[1:]]:
        d, info = quadbase.best_delta(D, hi=0.09)
        print("D", D, "delta", round(d, 6), "t", round(info[0], 4), info[1], flush=True)
