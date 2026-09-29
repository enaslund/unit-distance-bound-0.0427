"""Optimise six-shell finite windows for the Q(sqrt 241) design and rationalise them."""
import json
import sys
from fractions import Fraction
import numpy as np
from scipy.optimize import minimize
import env241  # noqa: F401
from model import local_logF

PRIMES = {2: (8, 4), 3: (2, 2), 5: (2, 2), 29: (1, 4), 7: (1, 8)}


def optimise(delta, Q, k):
    best = (local_logF(delta, Q, k), [1.0] + [0.0] * 5)
    for scale in [0.9, 1.0, 1.1]:
        x0 = np.log(np.array([1.0 / Q**(scale * i) for i in range(1, 6)]))
        f = lambda lx: -local_logF(delta, Q, k, np.exp(lx))
        r = minimize(f, x0, method="Nelder-Mead", options={"xatol": 1e-12, "fatol": 1e-15, "maxiter": 40000})
        if -r.fun > best[0]:
            best = (-r.fun, [1.0] + list(np.exp(r.x)))
    return best


def rationalise(w):
    out = [Fraction(1)]
    for x in w[1:]:
        fr = Fraction(float(x)).limit_denominator(10**14)
        if fr > out[-1]:
            fr = out[-1]
        out.append(fr)
    return out


if __name__ == "__main__":
    delta = float(Fraction(sys.argv[1]))
    ks, profiles = {}, {}
    for q, (e, f) in PRIMES.items():
        Q = float(q)**f
        bestk = None
        for k in range(0, 40):
            v, w = optimise(delta, Q, k)
            if bestk is None or v > bestk[0]:
                bestk = (v, k, w)
        v, k, w = bestk
        ks[str(q)] = k
        profiles[str(q)] = [str(x) for x in rationalise(w)]
        print(q, e, f, "k", k, "logF/(ef)", v / (e * f), flush=True)
    json.dump({"ks": ks, "finite_profiles": profiles}, open(f"shells241_{sys.argv[1].replace('/', '_')}.json", "w"), indent=1)
