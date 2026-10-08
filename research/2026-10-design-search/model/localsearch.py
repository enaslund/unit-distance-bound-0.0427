"""Exact same-model local search around the Q(sqrt241) design (weighted shells, exact GS, fine t grid).
Each place of B chooses an option; P(t) = 1 - s_D(t) + sum beta_v(t) must be < 0 for some t;
margin(delta) = sum of place values + archimedean/ell constants.  Reports all designs beating the
41-swap design at delta = 0.042901, by explicit enumeration of tame/dyadic/real choices and greedy-
exact cap allocation (all caps of one type cost the same, so the best n caps are the n most profitable)."""
import _paths  # noqa: F401
import itertools, functools, numpy as np
from model import best_local, JD_gauss, JR_gauss, LOG2, LOGPI
from design import JD_IMPROVE
DELTA = 0.042901
C_SLACK = 0.0070444
@functools.lru_cache(maxsize=None)
def logF(Q):
    v, k, _ = best_local(DELTA, float(Q), kmax=60, shells=True)   # six-shell weighted
    return v + np.log(1 - 1/Q)
def val(q, e, f, frac):          # per-degree value of a prime of B with absolute type (e,f), fraction of degree
    return frac * logF(q**f) / (e*f)
def hD(t, dims=(3, 2)):
    h = 1.0
    for i, d in enumerate(dims): h *= (1 + t**(i+1))**d
    return h
def sD(t): return t*t*(1 - t**7/hD(t))
SR = LOG2 + JR_gauss(DELTA)
CX = (1-DELTA)*LOG2 + (LOGPI + JD_gauss(DELTA) + JD_IMPROVE)/2
LOGRD = 0.5*np.log(241)
# options --------------------------------------------------------------------------------------------
# dyadic: (label, ord2 Diff, jennings dims, e, f)
DY = [('D', 2.25, (3, 2), 8, 4), ('DU8', 2.25, (3, 2, 0, 1), 8, 8), ('M16', 2.25, (3, 1), 8, 2)]
# tame at a degree-1 prime above q in {3,5}: (label, beta(t), e, f, ramified?)
def tame_opts(q):
    o = [('R22', lambda t: t - 1 + 1/(1+t)**2, 2, 2, True),
         ('R24', lambda t: t - 1 + 1/((1+t)**2*(1+t*t)), 2, 4, True),
         ('R21', lambda t: t*t/(1+t), 2, 1, True),
         ('u4',  lambda t: t**4/((1+t)*(1+t*t)), 1, 4, False),
         ('u2',  lambda t: t*t/(1+t), 1, 2, False),
         ('none', lambda t: 0.0, None, None, False)]
    if q == 5:
        o.append(('R42', lambda t: t - 1 + 1/((1+t)**2*(1+t*t)), 4, 2, True))   # C4 inertia x C2 (5 = 1 mod 4)
    return o
# cap candidates: primes of B (norm, degree over Q, rational p)
SPLIT = [29, 41, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
SPLIT = [p for p in SPLIT if pow(241 % p, (p-1)//2, p) == 1]
INERT = [7, 11, 13, 17, 19, 23, 31, 37, 43]
CAPS = []
for p in SPLIT: CAPS += [(p, 1, 'a'), (p, 1, 'b')]
for p in INERT: CAPS += [(p, 2, '')]
def cap_cost(kind, t):
    return {'C4': t**4/((1+t)*(1+t*t)), 'C2': t*t/(1+t), 'C8': t**8/((1+t)*(1+t*t)*(1+t**4)), 'C1': t}[kind]
def cap_val(cap, kind):
    p, fB, _ = cap
    frel = {'C4': 4, 'C2': 2, 'C8': 8, 'C1': 1}[kind]
    # fraction of degree above this prime of B: fB/2 ; absolute type (1, fB*frel)
    return val(p, 1, fB*frel, fB/2)
TS = np.arange(0.24, 0.33, 0.0025)
def evaluate():
    results = []
    tame3, tame5 = tame_opts(3), tame_opts(5)
    for dy in DY:
        for t3 in itertools.product(tame3, repeat=2):
            for t5 in itertools.product(tame5, repeat=2):
                for kill in (False, True):
                    # fixed part: value and cost (as function of t)
                    ell = 2*(0.5*dy[1]*LOG2)   # two dyadic places, each fraction 1/2
                    fixval = 2*val(2, dy[3], dy[4], 0.5)
                    for (lab, b, e, f, ram), q in [(x, 3) for x in t3] + [(x, 5) for x in t5]:
                        if lab == 'none': continue
                        if ram: ell += 0.5*0.5*np.log(q)*(1 - 1/e)*2 if e == 4 else 0.5*0.5*np.log(q)
                        fixval += val(q, e, f, 0.5)
                    arch = (CX if not kill else CX/2 + SR/2)
                    const = fixval - (0.5-DELTA)*(LOGRD + ell) - C_SLACK + arch
                    # caps: choose counts n2, n4, n8 of each type greedily from best values
                    capvals = {k: sorted(((cap_val(c, k), c) for c in CAPS), reverse=True) for k in ('C4', 'C2', 'C8', 'C1')}
                    best = None
                    for t in TS:
                        # v1 kept (beta = -t/(1+t)); v2 kept or killed (beta 0); two dyadic places
                        base = 1 - sD(t) - t/(1+t) + (0.0 if kill else -t/(1+t)) + 2*(2*t - 1 + 1/hD(t, dy[2]))
                        for (lab, b, e, f, ram) in list(t3) + list(t5):
                            base += b(t)        # beta already includes the generator credit when ramified
                        budget = -base
                        if budget <= 0: continue
                        # enumerate n1,n2,n4 (C8 caps nearly free: take all positive-valued ones)
                        for n1 in range(0, 3):
                            for n2 in range(0, 6):
                                c12 = n1*cap_cost('C1', t) + n2*cap_cost('C2', t)
                                if c12 >= budget: break
                                n4max = int((budget - c12) / cap_cost('C4', t))
                                # choose distinct caps: greedy over combined list respecting one cap per prime
                                used = set(); v = 0.0; ok = True
                                for kind, n in (('C1', n1), ('C2', n2), ('C4', n4max)):
                                    cnt = 0
                                    for cv, c in capvals[kind]:
                                        if cnt >= n or cv <= 0: break
                                        if c in used: continue
                                        used.add(c); v += cv; cnt += 1
                                total = const + v
                                if best is None or total > best[0]:
                                    best = (total, t, n1, n2, n4max, sorted(used))
                    if best:
                        results.append((best[0], dy[0], [x[0] for x in t3], [x[0] for x in t5], kill, best[1:]))
    return results
if __name__ == "__main__":
    res = evaluate()
    res.sort(key=lambda r: -r[0])
    for r in res[:8]:
        print(f"margin {r[0]:+.6f}  dyadic {r[1]}  3:{r[2]}  5:{r[3]}  kill_v2={r[4]}  t={r[5][0]:.4f} n1={r[5][1]} n2={r[5][2]} n4={r[5][3]} caps={r[5][4]}")
