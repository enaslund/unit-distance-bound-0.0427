import sys, numpy as np
from design import c1, dyadic, PD, pt, arch, C_SLACK, LOG2
from optimize import options, PR
from util import L
import fastopt

def sD(t): return t*t*(1-t**7/PD(t))

def solve_amort(delta,t,m,ell_extra,primes):
    base_extra = -(1-sD(t))*(1-1/m)
    M,ch = fastopt.solve_fast(delta,t,0.0,extra_base=base_extra,primes=primes)
    return M - (0.5-delta)*ell_extra, ch

def best(m,ell_extra,primes,ts=np.arange(0.18,0.40,0.005)):
    lo,hi=0.03,0.06; info=None
    for _ in range(16):
        mid=(lo+hi)/2; bM=-np.inf; bi=None
        for t in ts:
            M,ch=solve_amort(mid,t,m,ell_extra,primes)
            if M>bM: bM,bi=M,(t,ch)
        if bM>0: lo=mid; info=bi
        else: hi=mid
    return lo,info

if __name__=="__main__":
    pass
