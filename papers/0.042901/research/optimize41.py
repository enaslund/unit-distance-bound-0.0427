#!/usr/bin/env python3
"""Discovery optimizer for the 41-cap witness (floating search; not a certificate).

Fresh degree-3 archimedean search + six-shell (truncated where tiny) finite
optimization at the given delta, then exact interval verification of the
combined witness. Run from the repository root:
  python3 papers/0.042901/research/optimize41.py DELTA OUTDIR
The OUTDIR/shells.json and OUTDIR/arch.json combine into the certificate
witness (delta, C=0.04871285, theta_min=65535/131072, EF with 41:(2,4)).
"""
import json, sys
sys.path.insert(0, 'papers/0.04273/certificates')
sys.path.insert(0, 'papers/0.04273/research/design-model')
from fractions import Fraction as Q
from pathlib import Path
import os
os.chdir('papers/0.04273/certificates')
import env241
from model import local_logF
import numpy as np
from scipy.optimize import minimize
import importlib.util

def load(n,p):
    s=importlib.util.spec_from_file_location(n,p); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); return m

delta_str=sys.argv[1]; outdir=Path(sys.argv[2]); outdir.mkdir(parents=True,exist_ok=True)
delta=Q(delta_str); dfl=float(delta)

# archimedean fresh
# next-profile-search.py was removed from the tree on 2026-09-29. This path needs
# a copy of publication/unit-distance-lower-bound/research/ from tag
# pre-merge-2026-09-29 at papers/unit-distance-lower-bound/research/.
search=load('ps','../../unit-distance-lower-bound/research/next-profile-search.py')
calc,zero=search.setup(3,2.2,dfl,160,False)
res=minimize(calc,zero,jac=True,method='BFGS',options={'gtol':2e-10,'maxiter':1200})
row=calc(res.x,True)
print('J0',row['J0'],'bern_min',row['bernstein_min'],flush=True)
assert row['bernstein_min']>0
norm=row['bernstein'][0][0]
s_str=f"{row['gamma']:.12f}"; a_str=f"{row['a']:.16f}"
bern=[[f'{v/norm:.10f}' for v in line] for line in row['bernstein']]
bern[0][0]='1'
for i in range(4):
    for j in range(i): bern[i][j]=bern[j][i]

# shells for 2,3,5,29,41 (EF: 41=(2,4))
PRIMES={2:(8,4),3:(2,2),5:(2,2),29:(1,4),41:(2,4)}
def optimise(dfl,Q,k):
    best=(local_logF(dfl,Q,k),[1.0]+[0.0]*5)
    for scale in [0.9,1.0,1.1]:
        x0=np.log(np.array([1.0/Q**(scale*i) for i in range(1,6)]))
        r=minimize(lambda lx: -local_logF(dfl,Q,k,np.exp(lx)),x0,method='Nelder-Mead',options={'xatol':1e-12,'fatol':1e-15,'maxiter':40000})
        if -r.fun>best[0]: best=(-r.fun,[1.0]+list(np.exp(r.x)))
    return best
def rationalise(w):
    out=[Q(1)]
    for x in w[1:]:
        fr=Q(float(x)).limit_denominator(10**14)
        if fr<=0: break
        if fr>out[-1]: fr=out[-1]
        out.append(fr)
    return out
ks,profiles={},{}
for q,(e,ff) in PRIMES.items():
    Qf=float(q)**ff
    bestk=None
    for k in range(0,40):
        v,w=optimise(dfl,Qf,k)
        if bestk is None or v>bestk[0]: bestk=(v,k,w)
    v,k,w=bestk
    ks[str(q)]=k; profiles[str(q)]=[str(x) for x in rationalise(w)]
    print(q,'k',k,'logF/(ef)',v/(e*ff),flush=True)
shells={'ks':ks,'finite_profiles':profiles}
(outdir/'shells.json').write_text(json.dumps(shells,indent=1))
(outdir/'arch.json').write_text(json.dumps({'s':s_str,'a':a_str,'bernstein':bern,'J0':row['J0']},indent=1))

# margin via geom241 with patched EF
import geom241
geom241.EF={2:(8,4),3:(2,2),5:(2,2),29:(1,4),41:(2,4)}
from mpmath import mp,iv
mp.dps=80; iv.dps=80
after,fok,sok=geom241.margin(delta_str,'0.04871285',shells,s=s_str,a=a_str,bern=[[Q(v) for v in r] for r in bern])
print('delta',delta_str,'fourier',fok,'slope',sok)
from profile_certificate import interval_strings
print('margin_after',interval_strings(after))
