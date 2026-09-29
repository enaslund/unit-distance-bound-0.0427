from util import isprime, L
A=[-1,2,3,5,7,11,13]
def vec(p):
    v=0
    for i,a in enumerate(A):
        if a==p: continue
        if L(a%p,p)==-1: v|=1<<i
    return v
# known involutions (vector -> description)
known={1:'c',2:'x(dyadic inertia)',53:'y(dyadic inertia)',55:'xy',4:'tau3',8:'tau5',16:'tau7',32:'tau11',64:'tau13',43:'phi3',86:'phi5',47:'tau3phi3',94:'tau5phi5'}
print("Frobenius vectors of ramified:",{p:vec(p) for p in [3,5,7,11,13]})
hits=[]
for p in range(17,2000):
    if isprime(p):
        v=vec(p)
        if v in known: hits.append((p,v,known[v]))
print(hits)
from collections import defaultdict
g=defaultdict(list)
for p in range(17,400):
    if isprime(p): g[vec(p)].append(p)
print({v:ps for v,ps in g.items() if len(ps)>=2 and ps[0]<120})
