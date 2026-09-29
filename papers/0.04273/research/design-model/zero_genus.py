import numpy as np
from util import isprime, L
from model import best_local, p_of
d=83647/2000000
gens=[-1,2,3,5,7,11,13]
res=[]
for q in range(17,20000):
    if not isprime(q): continue
    if all(L(a%q,q)==1 for a in gens):
        res.append(q)
print(res[:20])
t=11/34
for q in res[:12]:
    v,k,_=best_local(d,float(q),shells=True)
    gain=v+np.log(1-1/q)
    print(q,"k",k,"gain per degree",round(gain,4),"cost t^2",round(t*t,4),"ratio",round(gain/(t*t),2))
