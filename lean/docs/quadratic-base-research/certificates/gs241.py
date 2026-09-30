from fractions import Fraction as Fr
def c1(t): return t*t/(1+t)
def c2(t): return 2*t-1+1/(1+t)**2
def c4(t): return t**4/((1+t)*(1+t*t))
def PD(t): return (1+t)**3*(1+t*t)**2
def dD(t): return 3*t-1+1/PD(t)
def sD(t): return t*t*(1-t**7/PD(t))
def P(t, caps=3):
    return 1-8*t + 2*c1(t) + 4*c2(t) + 2*dD(t) - sD(t) + caps*c4(t)
best=None
for den in range(10,200):
    for num in range(1,den):
        t=Fr(num,den)
        if not (Fr(1,5)<t<Fr(2,5)): continue
        v=P(t)
        if best is None or v<best[0]: best=(v,t)
v,t=best
print("min over small rationals: t =",t," P_B(t) =",v," ~",float(v))
for caps in [2,3,4,5,6]:
    vv=min(P(Fr(k,1000),caps) for k in range(200,400))
    print("caps",caps,"min P ~",float(vv))
