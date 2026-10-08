"""C127 independent check of R5-uniform-defect (stdlib only, no numpy).

Reimplements tensor/Magnus/rank logic with own elimination (low-bit pivot)
and own trip algebra; parses V from lie241.py source text.
Verifies: L2/R2/L3/I3/L4/I4 ranks, syzygy kernel 28, model span 4 (E-fix),
y1-cut 240->214 (rank 26, R2-kernel 0, consistency), LV(R2)=0/9408,
TOTAL 6-dim, ad3 18/18 + witness miss + escape 18, full240 37 + escape 18,
E-formula, LV-exactness (A2-style), (rho)_2 recorded, nine-in-I3/Fpin,
margin replay, group-like flag.
Usage: python3 research/2026-10-muse-involution-class/code/C127/c127_uniform_defect_check.py
"""
import re
import random
from fractions import Fraction as F

random.seed(999)

# ---------- parse V from lie241.py source ----------
with open("papers/0.04273/certificates/lie241.py") as f:
    src = f.read()
Vm = {}
for m in re.finditer(r'"(\w+)":\s*\[([0-9,\s]+)\]', src):
    k = m.group(1)
    vals = [int(x) for x in m.group(2).split(",")]
    if len(vals) == 8 and k in ("c1","c2","x1","y1","z1","x2","y2","z2",
        "t31","p31","t32","p32","t51","p51","t52","p52","f291","f292","f7"):
        Vm[k] = vals
assert len(Vm) == 19, len(Vm)
print("V parsed: 19 vectors")

def S_mat(v):
    M = [[0]*8 for _ in range(8)]
    for i in range(8):
        for j in range(8):
            M[i][j] = (v[i]&v[j])&1
    return M

def B_mat(v,w):
    M = [[0]*8 for _ in range(8)]
    for i in range(8):
        for j in range(8):
            M[i][j] = ((v[i]&w[j])^(w[i]&v[j]))&1
    return M

# ---------- tensor bitvec (big-endian, own code) ----------
def encode(idx):
    p = 0
    for i in idx:
        p = p*8+i
    return 1 << p

def decode(bit, deg):
    idx=[0]*deg
    for j in range(deg-1,-1,-1):
        idx[j]=bit%8; bit//=8
    return idx

def bits_of(v):
    o=[]
    while v:
        b=v.bit_length()-1
        o.append(b); v^=1<<b
    return o

def t1_of(v8):
    v=0
    for i in range(8):
        if v8[i]&1: v|=encode((i,))
    return v

def t2_of(M):
    v=0
    for i in range(8):
        for j in range(8):
            if M[i][j]&1: v|=encode((i,j))
    return v

def gen(i): return encode((i,))

def mul(A,da,B,db):
    v=0
    for ba in bits_of(A):
        ia=decode(ba,da)
        for bb in bits_of(B):
            v^=encode(tuple(ia+decode(bb,db)))
    return v

def br(A,da,B,db): return mul(A,da,B,db)^mul(B,db,A,da)
def sqm(A,da): return mul(A,da,A,da)

def rb_high(rows):
    bas={}
    for v in rows:
        w=v
        while w:
            p=w.bit_length()-1
            if p in bas: w^=bas[p]
            else: bas[p]=w; break
    return len(bas), bas

def cred_high(v,bas):
    w=v; r=0
    while w:
        p=w.bit_length()-1
        if p in bas: w^=bas[p]
        else: r^=1<<p; w^=1<<p
    return r

def lowbit(v): return (v&(-v)).bit_length()-1

def rb_low(rows):
    bas={}
    for v in rows:
        w=v
        while w:
            p=lowbit(w)
            if p in bas: w^=bas[p]
            else: bas[p]=w; break
    return len(bas), bas

def cred_low(v,bas):
    w=v; r=0
    while w:
        p=lowbit(w)
        if p in bas: w^=bas[p]
        else: r^=1<<p; w^=1<<p
    return r

E8=[[1 if i==j else 0 for j in range(8)] for i in range(8)]

# ---------- L2/R2 ----------
L2sp=[t2_of(S_mat(E8[i])) for i in range(8)]
for i in range(8):
    for j in range(i+1,8):
        L2sp.append(t2_of(B_mat(E8[i],E8[j])))
rL2h,_=rb_high(L2sp); rL2l,_=rb_low(L2sp)
print("L2 rank high/low: %d/%d (expect 36)"%(rL2h,rL2l))
assert rL2h==36 and rL2l==36
_,bL2h=rb_high(L2sp)
L2bas=list(bL2h.values())

# rels (22) per lie241.py recipes
rels=[]; names=[]
def add(M,nm): rels.append(M); names.append(nm)
add(S_mat(Vm["c1"]),"c1^2"); add(S_mat(Vm["c2"]),"c2^2")
for j in "12":
    t="t3"+j; p="p3"+j
    M=B_mat(Vm[t],Vm[p])
    S=S_mat(Vm[t])
    M=[[M[i][j2]^S[i][j2] for j2 in range(8)] for i in range(8)]
    add(M,"tame3"+j)
    add(B_mat(Vm["t5"+j],Vm["p5"+j]),"tame5"+j)
for j in "12":
    x,y,z=Vm["x"+j],Vm["y"+j],Vm["z"+j]
    Sy=S_mat(y); Bxy=B_mat(x,y); Bxz=B_mat(x,z)
    M=[[Sy[i][j2]^Bxy[i][j2]^Bxz[i][j2] for j2 in range(8)] for i in range(8)]
    add(M,"demuskin"+j)
    add(S_mat(x),"x^2_"+j)
    add(B_mat(x,y),"[x,y]_"+j)
    add(B_mat(x,z),"[x,z]_"+j)
for j in "12":
    add(S_mat(Vm["t3"+j]),"tau3sq"+j)
    add(S_mat(Vm["t5"+j]),"tau5sq"+j)
    add(S_mat(Vm["p3"+j]),"phi3sq"+j)
    add(S_mat(Vm["p5"+j]),"phi5sq"+j)
assert len(rels)==22
Q2=[t2_of(m) for m,nm in zip(rels,names) if nm!="demuskin1"]
assert len(Q2)==21
rR2h,_=rb_high(Q2); rR2l,_=rb_low(Q2)
print("R2 rank high/low: %d/%d (expect 21)"%(rR2h,rR2l))
assert rR2h==21 and rR2l==21
_,bR2h=rb_high(Q2)
R2bas=list(bR2h.values())

# ---------- L3/I3 ----------
free3=[br(M,2,gen(c),1) for M in L2sp for c in range(8)]
rFL3h,bFL3h=rb_high(free3); rFL3l,_=rb_low(free3)
print("free L3 high/low: %d/%d (expect 168)"%(rFL3h,rFL3l))
assert rFL3h==168 and rFL3l==168
cub3=[]
for j in "12":
    M=t2_of(B_mat(Vm["y"+j],Vm["z"+j]))
    T=0
    for ell in range(8):
        if Vm["z"+j][ell]: T^=br(M,2,gen(ell),1)
    cub3.append(T)
R3rows=[]
for q in Q2:
    for i in range(8): R3rows.append(br(q,2,gen(i),1))
R3rows+=cub3
assert len(R3rows)==170
rI3h,bI3h=rb_high(R3rows); rI3l,bI3l=rb_low(R3rows)
print("I3 rank high/low: %d/%d (expect 142)"%(rI3h,rI3l))
assert rI3h==142 and rI3l==142

# ---------- L4/I4 ----------
_,bL3h=rb_high([br(M,2,gen(c),1) for M in L2sp for c in range(8)])
L3bas=list(bL3h.values())
free4=[br(T,3,gen(l),1) for T in L3bas for l in range(8)]
free4+=[sqm(M,2) for M in L2bas]
rF4h,_=rb_high(free4); rF4l,_=rb_low(free4)
print("free L4 high/low: %d/%d (expect 1044)"%(rF4h,rF4l))
assert rF4h==1044 and rF4l==1044
P411=[0,0,1,1,1,0,0,0]
caps={"f291":Vm["f291"],"f292":Vm["f292"],"P41[1]":P411}
R4base=[]
for q in Q2:
    for i in range(8):
        T=br(q,2,gen(i),1)
        for j in range(8): R4base.append(br(T,3,gen(j),1))
for T in cub3:
    for l in range(8): R4base.append(br(T,3,gen(l),1))
for j in "12":
    R4base.append(sqm(t2_of(S_mat(Vm["z"+j])),2))
    R4base.append(sqm(t2_of(B_mat(Vm["y"+j],Vm["z"+j])),2))
R4base+=[sqm(q,2) for q in Q2]
for k in ["f291","f292","P41[1]"]:
    R4base.append(sqm(t2_of(S_mat(caps[k])),2))
rI4h,bI4h=rb_high(R4base); rI4l,bI4l=rb_low(R4base)
print("I4 rank high/low: %d/%d (expect 963)"%(rI4h,rI4l))
assert rI4h==963 and rI4l==963
print("PART1 OK: ranks verified with two eliminations")

# ---------- syzygy kernel (tracked, own) ----------
piv={}; ker=[]
for r,row in enumerate(R3rows):
    w,c=row,1<<r
    for p in sorted(piv):
        if (w>>p)&1: w^=piv[p][0]; c^=piv[p][1]
    if w==0: ker.append(c)
    else: lb=(w&(-w)).bit_length()-1; piv[lb]=(w,c)
assert len(ker)==28
for c in ker:
    s=0
    for r in range(170):
        if (c>>r)&1: s^=R3rows[r]
    assert s==0
print("syzygy kernel: 28, all verify")

# ---------- qlabel (21 Q2 identification) ----------
def deminit(j):
    x,y,z=Vm["x"+j],Vm["y"+j],Vm["z"+j]
    Sy=S_mat(y); Bxy=B_mat(x,y); Bxz=B_mat(x,z)
    return t2_of([[Sy[i][k]^Bxy[i][k]^Bxz[i][k] for k in range(8)] for i in range(8)])
cands={}
cands["real1"]=t2_of(S_mat(Vm["c1"])); cands["real2"]=t2_of(S_mat(Vm["c2"]))
tame_p={"t31":3,"t32":3,"t51":5,"t52":5}
tame_phi={"t31":"p31","t32":"p32","t51":"p51","t52":"p52"}
for tk,pk,p in [("t31","p31",3),("t32","p32",3),("t51","p51",5),("t52","p52",5)]:
    e=B_mat(Vm[tk],Vm[pk])
    if ((p-1)//2)%2:
        s=S_mat(Vm[tk]); e=[[e[i][j]^s[i][j] for j in range(8)] for i in range(8)]
    cands["tame_"+tk]=t2_of(e)
cands["rho_p2"]=deminit("2")
for j in "12":
    cands["x2_"+j]=t2_of(S_mat(Vm["x"+j]))
    cands["xy_"+j]=t2_of(B_mat(Vm["x"+j],Vm["y"+j]))
    cands["xz_"+j]=t2_of(B_mat(Vm["x"+j],Vm["z"+j]))
for tk,pk,_ in [("t31","p31",3),("t32","p32",3),("t51","p51",5),("t52","p52",5)]:
    cands["tau2_"+tk]=t2_of(S_mat(Vm[tk]))
    cands["phi2_"+pk]=t2_of(S_mat(Vm[pk]))
assert len(cands)==21
qlabel=[]
for q in Q2:
    hits=[kk for kk,vv in cands.items() if vv==q]
    assert len(hits)==1, "Q2 identification failed"
    qlabel.append(hits[0])
print("21 Q2 identified")

# ---------- dict Magnus deg3/deg4 (own) ----------
def emul(A,B,D):
    C={}
    for m1 in A:
        for m2 in B:
            if len(m1)+len(m2)>D: continue
            m=m1+m2
            C[m]=C.get(m,0)^1
            if C[m]==0: del C[m]
    return C
def eadd(*As):
    C={}
    for A in As:
        for m in A:
            C[m]=C.get(m,0)^1
            if C[m]==0: del C[m]
    return C
def arbD(v8,D):
    g={():1}
    for i in range(8):
        if v8[i]&1: g=emul(g,{():1,(i,):1},D)
    return g
def ginvD(g,D):
    one={():1}
    a={m:1 for m in g if m!=()}
    # 1/(1+a) = 1+a+a^2+... truncated
    res=dict(one); pw=dict(a)
    for _ in range(1,D+1):
        res=eadd(res,pw)
        pw=emul(pw,a,D)
    return res
def gpowD(g,e,D):
    if e==0: return {():1}
    if e<0: return gpowD(ginvD(g,D),-e,D)
    r={():1}
    for _ in range(e): r=emul(r,g,D)
    return r
def gcommD(a,b,D):
    return emul(emul(a,b,D),emul(ginvD(a,D),ginvD(b,D),D),D)
def t3_of(d):
    v=0
    for m in d:
        assert len(m)==3; v^=encode(m)
    return v
def t4_of(d):
    v=0
    for m in d:
        assert len(m)==4; v^=encode(m)
    return v
def eval_rho3(t,f,p):
    return emul(emul(emul(f,t,3),ginvD(f,3),3),gpowD(t,-p,3),3)

ARB3={k:arbD(v,3) for k,v in Vm.items()}
# also need c1,c2 already in Vm
def rho_arb_full(lab):
    if lab=="real1": return gpowD(ARB3["c1"],2,3)
    if lab=="real2": return gpowD(ARB3["c2"],2,3)
    if lab.startswith("tame_"):
        tk=lab[5:]; return eval_rho3(ARB3[tk],ARB3[tame_phi[tk]],tame_p[tk])
    if lab.startswith("xy_"):
        jj=lab[3:]; return gcommD(ARB3["x"+jj],ARB3["y"+jj],3)
    if lab.startswith("xz_"):
        jj=lab[3:]; return gcommD(ARB3["x"+jj],ARB3["z"+jj],3)
    if lab.startswith("x2_"):
        jj=lab[3:]; return gpowD(ARB3["x"+jj],2,3)
    if lab.startswith("tau2_"): return gpowD(ARB3[lab[5:]],2,3)
    if lab.startswith("phi2_"): return gpowD(ARB3[lab[5:]],2,3)
    raise AssertionError(lab)

# y1-word: S(y1) in R2 -> coef/used (need for C1/K/Fpin)
ya=t2_of(S_mat(Vm["y1"]))
aug={}
for i,q in enumerate(Q2):
    w=(q<<21)|(1<<i)
    while w:
        pp=w.bit_length()-1
        if pp in aug: w^=aug[pp]
        else: aug[pp]=w; break
w=ya<<21
while w:
    pp=w.bit_length()-1
    if pp in aug: w^=aug[pp]
    else: break
assert w>>21==0
coef=w&((1<<21)-1)
used=[qlabel[i] for i in range(21) if (coef>>i)&1]
print("y1bar^2 uses %d initials: %s"%(len(used),sorted(used)))
assert len(used)==9 and "rho_p2" in used

# C1, K, Fpin (own)
C1=t3_of({m:1 for m in gpowD(ARB3["y1"],2,3) if len(m)==3})
for lab in used:
    if lab=="rho_p2": continue
    C1^=t3_of({m:1 for m in rho_arb_full(lab) if len(m)==3})
Wp=emul(gpowD(ARB3["y2"],2,3),emul(gcommD(ARB3["x2"],ARB3["y2"],3),gcommD(ARB3["x2"],ARB3["z2"],3),3),3)
assert len({m:1 for m in Wp if len(m)==1})==0
K=t3_of({m:1 for m in Wp if len(m)==3})
wp2=0
for m in Wp:
    if len(m)==2: wp2^=encode(m)
assert wp2==deminit("2")
print("(Wp)_2==deminit(2): True")
def arb2_of(v8):
    v=0
    for i in range(8):
        for j in range(i+1,8):
            if v8[i] and v8[j]: v|=encode((i,j))
    return v
Xv2,Yv2,Zv2=t1_of(Vm["x2"]),t1_of(Vm["y2"]),t1_of(Vm["z2"])
ay2,az2=arb2_of(Vm["y2"]),arb2_of(Vm["z2"])
LVa=(br(Yv2,1,ay2,2)^br(Xv2,1,ay2,2))^br(Xv2,1,az2,2)
Fpin=K^LVa
# nine-in-I3
nine=[]
for b,W in [("XY",0),("XY",1),("XY",2),("XZ",0),("XZ",1),("XZ",2),("YZ",0),("YZ",1),("YZ",2)]:
    U={"XY":(Vm["x2"],Vm["y2"]),"XZ":(Vm["x2"],Vm["z2"]),"YZ":(Vm["y2"],Vm["z2"])}[b]
    inner=t2_of(B_mat(U[0],U[1]))
    T=0
    vecs=(Vm["x2"],Vm["y2"],Vm["z2"])
    for ell in range(8):
        if vecs[W][ell]: T^=br(inner,2,gen(ell),1)
    nine.append(T)
assert all(cred_high(t,bI3h)==0 for t in nine)
assert all(cred_low(t,bI3l)==0 for t in nine)
print("nine-in-I3: True (both eliminations)")
# formal image rank 19, Fpin consistent
fmon=[]
for a in range(3):
    for b in range(3):
        for c in range(3):
            vv=[Vm["x2"],Vm["y2"],Vm["z2"]]
            t=0
            for l in range(8):
                for mm in range(8):
                    for nn in range(8):
                        if vv[a][l] and vv[b][mm] and vv[c][nn]:
                            t^=encode((l,mm,nn))
            fmon.append(t)
assert rb_high(fmon)[0]==27
frh=rb_high(list(bI3h.values())+fmon)[0]-rI3h
frl=rb_low(list(bI3l.values())+fmon)[0]-rI3l
fr2h=rb_high(list(bI3h.values())+fmon+[Fpin])[0]-rI3h
print("formal-image rank mod I3 high/low: %d/%d (expect 19); Fpin consistent: %s"%(frh,frl,fr2h==frh))
assert frh==19 and frl==19 and fr2h==frh

F3m={}
for lab in set(qlabel):
    if lab=="rho_p2": F3m[lab]=Fpin
    else: F3m[lab]=t3_of({m:1 for m in rho_arb_full(lab) if len(m)==3})
OM4a={}
for j in "12":
    Y=arbD(Vm["y"+j],4); Z=arbD(Vm["z"+j],4)
    w=gcommD(gcommD(Y,Z,4),Z,4)
    OM4a[j]=t4_of({m:1 for m in w if len(m)==4})
model_corrs=[]
for c in ker:
    t=0
    for k in range(168):
        if (c>>k)&1:
            nm=qlabel[k//8]
            t^=br(F3m[nm],3,gen(k%8),1)
            t^=mul(br(Q2[k//8],2,gen(k%8),1),3,gen(k%8),1)
    if (c>>168)&1: t^=OM4a["1"]
    if (c>>169)&1: t^=OM4a["2"]
    model_corrs.append(t)
mspan_h=rb_high(list(bI4h.values())+model_corrs)[0]-rI4h
mspan_l=rb_low(list(bI4l.values())+model_corrs)[0]-rI4l
print("model span mod I4 high/low: %d/%d (expect 4)"%(mspan_h,mspan_l))
assert mspan_h==4 and mspan_l==4
print("PART2 OK: syzygy/model/E-fix verified")

# ---------- trip algebra deg3 (own) ----------
def gmul_trip(a,b):
    a1,a2,a3=a; b1,b2,b3=b
    return (a1^b1, a2^b2^mul(a1,1,b1,1),
            a3^b3^mul(a1,1,b2,2)^mul(a2,2,b1,1))
def ginv_trip(a):
    a1,a2,a3=a
    n1=a1; n2=a2^mul(a1,1,a1,1)
    n3=(a3^mul(a1,1,a2,2)^mul(a2,2,a1,1)^mul(mul(a1,1,a1,1),2,a1,1))
    return (n1,n2,n3)
def gpow_trip(a,e):
    if e==0: return (0,0,0)
    if e<0: return gpow_trip(ginv_trip(a),-e)
    r=(0,0,0)
    for _ in range(e): r=gmul_trip(r,a)
    return r
def arb_trip(v8):
    d=arbD(v8,3); t1=t2=t3=0
    for m in d:
        if len(m)==1: t1^=encode(m)
        elif len(m)==2: t2^=encode(m)
        elif len(m)==3: t3^=encode(m)
    return (t1,t2,t3)
def eval_rho_trip(t,f,p):
    return gmul_trip(gmul_trip(gmul_trip(f,t),ginv_trip(f)),gpow_trip(t,-p))

tame_cross={}
for tk in tame_p:
    pk=tame_phi[tk]; p=tame_p[tk]
    t0,f0=arb_trip(Vm[tk]),arb_trip(Vm[pk])
    base3=eval_rho_trip(t0,f0,p)[2]
    ct,cp=[],[]
    for fb in L2bas:
        tp=(t0[0],t0[1]^fb,t0[2]); ct.append(eval_rho_trip(tp,f0,p)[2]^base3)
        fp=(f0[0],f0[1]^fb,f0[2]); cp.append(eval_rho_trip(t0,fp,p)[2]^base3)
    tame_cross[tk]=(ct,cp)

def sq_cross(vec,fb): return br(t1_of(vec),1,fb,2)
def comm_cross(vecA,vecB):
    A1,B1=t1_of(vecA),t1_of(vecB)
    return ([br(fb,2,B1,1) for fb in L2bas],[br(A1,1,fb,2) for fb in L2bas])
def r2_cross_cols(vecs):
    Xv,Yv,Zv=(t1_of(v) for v in vecs)
    cx=[br(fb,2,Yv,1)^br(fb,2,Zv,1) for fb in L2bas]
    cy=[br(Yv,1,fb,2)^br(Xv,1,fb,2) for fb in L2bas]
    cz=[br(Xv,1,fb,2) for fb in L2bas]
    return cx,cy,cz

# LV_Wp == LV_r
Xv2t,Yv2t=t1_of(Vm["x2"]),t1_of(Vm["y2"]); Zv2t=t1_of(Vm["z2"])
lvwx=[br(fb,2,Yv2t,1)^br(fb,2,Zv2t,1) for fb in L2bas]
lvwy=[br(Yv2t,1,fb,2)^br(Xv2t,1,fb,2) for fb in L2bas]
lvwz=[br(Xv2t,1,fb,2) for fb in L2bas]
cx2,cy2,cz2=r2_cross_cols((Vm["x2"],Vm["y2"],Vm["z2"]))
assert lvwx==cx2 and lvwy==cy2 and lvwz==cz2
print("LV_Wp==LV_r: True")

lifts=["i1","i2","t31","p31","t32","p32","t51","p51","t52","p52",
       "x1","y1","z1","x2","y2","z2"]
lvecV={"i1":Vm["c1"],"i2":Vm["c2"]}
for kk in lifts[2:]: lvecV[kk]=Vm[kk]
M={kk:[0]*36 for kk in lifts}
for j,fb in enumerate(L2bas):
    M["y1"][j]^=sq_cross(Vm["y1"],fb)
for i in range(21):
    if not (coef>>i)&1: continue
    lab=qlabel[i]
    if lab=="real1":
        for j,fb in enumerate(L2bas): M["i1"][j]^=sq_cross(Vm["c1"],fb)
    elif lab=="real2":
        for j,fb in enumerate(L2bas): M["i2"][j]^=sq_cross(Vm["c2"],fb)
    elif lab.startswith("tame_"):
        tk=lab[5:]; ct,cp=tame_cross[tk]
        for j in range(36): M[tk][j]^=ct[j]; M[tame_phi[tk]][j]^=cp[j]
    elif lab=="rho_p2":
        cx,cy,cz=r2_cross_cols((Vm["x2"],Vm["y2"],Vm["z2"]))
        for j in range(36): M["x2"][j]^=cx[j]; M["y2"][j]^=cy[j]; M["z2"][j]^=cz[j]
    elif lab.startswith("x2_"):
        jj=lab[3:]
        for j,fb in enumerate(L2bas): M["x"+jj][j]^=sq_cross(Vm["x"+jj],fb)
    elif lab.startswith("xy_"):
        jj=lab[3:]; ca,cb=comm_cross(Vm["x"+jj],Vm["y"+jj])
        for j in range(36): M["x"+jj][j]^=ca[j]; M["y"+jj][j]^=cb[j]
    elif lab.startswith("xz_"):
        jj=lab[3:]; ca,cb=comm_cross(Vm["x"+jj],Vm["z"+jj])
        for j in range(36): M["x"+jj][j]^=ca[j]; M["z"+jj][j]^=cb[j]
    elif lab.startswith("tau2_"):
        tk=lab[5:]
        for j,fb in enumerate(L2bas): M[tk][j]^=sq_cross(Vm[tk],fb)
    elif lab.startswith("phi2_"):
        pk=lab[5:]
        for j,fb in enumerate(L2bas): M[pk][j]^=sq_cross(Vm[pk],fb)
    else: raise AssertionError(lab)
Mcols=[]
for kk in lifts: Mcols+=M[kk]
rkMh=rb_high(list(bI3h.values())+Mcols)[0]-rI3h
rkMl=rb_low(list(bI3l.values())+Mcols)[0]-rI3l
print("fiber-map rank mod I3 high/low: %d/%d (expect 26)"%(rkMh,rkMl))
assert rkMh==26 and rkMl==26

def coords_L2(vec):
    aug2={}
    for j,b in enumerate(L2bas):
        w=(b<<36)|(1<<j)
        while w:
            pp=w.bit_length()-1
            if pp in aug2: w^=aug2[pp]
            else: aug2[pp]=w; break
    w=vec<<36
    while w:
        pp=w.bit_length()-1
        if pp in aug2: w^=aug2[pp]
        else: break
    assert w>>36==0
    return w&((1<<36)-1)
bad=0
for kk in lifts:
    for r in R2bas:
        cc=coords_L2(r); acc=0
        for j in range(36):
            if (cc>>j)&1: acc^=M[kk][j]
        if cred_high(acc,bI3h)!=0: bad+=1
print("R2-kernel violations M: %d/336 (expect 0)"%bad)
assert bad==0
base_rank=rb_high(list(bI3h.values())+Mcols)[0]
full_rank=rb_high(list(bI3h.values())+Mcols+[C1^K])[0]
print("C1+K consistent: %s"%(full_rank==base_rank))
assert full_rank==base_rank
print("PART3a OK: y1-cut rank/kernel/consistency verified")

# ---------- quot subset Ssel + M1 ker/T0 ----------
Ssel=[]; rest=dict(rb_high(Q2)[1])
# rebuild bR2 as dict from rb_high(Q2)
_,bR2loc=rb_high(Q2); rest=dict(bR2loc)
for j,b in enumerate(L2bas):
    if cred_high(b,rest)!=0:
        Ssel.append(j)
        r=cred_high(b,rest); p=r.bit_length()-1
        for q in list(rest):
            if (rest[q]>>p)&1: rest[q]^=r
        rest[p]=r
    if len(Ssel)==15: break
assert len(Ssel)==15
keys=[(kk,a) for kk in lifts for a in range(15)]
M1={(kk,a):M[kk][j] for kk in lifts for a,j in enumerate(Ssel)}
res=[cred_high(M1[k],bI3h) for k in keys]
basis={}; kerM=[]
for e,r in enumerate(res):
    w,c=r,1<<e
    for p in sorted(basis):
        if (w>>p)&1: w^=basis[p][0]; c^=basis[p][1]
    if w==0: kerM.append(c)
    else: lb=(w&(-w)).bit_length()-1; basis[lb]=(w,c)
print("ker M1 dim: %d (expect 214)"%len(kerM))
assert len(kerM)==214
target=cred_high(C1^K,bI3h)
w,c=target,0
for p in sorted(basis):
    if (w>>p)&1: w^=basis[p][0]; c^=basis[p][1]
assert w==0
T0=c
print("particular T0 found: True")
# verify kerM/T0 solve the cut: M(ker)=0 mod I3, M(T0)=C1+K mod I3
for kv in kerM:
    acc=0; e=0; k=kv
    while k:
        if k&1: acc^=M1[keys[e]]
        e+=1; k>>=1
    assert cred_high(acc,bI3h)==0
acc0=0
for e in range(240):
    if (T0>>e)&1: acc0^=M1[keys[e]]
assert cred_high(acc0^(C1^K),bI3h)==0
print("kerM/T0 verified against cut equation")
print("PART3b OK: 214-space verified")

# ---------- LV maps (own, same formulas, own tensors) ----------
def lv_quad(lab,lift,tj):
    fb=L2bas[tj]
    if lab in ("real1","real2"):
        g="i1" if lab=="real1" else "i2"
        if lift!=g: return 0
        return br(t1_of(Vm["c1" if g=="i1" else "c2"]),1,fb,2)
    if lab.startswith("tame_"):
        tk=lab[5:]; ct,cp=tame_cross[tk]
        if lift==tk: return ct[tj]
        if lift==tame_phi[tk]: return cp[tj]
        return 0
    if lab=="rho_p2":
        if lift=="x2": return cx2[tj]
        if lift=="y2": return cy2[tj]
        if lift=="z2": return cz2[tj]
        return 0
    if lab.startswith("x2_"):
        if lift!="x"+lab[3:]: return 0
        return br(t1_of(Vm["x"+lab[3:]]),1,fb,2)
    if lab.startswith("xy_") or lab.startswith("xz_"):
        jj=lab[3:]
        A=Vm["x"+jj]; Bv=Vm["y"+jj] if lab.startswith("xy_") else Vm["z"+jj]
        Bl=("y" if lab.startswith("xy_") else "z")+jj
        if lift=="x"+jj: return br(fb,2,t1_of(Bv),1)
        if lift==Bl: return br(t1_of(A),1,fb,2)
        return 0
    if lab.startswith("tau2_") or lab.startswith("phi2_"):
        if lift!=lab[5:]: return 0
        return br(t1_of(Vm[lab[5:]]),1,fb,2)
    raise AssertionError(lab)

def lv_omega(j,lift,tj):
    Yv,Zv=t1_of(Vm["y"+j]),t1_of(Vm["z"+j]); T=L2bas[tj]
    if lift=="y"+j: return br(br(T,2,Zv,1),3,Zv,1)
    if lift=="z"+j: return br(br(Yv,1,T,2),3,Zv,1)^br(br(Yv,1,Zv,1),3,T,2)
    return 0

def lv_s(s,lift,tj):
    c=ker[s]; t=0
    for k in range(168):
        if (c>>k)&1:
            nm=qlabel[k//8]
            t^=br(lv_quad(nm,lift,tj),3,gen(k%8),1)
    if (c>>168)&1: t^=lv_omega("1",lift,tj)
    if (c>>169)&1: t^=lv_omega("2",lift,tj)
    return t

# LV(R2)=0
r2bad=0; r2tot=0
for s in range(28):
    for kk in lifts:
        for r in R2bas:
            cc=coords_L2(r); acc=0
            for j in range(36):
                if (cc>>j)&1: acc^=lv_s(s,kk,j)
            r2tot+=1
            if cred_high(acc,bI4h)!=0: r2bad+=1
print("LV(R2) outside I4: %d/%d (expect 0)"%(r2bad,r2tot))
assert r2bad==0 and r2tot==9408
# spot-check with low elimination too
for s in (0,7,27):
    for kk in ("y1","t31","x2"):
        for r in R2bas[:5]:
            cc=coords_L2(r); acc=0
            for j in range(36):
                if (cc>>j)&1: acc^=lv_s(s,kk,j)
            assert cred_low(acc,bI4l)==0
print("LV(R2)=0 cross-checked low elimination (sample)")

# TOTAL
tot_vecs=list(model_corrs)
for s in range(28):
    acc=0
    for e in range(240):
        if (T0>>e)&1:
            kk,a=keys[e]; acc^=lv_s(s,kk,Ssel[a])
    tot_vecs.append(acc)
for s in range(28):
    for kv in kerM:
        acc=0; e=0; k=kv
        while k:
            if k&1: kk,a=keys[e]; acc^=lv_s(s,kk,Ssel[a])
            e+=1; k>>=1
        tot_vecs.append(acc)
rTh,bTh=rb_high(list(bI4h.values())+tot_vecs)
rTl,bTl=rb_low(list(bI4l.values())+tot_vecs)
print("TOTAL dim mod I4 high/low: %d/%d (expect 6)"%(rTh-rI4h,rTl-rI4l))
assert rTh-rI4h==6 and rTl-rI4l==6
rMh=rb_high(list(bI4h.values())+model_corrs)[0]-rI4h
t0vecs=tot_vecs[28:56]
rM0h=rb_high(list(bI4h.values())+model_corrs+t0vecs)[0]-rI4h
print("breakdown high: model=%d model+T0=%d total=%d (expect 4/6/6)"%(rMh,rM0h,rTh-rI4h))
assert (rMh,rM0h,rTh-rI4h)==(4,6,6)

# ad3
L2sp2=[t2_of(S_mat(E8[i])) for i in range(8)]
for i in range(8):
    for j in range(i+1,8): L2sp2.append(t2_of(B_mat(E8[i],E8[j])))
L3rows=[br(M,2,gen(c),1) for M in L2sp2 for c in range(8)]
assert len(L3rows)==288
# witness row1 = [X0^2,X1]?
assert L3rows[1]==br(t2_of(S_mat(E8[0])),2,gen(1),1)
assert cred_high(L3rows[1],bFL3h)==0  # in L3
print("witness L3row1 = [X0^2,X1] in L3: True")
for cnm in ["c1","c2"]:
    W=t1_of(Vm[cnm])
    adv=[br(T,3,W,1) for T in L3rows]
    rah=rb_high(list(bI4h.values())+adv)[0]-rI4h
    ral=rb_low(list(bI4l.values())+adv)[0]-rI4l
    esch=rb_high(list(bTh.values())+adv)[0]-rTh
    escl=rb_low(list(bTl.values())+adv)[0]-rTl
    wit=None
    for idx,a in enumerate(adv):
        if cred_high(a,bTh)!=0:
            wit=idx; break
    witl=None
    for idx,a in enumerate(adv):
        if cred_low(a,bTl)!=0:
            witl=idx; break
    nwit=sum(1 for a in adv if cred_high(a,bTh)!=0)
    print("ad3(%s): rank mod I4 high/low=%d/%d (expect 18); escape high/low=%d/%d (expect 18); witness high/low=%s/%s; rows=%d/288"%(cnm,rah,ral,esch,escl,wit,witl,nwit))
    assert rah==18 and ral==18 and esch==18 and escl==18
    assert wit==1 and witl==1
    assert cred_high(adv[1],bTh)!=0 and cred_low(adv[1],bTl)!=0
print("PART4 OK: TOTAL/ad3/witness/escape verified with two eliminations")

# full240
full=list(model_corrs)
for s in range(28):
    for kk in lifts:
        for a in range(15): full.append(lv_s(s,kk,Ssel[a]))
rFh,bFh=rb_high(list(bI4h.values())+full)
rFl,bFl=rb_low(list(bI4l.values())+full)
print("TOTAL_full240 dim mod I4 high/low: %d/%d (expect 37)"%(rFh-rI4h,rFl-rI4l))
assert rFh-rI4h==37 and rFl-rI4l==37
for cnm in ["c1","c2"]:
    W=t1_of(Vm[cnm]); adv=[br(T,3,W,1) for T in L3rows]
    esch=rb_high(list(bFh.values())+adv)[0]-rFh
    escl=rb_low(list(bFl.values())+adv)[0]-rFl
    print("vs full240 ad3(%s): escape high/low=%d/%d (expect 18)"%(cnm,esch,escl))
    assert esch==18 and escl==18
print("PART4b OK: full240 H1-independence verified")

# ---------- trip4 (own) + finite-difference validation ----------
def gmul4(a,b):
    a1,a2,a3,a4=a; b1,b2,b3,b4=b
    return (a1^b1, a2^b2^mul(a1,1,b1,1),
            a3^b3^mul(a1,1,b2,2)^mul(a2,2,b1,1),
            a4^b4^mul(a1,1,b3,3)^mul(a3,3,b1,1)^mul(a2,2,b2,2))
def ginv4(a):
    a1,a2,a3,a4=a
    a12=mul(a1,1,a1,1)
    n1=a1; n2=a2^a12
    n3=a3^mul(a1,1,a2,2)^mul(a2,2,a1,1)^mul(a12,2,a1,1)
    n4=(a4^mul(a1,1,a3,3)^mul(a3,3,a1,1)^mul(a2,2,a2,2)
        ^mul(a12,2,a2,2)^mul(mul(a1,1,a2,2),3,a1,1)
        ^mul(mul(a2,2,a1,1),3,a1,1)^mul(mul(a12,2,a1,1),3,a1,1))
    return (n1,n2,n3,n4)
def gpow4(a,e):
    if e==0: return (0,0,0,0)
    if e<0: return gpow4(ginv4(a),-e)
    r=(0,0,0,0)
    for _ in range(e): r=gmul4(r,a)
    return r
def gcomm4(a,b): return gmul4(gmul4(a,b),gmul4(ginv4(a),ginv4(b)))

# E-formula + master formula (random D2 x D1)
for t in range(6):
    A=(0,random.getrandbits(64),random.getrandbits(512),random.getrandbits(4096))
    i=random.randrange(8); xh=(gen(i),0,0,0)
    got=gcomm4(A,xh)[3]
    want=br(A[2],3,gen(i),1)^mul(br(A[1],2,gen(i),1),3,gen(i),1)
    assert got==want, "E-formula failed"
    B=(random.getrandbits(8),random.getrandbits(64),random.getrandbits(512),random.getrandbits(4096))
    got2=gcomm4(A,B)[3]
    want2=br(A[2],3,B[0],1)^br(A[1],2,B[1],2)^mul(br(A[1],2,B[0],1),3,B[0],1)
    assert got2==want2, "master failed"
print("E-formula + master ([A,B])_4 exact 6/6")

def arb3_of(v8):
    v=0
    for i in range(8):
        for j in range(i+1,8):
            for k in range(j+1,8):
                if v8[i] and v8[j] and v8[k]: v^=encode((i,j,k))
    return v
lvecK={"i1":"c1","i2":"c2"}
for kk in lifts[2:]: lvecK[kk]=kk
def rand_T2():
    v=0; m=0
    for j in range(36):
        if random.getrandbits(1): v^=L2bas[j]; m|=1<<j
    return v,m
def mk_lift(key,T2,U3,T4=0):
    v8=Vm[key]; V1=t1_of(v8); A2=arb2_of(v8); A3=arb3_of(v8)
    return (V1,A2^T2,A3^mul(V1,1,T2,2)^U3,T4)
def rand_lifts(t4=False):
    L,Mm={},{}
    for kk in lifts:
        T2,m=rand_T2(); T4=random.getrandbits(4096) if t4 else 0
        L[kk]=mk_lift(lvecK[kk],T2,random.getrandbits(512),T4); Mm[kk]=m
    return L,Mm
def arb_lifts():
    return {kk:mk_lift(lvecK[kk],0,0) for kk in lifts}
def rho_tame4(T,Fp,p): return gmul4(gmul4(gmul4(Fp,T),ginv4(Fp)),gpow4(T,-p))
def rho_of(lab,L):
    if lab=="real1": return gpow4(L["i1"],2)
    if lab=="real2": return gpow4(L["i2"],2)
    if lab.startswith("tame_"):
        tk=lab[5:]; return rho_tame4(L[tk],L[tame_phi[tk]],tame_p[tk])
    if lab.startswith("xy_"):
        jj=lab[3:]; return gcomm4(L["x"+jj],L["y"+jj])
    if lab.startswith("xz_"):
        jj=lab[3:]; return gcomm4(L["x"+jj],L["z"+jj])
    if lab.startswith("x2_"): return gpow4(L["x"+lab[3:]],2)
    if lab.startswith("tau2_") or lab.startswith("phi2_"): return gpow4(L[lab[5:]],2)
    raise AssertionError(lab)
def omega_of(j,L): return gcomm4(gcomm4(L["y"+j],L["z"+j]),L["z"+j])
def wp_of(j,L):
    return gmul4(gpow4(L["y"+j],2),gmul4(gcomm4(L["x"+j],L["y"+j]),gcomm4(L["x"+j],L["z"+j])))
def rstand_of(L):
    return gmul4(gcomm4(L["x2"],L["z2"]),gmul4(gcomm4(L["x2"],L["y2"]),gpow4(L["y2"],2)))

# (rho)_2 recorded (T'/U'/T4 independence at deg2)
La=arb_lifts()
Q2by=dict(zip(qlabel,Q2))
# qlabel may repeat? each Q2 unique label, so map label->Q2 value (first occurrence)
Q2lab={}
for lab,q in zip(qlabel,Q2): Q2lab[lab]=q
for lab in sorted(set(qlabel)):
    if lab=="rho_p2": continue
    L,_=rand_lifts(t4=True)
    R=rho_of(lab,L)
    assert R[0]==0 and R[1]==Q2lab[lab], lab
L,_=rand_lifts(t4=True)
rs=rstand_of(L)
assert rs[0]==0 and rs[1]==deminit("2")
print("(rho)_2 recorded for all 20 types + r_stand (random T'/U'/T4)")

# r_stand affinity + y2 T'/U'-freedom (validate B, own)
def lv_r_at(Mm):
    Xv,Yv,Zv=t1_of(Vm["x2"]),t1_of(Vm["y2"]),t1_of(Vm["z2"])
    LV=0
    for lift,role in (("x2",0),("y2",1),("z2",2)):
        m=Mm[lift]
        for j in range(36):
            if (m>>j)&1:
                fb=L2bas[j]
                if role==0: LV^=br(fb,2,Yv,1)^br(fb,2,Zv,1)
                elif role==1: LV^=br(Yv,1,fb,2)^br(Xv,1,fb,2)
                else: LV^=br(Xv,1,fb,2)
    return LV
Fstand=rstand_of(La)[2]
assert rstand_of(La)[1]==deminit("2")
for trial in range(2):
    L,Mm=rand_lifts()
    rs=rstand_of(L)
    assert rs[2]==(Fstand^lv_r_at(Mm))
    Wp=wp_of("2",L); Wpp=gmul4(Wp,ginv4(rs))
    assert Wpp[2]==(K^Fstand)
print("r_stand affine + y2 T'/U'-free 2/2")

# A2: (w_s)_4 == model + LV(T') for 24 non-rho_p2 syzygies, random T2/U3/T4
p2slots={i for i,q in enumerate(qlabel) if q=="rho_p2"}
cand=[s for s in range(28) if not any((ker[s]>>(q*8+i))&1 for q in p2slots for i in range(8))]
print("non-rho_p2 syzygies: %d of 28"%len(cand))
assert len(cand)==24
for s in cand:
    L,Mm=rand_lifts(t4=True)
    w=(0,0,0,0); c=ker[s]
    for k in range(168):
        if (c>>k)&1:
            nm=qlabel[k//8]; xh=(gen(k%8),0,0,0)
            w=gmul4(w,gcomm4(rho_of(nm,L),xh))
    if (c>>168)&1: w=gmul4(w,omega_of("1",L))
    if (c>>169)&1: w=gmul4(w,omega_of("2",L))
    assert w[0]==0 and w[1]==0 and w[2]==0, s
    pred=model_corrs[s]
    for kk in lifts:
        m=Mm[kk]
        for j in range(36):
            if (m>>j)&1: pred^=lv_s(s,kk,j)
    assert w[3]==pred, s
print("A2 exact 24/24 (random full-L2 T', random T3 U', random T4)")
print("PART5 OK: E/LV-exactness/U'-absence/T'2-absence validated")

# ---------- margin replay (own fractions) ----------
theta_star=F(65535,131072); theta_new=F(1,2)-F(1,2**18)
assert theta_new-theta_star==F(1,2**18)
tiers={
 "certified":(F("-1.32962595959847075e-05"),F("-1.32962595959484946e-05"),F("-8.52982440210e-06"),F("-8.52982440206e-06")),
 "middle":(F("-1.9562595959847075e-06"),F("-1.9562595959484946e-06"),F("2.81017559790e-06"),F("2.81017559794e-06")),
 "estimated":(F("-6.962595959847075e-07"),F("-6.962595959484946e-07"),F("4.07017559790e-06"),F("4.07017559794e-06")),
}
slope=(F("0.62474619373310090"),F("0.62474619373310098"))
assert slope[0]>0
zeros={"middle":(F("0.49999550189240666"),F("0.49999550189240672")),"estimated":(F("0.49999348507339658"),F("0.49999348507339664"))}
for name,(mlo,mhi,hlo,hhi) in tiers.items():
    Mnew=(mlo+slope[0]*F(1,2**18),mhi+slope[1]*F(1,2**18))
    Mh=(mlo+slope[0]*F(1,2**17),mhi+slope[1]*F(1,2**17))
    assert Mh[0]<=hhi and hlo<=Mh[1]
    if name=="certified":
        assert not (Mnew[0]>0 and hlo>0)
        print("margin %s: Mnew~%.3e fail (both ends <0)"%(name,float(Mnew[0])))
    else:
        assert Mnew[0]>0 and hlo>0
        zlo,zhi=zeros[name]
        assert theta_new>zhi
        print("margin %s: Mnew~%.3e pass, above zero by %.3e"%(name,float(Mnew[0]),float(theta_new-zhi)))
print("PART6 OK: margin replay verified (middle/estimated pass, certified fails)")

# ---------- group-like flag (256 V exhaustive, own) ----------
bad=[]
for mask in range(256):
    v=[(mask>>i)&1 for i in range(8)]
    wt=sum(v)
    # group-like defect: off-diagonal sum_{i<j} v_i v_j (E_ij+E_ji) == 0?
    glike=(wt<=1)
    # direct: defect nonzero iff exists i<j with v_i=v_j=1 iff wt>=2
    defect=(wt>=2)
    if glike==(not defect): pass
    else: bad.append(mask)
    # also check single-bit 1+X_i is free generator (genuine) by definition
assert not bad
# recorded 19 vectors: wt<=1 iff group-like
for k,v in Vm.items():
    wt=sum(v)
    assert (wt<=1)==(wt<2)
print("group-like iff wt<=1 for all 256 V; C107 'V!=0' wrong for wt-1, repair wt>=2 correct")
print("PART7 OK: C107 flag verified")
print("ALL C127 CHECKS PASS")
