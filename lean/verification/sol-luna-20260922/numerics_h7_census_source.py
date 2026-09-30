#!/usr/bin/env python3
"""Exact retained-state census for the new dyadic tower and its H7 field.

The C++ sieve is derived from the frozen, independently checked H6 sieve;
only its actual norm fields, retained predicates, and protocol are changed.
The prefix audit instead uses PARI primes and ordinary Python residue rings.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import isqrt,prod
import argparse,hashlib,importlib.util,json,subprocess,sys
HERE=Path(__file__).resolve().parent;PUB=HERE.parents[1]
FROZEN=PUB/'six-dimensional-lower-bound/research'
OCTIC=HERE/'octic-arithmetic-h6-1555.json'
sys.path.insert(0,str(PUB/'five-prime-lower-bound/certificates'))
import five_descent as d
from exact_group import addbasis
from flint import arb,ctx
from hecke_afe import enclosure
from hecke_coefficients import sqrtmod
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
structure=load('census_dyadic_structure',FROZEN/'next-structure-dyadic.py')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rat(q):
    q=Q(q);return arb(q.numerator)/q.denominator

def arithmetic():
    G=structure.generate();D=d.dual_basis();words=d.words();H4=[133,2186,13,40]
    fields=[*d.FIELDS,(-6,385,1,8),(-14,65,3,2),(-11,5,3,1),(-1,13,-2,3)]
    roots=[*d.NORM_ROOTS,1,1,2,1]
    assert len(fields)==len(roots)==17
    forms=[d.cup(d.cmask(A),d.cmask(B)) for A,B,x,y in fields]
    def word(mask):
        q=d.xor(D[i] for i in d.bits(mask));w,extra=words[q]
        return w^((1<<13)|(1<<14) if extra else 0)
    retained=[]
    for mask in range(4096):
        q=d.xor(D[i] for i in d.bits(mask))
        if all(not (r&d.seven_form(q)).bit_count()%2 for r in G['relations']):retained.append(mask)
    assert len(retained)==1024
    basis={};old_basis=[]
    for mask in sorted(retained,key=lambda m:(word(m).bit_count(),word(m),m)):
        if addbasis(basis,mask):old_basis.append(mask)
    assert len(old_basis)==10
    octic=next(s for s in json.loads(OCTIC.read_text())['sectors'] if s['mask']==1555)
    assert octic['extended_catalog_field13']=={'A':-11,'B':5,'x':3,'y':1,'z':2}
    extra=octic['extra_old_catalog'];assert extra in ([],[1,4])
    added=sum(1<<(15 if j==13 else j) for j in octic['catalog_word'])
    if extra:added^=(1<<13)|(1<<14)
    assert added==39508
    completed=[word(m) for m in H4]+[1<<15,added,132]
    union=[word(m) for m in old_basis]+[1<<15,1<<16]
    def form(w):return d.xor(forms[i] for i in d.bits(w))
    assert form(added)==int(octic['original_form_hex'],16)
    assert form(132)==0x2408e1200
    U=[form(w) for w in union];UU={}
    for q in U:
        assert all(not (r&d.seven_form(q)).bit_count()%2 for r in G['relations'])
        addbasis(UU,q)
    assert len(UU)==12
    assert d.span(U)==d.span(int(q,16) for q in G['dual_basis_eight_hex'])
    assert len(d.span(form(w) for w in completed))==128
    # Word26 is an exact square: alpha1*alpha3*alpha4=-728=(2sqrt(-182))².
    raw_union=d.span(union)
    assert all(w in raw_union or (w^26) in raw_union for w in completed)
    for (A,B,x,y),z in zip(fields,roots):assert x*x-A*y*y==B*z*z
    return {'fields':[list(f)+[z] for f,z in zip(fields,roots)],'completed_linear_masks':completed,
        'union_linear_masks':union,'predicate_order':completed+union,
        'completed_forms_hex':[hex(form(w)) for w in completed],
        'union_forms_hex':[hex(q) for q in U],'common_old_basis_masks':old_basis,
        'full_central_dimension':12,'completed_central_dimension':7,
        'new_generator_raw_word':132,'new_generator_mask':274,'new_octic_mask':1555,'new_raw_word':added,'octic_arithmetic_sha256':sha(OCTIC)}

def build():
    a=arithmetic();old=PUB/'five-prime-lower-bound/research/nonpositive-census.cpp';src=old.read_text()
    start=src.index('const std::array<Field,15>');end=src.index('// All callers',start)
    src=src[:start]+'const std::array<Field,17> fields={{'+','.join('{'+','.join(map(str,r[:4]))+'}' for r in a['fields'])+'}};\n'+\
        'const std::array<S,17> norm_square_roots={{'+','.join(str(r[4]) for r in a['fields'])+'}};\n'+\
        'const std::array<unsigned,19> predicates={{'+','.join(map(str,a['predicate_order']))+'}};\n\n'+src[end:]
    src=src.replace('std::array<U,20> hits','std::array<U,19> hits')
    src=src.replace('std::array<int,15> bits','std::array<int,17> bits').replace('std::array<U,15> roots','std::array<U,17> roots')
    start=src.index('            // The first six forms');end=src.index('            for(unsigned stage',start)
    src=src[:start]+'            // Seven completed predicates followed by a basis of all12 retained forms.\n'+src[end:]
    src=src.replace('i<15;++i','i<17;++i').replace('completed=stage<6','completed=stage<7')
    src=src.replace('+total.hits[5]','+total.hits[5]+total.hits[6]')
    src=src.replace('FIVE_PRIME_H6_CENSUS_V1','NONABELIAN_DYADIC_H7_CENSUS_V1')
    start=src.index('    std::cout<<"space_index');end=src.index('    std::cout<<"predicate_first_hits',start)
    literal=''.join(key+' '+ ' '.join(map(str,a[key]))+'\\n' for key in ('completed_linear_masks','union_linear_masks','predicate_order'))
    src=src[:start]+'    std::cout<<"'+literal+'";\n'+src[end:]
    src='// Generated by h7-census.py from frozen H6 source '+sha(old)+'\n'+src
    (HERE/'h7-census.cpp').write_text(src)
    a['template_sha256']=sha(old);a['generated_cpp_sha256']=sha(HERE/'h7-census.cpp')
    (HERE/'h7-census-arithmetic.json').write_text(json.dumps(a,indent=2)+'\n')
    print('PASS full12D and completedH7 arithmetic',a['completed_linear_masks'])

def parse(path):
    lines=Path(path).read_text().splitlines();assert lines[0]=='NONABELIAN_DYADIC_H7_CENSUS_V1' and lines[-1]=='END'
    out={'fields':[],'bins':[]}
    for line in lines[1:-1]:
        key,*raw=line.split();values=list(map(int,raw))
        if key=='field':assert values[0]==len(out['fields']);out['fields'].append(values[1:])
        elif key=='bin':out['bins'].append(values)
        else:assert key not in out;out[key]=values[0] if len(values)==1 else values
    a=arithmetic()
    for key in ('fields','completed_linear_masks','union_linear_masks','predicate_order'):assert out[key]==a[key]
    assert out['modulus']==120120 and out['residue_classes']==180 and out['denominator']==10**30
    return out,a

def certify(path,eps=Q(1,6000)):
    eps=Q(eps);assert 0<eps<Q(1,100)
    ctx.prec=256;data,a=parse(path);limit=data['limit'];den=data['denominator'];allowed={};lo=13
    while lo<limit:
        hi=min(limit,max(lo+1,(1001*lo+999)//1000));allowed[lo]=hi;lo=hi
    lower=arb(0);upper=arb(0);counts=[0,0,0];previous=13
    for lo,hi,n,u,n0,u0,n1,u1 in data['bins']:
        assert previous<=lo and allowed[lo]==hi;previous=hi
        assert n0+n1==n and u0+u1==u and 0<n<=hi-lo
        for j,(nn,uu) in enumerate(((n,u),(n0,u0),(n1,u1))):
            assert 0<=nn<=n and nn*(den//hi)<=uu<=nn*(den//(lo+1));counts[j]+=nn
        lower+=arb(hi)**(-rat(eps))*rat(Q(u1,den))
        upper+=arb(lo)**(-rat(eps))*rat(Q(u1+n1,den))*rat(Q(lo*lo,lo*lo-1))
    assert counts==[data['full_count'],data['completed_count'],data['complement_count']]
    value=lower.lower().union(upper.upper())
    return {'status':'PASS outward genus-split H7 complement census; exact sieve and independent prefix are separate checked inputs',
        'sigma':str(1+eps),'cutoff':limit,'complement':enclosure(value),
        'counts':counts,'genus_split_count':data['genus_split_count'],'arithmetic':a,
        'source_sha256':{str(p.resolve().relative_to(PUB)):sha(p) for p in (Path(path),Path(__file__),HERE/'h7-census.cpp',OCTIC,FROZEN/'next-structure-dyadic.py')}}

def prefix(path):
    data,a=parse(path);limit=data['limit'];assert limit<=10**7
    run=subprocess.run(['gp','-fq','-s','100000000'],input=f'print(primes([14,{limit}]));quit\n',text=True,capture_output=True,check=True)
    assert not run.stderr.strip(),run.stderr;ps=json.loads(run.stdout)
    bins={};lo=13
    while lo<limit:hi=min(limit,max(lo+1,(1001*lo+999)//1000));bins[lo]=[hi,0,0,0,0,0,0];lo=hi
    intervals=list(bins);bi=0;genus=0;hits=[0]*19;count=first=0
    allowed={r for r in range(1,120120,8) if all(pow(r%p,(p-1)//2,p)==1 for p in (3,5,7,11,13))};assert len(allowed)==180
    for p in ps:
        if p%120120 not in allowed:continue
        genus+=1;state=0
        for i,(A,B,x,y,z) in enumerate(a['fields']):
            r=sqrtmod(A%p,p);assert r*r%p==A%p
            b=(x+y*r)%p;val=pow(b,(p-1)//2,p);assert val in (1,p-1)
            assert pow((x-y*r)%p,(p-1)//2,p)==val
            if val==p-1:state|=1<<i
        stage=next((j for j,w in enumerate(a['predicate_order']) if (w&state).bit_count()%2),None)
        if stage is None:continue
        hits[stage]+=1;count+=1;done=stage<7;first+=done
        while p>bins[intervals[bi]][0]:bi+=1
        row=bins[intervals[bi]];u=10**30//p;row[1]+=1;row[2]+=u;row[3 if done else 5]+=1;row[4 if done else 6]+=u
    expected=[[lo,*row] for lo,row in bins.items() if row[1]]
    assert expected==data['bins'] and hits==data['predicate_first_hits']
    assert (genus,count,first)==(data['genus_split_count'],data['full_count'],data['completed_count'])
    return {'status':'PASS independent PARI primes and ordinary finite-field arithmetic; every bin/count/reciprocal matches',
        'limit':limit,'genus_split_count':genus,'full_count':count,'completed_count':first,
        'complement_count':count-first,'source_sha256':{str(p.resolve().relative_to(PUB)):sha(p) for p in (Path(__file__),Path(path))}}

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions required')
    ap=argparse.ArgumentParser();ap.add_argument('--build',action='store_true');ap.add_argument('--prefix',action='store_true');ap.add_argument('path',nargs='?',type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--sigma',type=Q,default=Q(6001,6000));args=ap.parse_args()
    if args.build:build()
    else:
        result=prefix(args.path) if args.prefix else certify(args.path,args.sigma-1)
        (args.output or args.path.with_suffix('.json')).write_text(json.dumps(result,indent=2)+'\n')
        print(result['status'],result.get('complement',result.get('complement_count')))
