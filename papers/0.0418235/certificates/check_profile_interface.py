#!/usr/bin/env python3
"""Optional independent profile diagnostic; this is not an interval certificate.

No output is produced by default. With --output PATH, write a diagnostic JSON
receipt. --verbose prints it. mpmath at 90 decimal digits supplies numerical
cross-checks; it does not prove directed enclosures. The interval certificate
is certificates/reproduce.py. This script does not import that verifier.
"""
from pathlib import Path
import argparse
import json,re,math
from fractions import Fraction
import mpmath as m
m.mp.dps=90
assert __debug__, "Run without -O: assertions implement diagnostic checks"
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path)
parser.add_argument('--verbose',action='store_true')
args=parser.parse_args()
paper=Path(__file__).resolve().parents[1]
w=json.loads((paper/'certificates/witness.json').read_text())
# Check the typeset witness independently as exact rational numbers.
text=(paper/'sections/finite-witness.tex').read_text()
parts=text.split(r'\begin{table}')
weight_count=0
for section,indices in [(1,(1,2,3)),(2,(4,5))]:
 for row in parts[section].splitlines():
  match=re.match(r'^(\d+) & (.+)\\\\$',row)
  if match is None: continue
  prime=match[1]
  fields=match[2].split(' & ')
  assert len(fields)==len(indices)
  for index,field in zip(indices,fields):
   term=re.fullmatch(r'\$([\d.]+)\\cdot10\^\{(-?\d+)\}\$',field)
   assert term,(prime,field)
   assert Fraction(term[1])*Fraction(10)**int(term[2])==Fraction(w['finite_profiles'][prime][index])
   weight_count+=1
assert weight_count==55
profile=(paper/'sections/profiles.tex').read_text()
matrix_text=profile.split(r'B=\begin{pmatrix}')[1].split(r'\end{pmatrix}')[0]
matrix=[[Fraction(x.strip()) for x in row.split('&')] for row in matrix_text.split(r'\\')]
assert matrix==[[Fraction(x) for x in row] for row in w['bernstein']]
assert Fraction(w['delta'])==Fraction('0.0418235')
assert Fraction(w['analytic_ceiling'])==Fraction('0.042161819')
assert Fraction(w['theta_min'])==Fraction(4095,8192)
assert all(Fraction(x)>0 for row in w['finite_profiles'].values() for x in row)
assert all(all(Fraction(x)>=Fraction(y) for x,y in zip(row,row[1:])) for row in w['finite_profiles'].values())
def q(s):
 f=Fraction(s); return m.mpf(f.numerator)/f.denominator
B=[[Fraction(x) for x in row] for row in w['bernstein']]
s,a,delta=map(q,[w['s'],w['a'],w['delta']]); p=2/(1+delta); beta=s*p
D=[[Fraction(0) for j in range(4)] for i in range(4)]
for i in range(4):
 for j in range(4):
  for h in range(4-i):
   for k in range(4-j):
    D[i+h][j+k]+=B[i][j]*math.comb(3,i)*math.comb(3,j)*math.comb(3-i,h)*math.comb(3-j,k)*(-1)**(h+k)
z0=a*a/16
Z=m.mpf(0); loss=m.mpf(0)
for i in range(4):
 for j in range(4):
  for k in range(4):
   for l in range(4):
    coeff=q(D[i][j]*D[k][l]); A=2*s+i+k-1; BB=2*s+j+l-1
    assert A*BB*z0<1
    assert 2*m.log(4/a)>=m.harmonic(m.ceil(A)-1)+m.harmonic(m.ceil(BB)-1)
    if coeff<0: loss+=-coeff/(A*BB)*(A*BB*z0)**2/(1-A*BB*z0)*m.log(4/a)
    for n in (0,1):
     K1=m.rf(s+i,n)*m.rf(s+k,n)/(m.factorial(n)*m.rf(A+n,n+1))
     K2=m.rf(s+j,n)*m.rf(s+l,n)/(m.factorial(n)*m.rf(BB+n,n+1))
     C=m.log(1/a)+m.digamma(n+1)-(m.digamma(A+n)+m.digamma(BB+n))/2
     C-=(m.digamma(s+i+n)+m.digamma(s+k+n)+m.digamma(s+j+n)+m.digamma(s+l+n))/2
     C+=m.digamma(A+2*n+1)+m.digamma(BB+2*n+1)
     Z+=coeff*a**(2*n)*K1*K2*C
Z-=loss
assert m.mpf('348.4186894704059951')<Z<m.mpf('348.4186894704059952')
finite=m.mpf(0);H=m.mpf(0)
evals={2:8,3:2,5:2,7:2,11:2,13:2}; fvals={2:4,3:2,5:2}
for rstr,weights in w['finite_profiles'].items():
 r=int(rstr); e=evals.get(r,1);f=fvals.get(r,4);Q=r**f;k=w['ks'][rstr]; weights=list(map(q,weights))
 masses=[1]+[Q**i-Q**(i-1) for i in range(1,6)]
 aa=sum(v*x**p for v,x in zip(masses,weights)); bb=sum(v*x*x for v,x in zip(masses,weights))
 rr=m.mpf(0)
 for i in range(6):
  for j in range(6):
   dij=masses[min(i,j)] if i!=j else (i*masses[i]-Q**(i-1) if i else 0)
   rr+=dij*weights[i]*weights[j]
 finite+=(-delta*k*m.log(Q)+m.log((k+1)*bb*bb+2*bb*rr)-2*(1+delta)*m.log(aa))/(e*f)
 H+=m.mpf(k)/e*m.log(r)
assert m.mpf('1.0335669225039939710')<finite<m.mpf('1.0335669225039939712')
# Use exactly the proved, conservatively enlarged printed mass endpoint.
massupper=m.mpf('38.9687816563247561')
JD=m.log(Z)+2*(1+delta)*m.log(beta-1)-2*delta*m.log(m.pi)+2*delta*m.log(a)-(1+delta)*m.log(massupper)
aC=2*p*delta;JC=m.log(p/2)+delta*m.log(aC/m.pi)-aC/(2*p)
ell=m.mpf(9)/4*m.log(2)+m.log(15015)/2
slope=-m.log(m.pi)-2*JC+JD; theta=q(w['theta_min'])
margin=finite-(m.mpf('.5')-delta)*ell-q(w['analytic_ceiling'])+(1-delta)*m.log(2)+(1-theta)*m.log(m.pi)+(1-2*theta)*JC+theta*JD
rho=q(w['tube_width']); om=(rho+rho*rho)/(1-rho*rho); rel=m.mpf(0)
for r in range(4):
 for t in range(4):
  if r+t==0:continue
  dx=max(abs(sum((-1)**(r-h+t-k)*math.comb(r,h)*math.comb(t,k)*B[i+h][j+k] for h in range(r+1) for k in range(t+1))) for i in range(4-r) for j in range(4-t))
  rel+=math.comb(3,r)*math.comb(3,t)*q(dx)*om**(r+t)
rel/=q(min(x for row in B for x in row));assert rel<1
logKD=-2*beta*m.log(1-rho*rho)+p*m.log(1+rel)
sigmaD=2*m.pi*rho/m.sqrt(a);mu=2*m.exp(H/2-ell)
assert logKD<m.mpf('.04916819') and sigmaD>m.mpf('1.7518755') and mu>m.mpf('26497.47')
assert min(1,sigmaD)*mu>max(m.log(2),logKD/2)+2*m.log(5)+2
assert slope>m.mpf('.6492390240')
numerical={key:m.nstr(val,75) for key,val in [('overlap_lower_expression',Z),('signed_remainder',loss),('finite',finite),('J_C',JC),('J_D_using_printed_mass_upper',JD),('slope',slope),('margin_using_printed_mass_upper',margin),('margin_after_concentration_using_printed_mass_upper',margin-4*q(w['concentration_epsilon'])),('q0',rel),('log_K_D',logKD),('sigma_D',sigmaD),('mu',mu)]}
assert margin-4*q(w['concentration_epsilon'])>0
result={
 'status':'PASS independent exact witness and high-precision profile diagnostic',
 'scope':'Exact rational comparisons check the printed weights and matrix. Independent mpmath formula evaluation cross-checks the score and Fourier hypotheses at 90 decimal digits; it is not outward-rounded and is not a substitute for certificates/reproduce.py or the proved remainders. The final diagnostic score deliberately uses the larger printed mass upper endpoint, so it is slightly below the production score based on the full interval.',
 'precision_decimal_digits':m.mp.dps,
 'exact_checks':{'printed_nontrivial_shell_weights':weight_count,'printed_Bernstein_entries':16,'weights_positive_and_nonincreasing':True,'delta_ceiling_and_signature_match':True},
 'numerical_checks':{'overlap_and_finite_sum_inside_printed_ranges':True,'all_signed_overlap_thresholds_pass':True,'Fourier_zero_free_tube_and_packing_threshold_pass':True,'positive_signature_slope':True,'positive_margin_after_concentration_with_printed_mass_upper':True},
 'numerical_results':numerical,
}
if args.output:
 args.output.parent.mkdir(parents=True,exist_ok=True)
 args.output.write_text(json.dumps(result,indent=2)+'\n')
if args.verbose: print(json.dumps(result,indent=2))
