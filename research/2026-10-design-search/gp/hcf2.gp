default(parisize,"2G");
\\ output: D h hnarrow cycnarrow | for each p<=47: list of [e_B', f_B'] for primes of B' (narrow HCF) above p, with multiplicities
{
for(D=17,20000,
  if(D%8!=1 || !isfundamental(D), next);
  if(qfbclassno(D)*(if(quadunitnorm(D)==1,2,1))<2, next);
  k=bnfinit(x^2-x-(D-1)/4,1);
  bnr=bnrinit(k,[1,[1,1]]); cyc=bnr.cyc; H=prod(i=1,#cyc,cyc[i]);
  if(H<2, next);
  ok=1; foreach(idealprimedec(k,2),P, if(bnrisprincipal(bnr,P,0)!=0, ok=0)); if(!ok, next);
  hw=k.no;
  s=Str(D," ",hw," ",H);
  forprime(p=3,47,
    dec=idealprimedec(k,p); out=List();
    foreach(dec,P, c=bnrisprincipal(bnr,P,0); o=1; for(i=1,#cyc, o=lcm(o, cyc[i]/gcd(cyc[i],c[i])));
       listput(out,[P.e, P.f*o, H/o]));
    s=Str(s," ",p,":",Vec(out)));
  print(s);
)
}
