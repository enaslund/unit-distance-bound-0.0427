\\ real quadratic k0 with 2 split; narrow class group; for the class field B' = full narrow (or wide) Hilbert class field,
\\ report splitting of small primes and signature.
default(parisize,"2G");
{
for(D=17,30000,
  if(D%8!=1 || !isfundamental(D), next);
  hn=qfbclassno(D)*(if(quadunitnorm(D)==1,2,1)); \\ narrow class number
  if(hn<2, next);
  k=bnfinit(x^2-x-(D-1)/4,1);
  bnr=bnrinit(k,[1,[1,1]]);   \\ narrow ray class group (modulus = both infinite places)
  cyc=bnr.cyc; ho=prod(i=1,#cyc,cyc[i]);
  if(ho<2, next);
  \\ order of classes of primes above 2 (must be trivial for 2 to split completely in the narrow HCF)
  ok=1; foreach(idealprimedec(k,2),P, if(bnrisprincipal(bnr,P,0)!=0, ok=0));
  if(!ok, next);
  s=Str("D=",D," rd=",precision(sqrt(D)*1.,6)," h=",k.no," narrowcyc=",cyc);
  forprime(p=3,23, dec=idealprimedec(k,p); s=Str(s," ",p,":",vector(#dec,i,bnrisprincipal(bnr,dec[i],0)~)));
  print(s);
)
}
