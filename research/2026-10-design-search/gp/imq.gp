default(parisize,"1G");
\\ imaginary quadratic k=Q(sqrt(-d)) with 2,3,5 split: class group, S-class group 2-rank, splitting of small primes
{
for(d=3,40000,
  D=-d; if(!isfundamental(D) || D%8!=1, next);
  if(kronecker(D,3)!=1 || kronecker(D,5)!=1, next);
  k=bnfinit(x^2-x+(1-D)/4,1);
  S=concat([idealprimedec(k,2),idealprimedec(k,3),idealprimedec(k,5)]);
  cyc=k.cyc;
  M=matconcat(vector(#S,i,bnfisprincipal(k,S[i],0)));
  Q=if(#cyc, matsnf(matconcat([matdiagonal(cyc),M]),4), []);
  c2=sum(i=1,#Q,(Q[i]%2==0));
  s=Str(d," rd=",precision(sqrt(d)*1.,5)," h=",k.no," cyc=",cyc," ClS=",Q," c2=",c2);
  forprime(p=7,31, s=Str(s," ",p,":",kronecker(D,p)));
  if(d<2000 || c2>0, print(s));
)
}
