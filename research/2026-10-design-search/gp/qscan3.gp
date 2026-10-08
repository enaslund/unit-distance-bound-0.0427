{
cnt=0; cnth=0;
for(D=2,200000,
  if(D%8!=1 || !isfundamental(D), next);
  if(kronecker(D,3)!=1 || kronecker(D,5)!=1, next);
  cnt++;
  h=qfbclassno(D); if(h<3, next);
  cnth++;
  bnf=bnfinit(x^2-x-(D-1)/4,1);
  S=concat([idealprimedec(bnf,2),idealprimedec(bnf,3),idealprimedec(bnf,5)]);
  v=vector(#S,i,bnfisprincipal(bnf,S[i],0));
  M=matconcat(v); \\ columns = classes
  cyc=bnf.cyc;
  \\ order of quotient Cl/<S>: use matsnf of [diag(cyc) | M]
  Q=matsnf(matconcat([matdiagonal(cyc),M]),4);
  o=prod(i=1,#Q,Q[i]);
  if(o>=2, printf("%7d rd=%.1f h=%d cyc=%s ClS_order=%d ClS=%s narrow=%d\n",D,sqrt(D),bnf.no,cyc,o,Q,bnfnarrow(bnf)[1]));
);
print("count ",cnt," with h>=3: ",cnth);
}
