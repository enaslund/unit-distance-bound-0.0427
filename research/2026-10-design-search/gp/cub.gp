default(parisize,"2G");
sp(K,p)={my(dec=idealprimedec(K,p)); vecsort(vector(#dec,i,[dec[i].e,dec[i].f]))}
{
L=nflist("S3",[1,2*10^6],1); cnt=0;
for(i=1,#L, P=L[i]; K=nfinit(P);
  ok=1; for(j=1,3, p=[2,3,5][j]; if(#idealprimedec(K,p)!=3, ok=0; break));
  if(ok, cnt++; s=Str("disc=",K.disc," rd=",precision(abs(K.disc)^(1/3)*1.,10)," P=",P," h=",bnfinit(P).no);
     forprime(p=7,47, s=Str(s," ",p,":",sp(K,p))); print(s); if(cnt>=25, break)));
print("# complex cubics up to 2e6: ",#L,", with 2,3,5 split completely: ",cnt);
}
