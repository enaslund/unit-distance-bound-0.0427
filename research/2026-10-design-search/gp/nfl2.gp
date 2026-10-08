default(parisize,"4G");
\\ splitting type of p: vector of [e,f]
sp(K,p)={my(dec=idealprimedec(K,p)); vecsort(vector(#dec,i,[dec[i].e,dec[i].f]))}
{
X=10^7;
for(gi=1,5, G=["C4","V4","D4","A4","S4"][gi];
  t0=getabstime();
  L=nflist(G,[1,X],0);
  cnt=0;
  for(i=1,#L, P=L[i];
     \\ quick filter: 2,3,5 must split completely: polynomial-free test via nfinit
     K=nfinit(P);
     ok=1; for(j=1,3, p=[2,3,5][j]; if(#idealprimedec(K,p)!=4, ok=0; break));
     if(ok, cnt++; D=K.disc; printf("%s disc=%d rd=%.2f P=%s 7:%s 11:%s 13:%s\n",G,D,D^(1/4),P,sp(K,7),sp(K,11),sp(K,13))));
  printf("# %s: %d fields up to %g, %d with 2,3,5 split completely (%d s)\n",G,#L,X,cnt,(getabstime()-t0)\1000);
)
}
