default(parisize,"2G");
splits(P,p)={my(K=nfinit([P,[p]]),dec=idealprimedec(K,p)); [#dec, vector(#dec,i,[dec[i].e,dec[i].f])]}
{
for(gi=1,5, G=["C4","V4","D4","A4","S4"][gi];
  t0=getabstime();
  L=nflist(G,[1,4*10^6],0);
  cnt=0;
  for(i=1,#L, P=L[i];
     ok=1; for(j=1,3, p=[2,3,5][j]; s=splits(P,p); if(s[1]!=4, ok=0; break));
     if(ok, cnt++; D=nfdisc(P); printf("%s disc=%d rd=%.2f P=%s\n",G,D,D^(1/4),P)));
  printf("# %s: %d fields up to 4e6, %d with 2,3,5 split completely (%d ms)\n",G,#L,cnt,getabstime()-t0);
)
}
