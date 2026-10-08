default(parisize,"2G");
sp(K,p)={my(dec=idealprimedec(K,p)); vecsort(vector(#dec,i,[dec[i].e,dec[i].f]))}
{
outf="cubic2split.txt";
foreach([["C3",0],["S3",0],["S3",1]], gs,
  L=nflist(gs[1],[1,2*10^6],gs[2]); cnt=0;
  for(i=1,#L, P=L[i]; K=nfinit(P);
     if(#idealprimedec(K,2)!=3, next);
     cnt++;
     s=Str(gs[1]," ",gs[2]," ",K.disc," ",P);
     forprime(p=3,61, s=Str(s," ",p,":",sp(K,p)));
     write(outf,s));
  printf("# %s r2=%d: %d fields, %d with 2 split completely\n",gs[1],gs[2],#L,cnt));
}
