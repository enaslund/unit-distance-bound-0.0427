default(parisize,"4G");
sp(K,p)={my(dec=idealprimedec(K,p)); vecsort(vector(#dec,i,[dec[i].e,dec[i].f]))}
{
X=10^7;
outf="quart2split.txt";
foreach([[["C4","V4","D4","A4","S4"],0],[["D4","S4"],1]], gs,
 foreach(gs[1], G,
  L=nflist(G,[1,X],gs[2]); cnt=0;
  for(i=1,#L, P=L[i]; K=nfinit(P);
     if(#idealprimedec(K,2)!=4, next);
     cnt++;
     s=Str(G," ",gs[2]," ",K.disc," ",P);
     forprime(p=3,61, s=Str(s," ",p,":",sp(K,p)));
     write(outf,s));
  printf("# %s r2=%d: %d fields, %d with 2 split completely\n",G,gs[2],#L,cnt)));
}
