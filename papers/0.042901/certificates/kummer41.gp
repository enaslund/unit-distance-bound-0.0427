default(parisize,"1G");
K = bnfinit(y^2 - 241, 1);
eps = K.fu[1];
P2 = idealprimedec(K,2); P3 = idealprimedec(K,3); P5 = idealprimedec(K,5);
gen(pr) = nfbasistoalg(K, bnfisprincipal(K, pr)[2]);
pis = [gen(P2[1]), gen(P2[2]), gen(P3[1]), gen(P3[2]), gen(P5[1]), gen(P5[2])];
V = concat([-1, eps], pis);   \\ same Kummer basis as kummer241.gp
hs(a, b, pr) = if (nfhilbert(K, a, b, pr) == -1, 1, 0);
vecof(a, pr) = vector(#V, i, hs(a, V[i], pr));
P41 = idealprimedec(K,41);
print("nprimes41 ", #P41);
for (j = 1, 2, pr = P41[j]; print("cap41 ", j, " frob(41) ", vecof(41, pr)));
quit
