default(parisize,"1G");
K = bnfinit(y^2 - 241, 1);
eps = K.fu[1];
\\ primes above 2,3,5,29 and the inert prime 7
P2 = idealprimedec(K,2); P3 = idealprimedec(K,3); P5 = idealprimedec(K,5); P29 = idealprimedec(K,29); P7 = idealprimedec(K,7);
gen(pr) = nfbasistoalg(K, bnfisprincipal(K, pr)[2]);
pis = [gen(P2[1]), gen(P2[2]), gen(P3[1]), gen(P3[2]), gen(P5[1]), gen(P5[2])];
V = concat([-1, eps], pis);   \\ Kummer basis
print("V = ", V);
print("norms ", apply(a->norm(a), V));
\\ real embeddings: y -> +sqrt(241) (place 1), y -> -sqrt(241) (place 2)
sgn(a, s) = { my(v = subst(lift(Mod(a, y^2-241)), y, s*sqrt(241.))); if (v < 0, 1, 0); }
hs(a, b, pr) = if (nfhilbert(K, a, b, pr) == -1, 1, 0);
vecof(a, pr) = vector(#V, i, hs(a, V[i], pr));
realvec(s) = vector(#V, i, sgn(V[i], s));
print("c1 ", realvec(1));
print("c2 ", realvec(-1));
{
for (j = 1, 2, pr = P2[j];
  print("dyadic ", j, " x(5) ", vecof(5, pr), " y(-1) ", vecof(-1, pr), " z(-2) ", vecof(-2, pr)));
for (j = 1, 2, pr = P3[j]; pi = pis[2+j];
  print("three ", j, " tau(-1) ", vecof(-1, pr), " phi(-pi) ", vecof(-pi, pr)));
for (j = 1, 2, pr = P5[j]; pi = pis[4+j];
  u = 2; print("five ", j, " tau(2) ", vecof(2, pr), " phi(-pi) ", vecof(-pi, pr)));
for (j = 1, 2, pr = P29[j]; print("cap29 ", j, " frob(29) ", vecof(29, pr)));
print("inert7 frob(7) ", vecof(7, P7[1]));
}
quit
