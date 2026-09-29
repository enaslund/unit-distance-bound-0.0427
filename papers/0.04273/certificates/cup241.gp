default(parisize,"1G");
K = bnfinit(y^2 - 241, 1);
eps = K.fu[1];
gen(pr) = nfbasistoalg(K, bnfisprincipal(K, pr)[2]);
P2 = idealprimedec(K,2); P3 = idealprimedec(K,3); P5 = idealprimedec(K,5);
V = [-1, eps, gen(P2[1]), gen(P2[2]), gen(P3[1]), gen(P3[2]), gen(P5[1]), gen(P5[2])];
fin = [P2[1], P2[2], P3[1], P3[2], P5[1], P5[2]];
sg(a, s) = { my(v = subst(lift(Mod(a, y^2-241)), y, s*sqrt(241.))); v < 0; }
realinv(a, b, s) = (sg(a,s) && sg(b,s));
\\ local invariant vector of quaternion algebra (a,b) at the 8 places [P2_1,P2_2,P3_1,P3_2,P5_1,P5_2, v1, v2]
inv(a, b) = concat(vector(6, k, nfhilbert(K, a, b, fin[k]) == -1), [realinv(a,b,1), realinv(a,b,-1)]);
for (i = 1, 8, for (j = i, 8, print(i," ",j," ",inv(V[i], V[j]))));
quit
