default(parisize,"4G"); default(realprecision, 38);
K = bnfinit(y^2 - 241, 1);
gen(pr) = nfbasistoalg(K, bnfisprincipal(K, pr)[2]);
V = [-1, K.fu[1], gen(idealprimedec(K,2)[1]), gen(idealprimedec(K,2)[2]), gen(idealprimedec(K,3)[1]), gen(idealprimedec(K,3)[2]), gen(idealprimedec(K,5)[1]), gen(idealprimedec(K,5)[2])];
alpha(e) = { my(a = Mod(1, y^2-241)); for (i = 1, 8, if (bittest(e, i-1), a *= V[i])); a; }
s = 301/300;
zB = lfun(lfuncreate(x^2-241), s);
tot = log(zB);
for (e = 1, 255, my(P = polredbest(rnfequation(K, x^2 - lift(alpha(e))))); tot += log(lfun(lfuncreate(P), s)) - log(zB));
print("PARI Y_E(301/300) = ", tot/512);
quit
