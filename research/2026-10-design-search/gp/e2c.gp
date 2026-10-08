default(parisize,"2G");
P = polredabs(polcompositum(polcompositum(x^2+1, x^2-2)[1], x^2-5)[1]);
P = subst(P, x, y);
E = nfinit(P);
pr = idealprimedec(E, 2)[1];
G = nfgaloisconj(E);
S = concat([idealprimedec(E,2), idealprimedec(E,3), idealprimedec(E,5), idealprimedec(E,7), idealprimedec(E,11), idealprimedec(E,13), idealprimedec(E,17)]);
bnf = bnfinit(P, 1);
su = bnfsunit(bnf, S);
gens = concat([bnf.tu[2]], concat(bnf.fu, su[1]));
gens = apply(g -> nfalgtobasis(E, g), gens);
n = #gens;
hil(a,b) = (1 - nfhilbert(E, a, b, pr))/2;
Mh = matrix(n, n, i, j, hil(gens[i], gens[j]));
B = [];
{for(i=1,n, cand = concat(B,[i]); M = matrix(#cand,n,a,b, Mh[cand[a],b]); if(matrank(M*Mod(1,2)) > #B, B = cand); if(#B==10, break));}
Gram = matrix(10,10,i,j, Mh[B[i],B[j]]);
Gi = Mod(Gram,2)^(-1);
cls(a) = vector(10, j, hil(a, gens[B[j]]))~;
coord(a) = lift(Gi * Mod(cls(a),2));
Tmats = vector(#G, k, matconcat(vector(10, i, coord(nfgaloisapply(E, G[k], gens[B[i]])))));
K = matconcat(vector(#G, k, Mod(Tmats[k] - matid(10), 2))~);
Fl = lift(matker(K));
print("fixed dim ", #Fl);
elt(c) = {my(b = 1); for(i=1,10, if(c[i], b = nfeltmul(E, b, gens[B[i]]))); b};
cond(c) = {my(b = elt(c), R); R = rnfdisc(E, x^2 - nfbasistoalg(E,b)); idealval(E, R[1], pr)};
res = List();
{forvec(v = vector(5, i, [0,1]), if(vecsum(v)==0, next); c = (Fl * v~) % 2; listput(res, [v, cond(c)]));}
print("conductors (class coords in fixed basis, conductor exponent at P): ");
{foreach(res, r, print(r[1], "  c=", r[2]));}
\\ save for python
write("conductors.txt", Vec(res));
