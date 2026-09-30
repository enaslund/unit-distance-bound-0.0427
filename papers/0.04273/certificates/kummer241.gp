\\ Kummer basis and local Hilbert-symbol vectors for B = Q(sqrt 241)
\\ (Section 2 of the manuscript: the basis alpha_0..alpha_7 of V, the primes of
\\ Lemma tw:base, Table tw:squareclass-table and Table tw:vector-table).
\\ The basis alpha_0..alpha_7 and the prime labels p_j, q_j, r_j, t_j, t_0 are
\\ those of the paper, entered explicitly and checked below; nothing depends on
\\ PARI's choice of generators or on its ordering of prime ideals.
default(parisize,"1G");
K = bnfinit(y^2 - 241, 1);
w = Mod(y, K.pol);                                   \\ sqrt(241)
check(c, msg) = if (!c, print("FAILED: ", msg); quit(1));
\\ the Kummer basis alpha_0, ..., alpha_7 of the paper
{V = [Mod(-1, K.pol), -71011068 + 4574225*w, (-6101 - 393*w)/2, (6101 - 393*w)/2,
     31 - 2*w, 31 + 2*w, 326 - 21*w, 326 + 21*w];}
check(#select(a -> denominator(nfalgtobasis(K, a)) != 1, V) == 0, "alpha_i are integral");
check(apply(a -> norm(a), V) == [1, -1, -2, -2, -3, -3, -5, -5], "norms of alpha_0..alpha_7");
check(V[3]*V[4] == 2 && V[5]*V[6] == -3 && V[7]*V[8] == -5, "alpha_2 alpha_3 = 2, alpha_4 alpha_5 = -3, alpha_6 alpha_7 = -5");
check(bnfisunit(K, V[2])[1] % 2 == 1, "eps is an odd power of a fundamental unit");
\\ the primes of the paper, identified by their generators
prime_of(g, p) = {
  my(L = idealprimedec(K, p), H = idealhnf(K, g), r = []);
  for (i = 1, #L, if (idealhnf(K, L[i]) == H, r = concat(r, [L[i]])));
  check(#r == 1, Str("the generator ", g, " generates a prime of degree one above ", p));
  r[1];
}
p1 = prime_of(V[3], 2); p2 = prime_of(V[4], 2);
q1 = prime_of(V[5], 3); q2 = prime_of(V[6], 3);
r1 = prime_of(V[7], 5); r2 = prime_of(V[8], 5);
t1 = prime_of(-14127 + 910*w, 29); t2 = prime_of(-14127 - 910*w, 29);
P7 = idealprimedec(K, 7);
check(#P7 == 1 && P7[1].f == 2, "7 is inert"); t0 = P7[1];
{check(idealhnf(K, p1) != idealhnf(K, p2) && idealhnf(K, q1) != idealhnf(K, q2)
      && idealhnf(K, r1) != idealhnf(K, r2) && idealhnf(K, t1) != idealhnf(K, t2),
      "the two primes above each of 2, 3, 5, 29 are distinct");}
\\ the residues of sqrt(241) at the primes of degree one (Table tw:squareclass-table)
res = [[p1, 7, 5], [p2, 25, 5], [q1, 2, 1], [q2, 1, 1], [r1, 1, 1], [r2, 4, 1], [t1, 3, 1], [t2, 26, 1]];
for (i = 1, #res, check(idealval(K, w - res[i][2], res[i][1]) >= res[i][3], Str("residue of sqrt(241), case ", i)));
print("PASS Kummer basis alpha_0..alpha_7 and prime labels p_j, q_j, r_j, t_j, t_0 of the paper");
print("V = ", V);
print("norms ", apply(a->norm(a), V));
\\ exact sign of a at the real place y -> s*sqrt(241), s = +1 (v_1) or -1 (v_2): 1 if negative
sgn(a, s) = {
  my(c = lift(Mod(a, K.pol)), u = polcoef(c, 0, y), v = s*polcoef(c, 1, y));
  if (u >= 0 && v >= 0, 0, if (u <= 0 && v <= 0, 1, if (u^2 > 241*v^2, u < 0, v < 0)));
}
hs(a, b, pr) = if (nfhilbert(K, a, b, pr) == -1, 1, 0);
vecof(a, pr) = vector(#V, i, hs(a, V[i], pr));
realvec(s) = vector(#V, i, sgn(V[i], s));
print("c1 ", realvec(1));
print("c2 ", realvec(-1));
{
my(P = [p1, p2], Q = [q1, q2], R = [r1, r2], T = [t1, t2], pr, g);
for (j = 1, 2, pr = P[j];
  print("dyadic ", j, " x(5) ", vecof(5, pr), " y(-1) ", vecof(-1, pr), " z(-2) ", vecof(-2, pr)));
for (j = 1, 2, pr = Q[j]; g = V[4+j];
  print("three ", j, " tau(-1) ", vecof(-1, pr), " phi(-pi) ", vecof(-g, pr)));
for (j = 1, 2, pr = R[j]; g = V[6+j];
  print("five ", j, " tau(2) ", vecof(2, pr), " phi(-pi) ", vecof(-g, pr)));
for (j = 1, 2, pr = T[j]; print("cap29 ", j, " frob(29) ", vecof(29, pr)));
print("inert7 frob(7) ", vecof(7, t0));
}
quit
