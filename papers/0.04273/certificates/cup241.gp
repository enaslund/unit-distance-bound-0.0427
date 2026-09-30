\\ Local invariants of the quaternion algebras (alpha_i, alpha_j) over B = Q(sqrt 241)
\\ (Section 2 of the manuscript: Lemma tw:local-forms and Remark tw:cup-remark).
\\ The basis alpha_0..alpha_7 and the primes p_j = (alpha_{1+j}), q_j = (alpha_{3+j}),
\\ r_j = (alpha_{5+j}) are those of the paper, entered explicitly and checked below;
\\ nothing depends on PARI's choice of generators or on its ordering of prime ideals.
default(parisize,"1G");
K = bnfinit(y^2 - 241, 1);
w = Mod(y, K.pol);                                   \\ sqrt(241)
check(c, msg) = if (!c, print("FAILED: ", msg); quit(1));
{V = [Mod(-1, K.pol), -71011068 + 4574225*w, (-6101 - 393*w)/2, (6101 - 393*w)/2,
     31 - 2*w, 31 + 2*w, 326 - 21*w, 326 + 21*w];}
check(apply(a -> norm(a), V) == [1, -1, -2, -2, -3, -3, -5, -5], "norms of alpha_0..alpha_7");
prime_of(g, p) = {
  my(L = idealprimedec(K, p), H = idealhnf(K, g), r = []);
  for (i = 1, #L, if (idealhnf(K, L[i]) == H, r = concat(r, [L[i]])));
  check(#r == 1, Str("the generator ", g, " generates a prime of degree one above ", p));
  r[1];
}
\\ the six primes of S in the order p_1, p_2, q_1, q_2, r_1, r_2
fin = [prime_of(V[3], 2), prime_of(V[4], 2), prime_of(V[5], 3), prime_of(V[6], 3), prime_of(V[7], 5), prime_of(V[8], 5)];
check(#Set(apply(pr -> idealhnf(K, pr), fin)) == 6, "the six primes of S are distinct");
\\ the residues of sqrt(241) at p_1, p_2 (7 and 25 mod 32) fix the labels of the dyadic primes
check(idealval(K, w - 7, fin[1]) >= 5 && idealval(K, w - 25, fin[2]) >= 5, "residues of sqrt(241) at p_1, p_2");
print("PASS Kummer basis alpha_0..alpha_7 and the primes of S labeled as in the paper");
\\ exact sign test at the real place y -> s*sqrt(241), s = +1 (v_1) or -1 (v_2): 1 if negative
sg(a, s) = {
  my(c = lift(Mod(a, K.pol)), u = polcoef(c, 0, y), v = s*polcoef(c, 1, y));
  if (u >= 0 && v >= 0, 0, if (u <= 0 && v <= 0, 1, if (u^2 > 241*v^2, u < 0, v < 0)));
}
realinv(a, b, s) = (sg(a,s) && sg(b,s));
\\ local invariant vector of quaternion algebra (a,b) at the 8 places [p_1, p_2, q_1, q_2, r_1, r_2, v_1, v_2]
inv(a, b) = concat(vector(6, k, nfhilbert(K, a, b, fin[k]) == -1), [realinv(a,b,1), realinv(a,b,-1)]);
for (i = 1, 8, for (j = i, 8, print(i," ",j," ",inv(V[i], V[j]))));
quit
