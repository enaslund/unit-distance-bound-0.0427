\\ Export the data of the 64 twists of one D4 field (global ORB = orbit number) to ddata_orb<ORB>.json (or to the
\\ file named by the string OUT, if set):
\\ c, gamma0 = g0 + g1 sqrt c (elements of B as [a, b, den] = (a + b t)/den, t = sqrt 241), the conductor
\\ Q_w = |d(K_w)|/|d(Bc)| of each twist, its Euler denominator polynomials at 2, 3, 5 and at 7 <= p <= 1000
\\ (from prime decompositions in K_w = Bc(sqrt(gamma0 alpha^w)) and Bc = B(sqrt c)), and K_w.
\\ Asserts r1(K_w) = r1(Bc), so that zeta(K_w)/zeta(Bc) has gamma factor Gamma_C(s)^2.
read("ddata27.gp");
belt(z) = { my(zz = lift(Mod(z, t^2 - 241)), d = denominator(content(zz))); [numerator(polcoef(zz*d, 0, t)), numerator(polcoef(zz*d, 1, t)), d] };
{
  my(r = ddata(ORB + 1), nfBc = nfinit(r[5]), PSMALL = 1000, fh = if(type(OUT) == "t_STR", OUT, Str("ddata_orb", ORB, ".json")));
  system(Str("rm -f ", fh));    \\ write() appends
  for(k = 1, 64, if(polsturm(r[4][k][4]) != polsturm(r[5]), error("gamma factor: r1(K) != r1(Bc)")));
  my(ent = vector(64, k, my(z = r[4][k], nfK = nfinit(z[4]));
        [z[1], z[2], z[3], vector(#primes([7, PSMALL]), i, my(p = primes([7, PSMALL])[i]); [p, Vec(zloc(nfK, p) / zloc(nfBc, p) + O(X^9))])]));
  my(s = Str("{\"c\": ", belt(r[1]), ", \"g0\": ", belt(r[2]), ", \"g1\": ", belt(r[3]), ", \"dBc\": ", r[6], ", \"PBc\": \"", r[5], "\", \"twists\": ["));
  for(k = 1, 64, my(e = ent[k]);
     s = Str(s, if(k > 1, ", ", ""), "{\"w\": ", e[1], ", \"Q\": ", e[2], ", \"bad\": {\"2\": ", e[3][1], ", \"3\": ", e[3][2], ", \"5\": ", e[3][3], "}, \"small\": {");
     for(i = 1, #e[4], s = Str(s, if(i > 1, ", ", ""), "\"", e[4][i][1], "\": ", e[4][i][2]));
     s = Str(s, "}, \"K\": \"", r[4][k][4], "\"}"));
  s = Str(s, "]}");
  write(fh, s);
  print("export: wrote ", fh);
}
