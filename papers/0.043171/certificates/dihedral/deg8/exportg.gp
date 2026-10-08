\\ export.gp for D4 fields whose twists need not have gamma factor Gamma_C(s)^2 (orbit 20): the same data for the
\\ 64 twists of orbit ORB, plus r1(K_w) and r1(Bc) (so the gamma factor of zeta(K_w)/zeta(Bc) is
\\ Gamma_R(s)^(r1(K) - r1(Bc)) Gamma_C(s)^(r2(K) - r2(Bc))), with Euler polynomials at 7 <= p <= PSMALL (global,
\\ default 1000).  Writes the file named by the string OUT.  Run from certificates/dihedral.
read("ddata27.gp");
belt(z) = { my(zz = lift(Mod(z, t^2 - 241)), d = denominator(content(zz))); [numerator(polcoef(zz*d, 0, t)), numerator(polcoef(zz*d, 1, t)), d] };
{
  if(type(PSMALL) != "t_INT", PSMALL = 1000);
  my(r = ddata(ORB + 1), nfBc = nfinit(r[5]), fh = OUT, PR = primes([7, PSMALL]));
  system(Str("rm -f ", fh));
  my(ent = vector(64, k, my(z = r[4][k], nfK = nfinit(z[4]));
        [z[1], z[2], z[3], vector(#PR, i, my(p = PR[i]); [p, Vec(zloc(nfK, p) / zloc(nfBc, p) + O(X^9))]), polsturm(z[4])]));
  my(s = Str("{\"c\": ", belt(r[1]), ", \"g0\": ", belt(r[2]), ", \"g1\": ", belt(r[3]), ", \"dBc\": ", r[6], ", \"PBc\": \"", r[5],
             "\", \"r1Bc\": ", polsturm(r[5]), ", \"PSMALL\": ", PSMALL, ", \"twists\": ["));
  for(k = 1, 64, my(e = ent[k]);
     s = Str(s, if(k > 1, ", ", ""), "{\"w\": ", e[1], ", \"Q\": ", e[2], ", \"r1K\": ", e[5], ", \"bad\": {\"2\": ", e[3][1], ", \"3\": ", e[3][2], ", \"5\": ", e[3][3], "}, \"small\": {");
     for(i = 1, #e[4], s = Str(s, if(i > 1, ", ", ""), "\"", e[4][i][1], "\": ", e[4][i][2]));
     s = Str(s, "}, \"K\": \"", r[4][k][4], "\"}"));
  s = Str(s, "]}");
  write(fh, s);
  print("exportg: wrote ", fh);
}
