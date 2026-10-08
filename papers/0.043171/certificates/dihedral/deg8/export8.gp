\\ The 16 degree-8 L-functions L(s, rho_O1 (x) rho_O2 (x) lambda_w) (globals O1, default 19, and O2) as quotients
\\ zeta(F'_w)/zeta(F_L) (Mackey): F_L = B(sqrt c_O1, sqrt c_O2), F'_w = F_L(sqrt(gamma_O1 gamma_O2 alpha^w)), w over the
\\ complement of span(r1_O1, r2_O1, r1_O2, r2_O2) (greedy unit vectors).  gamma_o = g0 + g1 sqrt(c_o) as in ddata27.gp.
\\ The JSON keys c19, g0_19, g1_19 hold the data of O1 (for O1 = 19 as named).
\\ Writes deg8_<O1>_<O2>.json (or the file named by the string OUT): the elements, F_L, and for each twist the conductor
\\ Q = |d(F')|/|d(F_L)| and the Euler denominator polynomials at every prime p <= PSMALL (global, default 2^18).
\\ Asserts: F_L and F' totally complex (gamma factor Gamma_C(s)^4), |d(F')| a {2,3,5,241}-unit (so the orders computed
\\ with that partial factorization are maximal), and that each local quotient is a polynomial of degree <= 8.
\\ Run from certificates/dihedral.
read("ddata27.gp");
belt(z) = { my(zz = lift(Mod(z, t^2 - 241)), d = denominator(content(zz))); [numerator(polcoef(zz*d, 0, t)), numerator(polcoef(zz*d, 1, t)), d] };
gam(j) =
{
  my(f = FIELDS[j], r1 = f[1], r2 = f[2], rho = f[3], co = f[4], m = f0model(r1, r2), P0 = m[1], s = m[2], sa = m[3], sb = m[4], a = m[5], b = m[6], nf0 = nfinit(P0), beta, AU, tauv, g, u, gm, c, sc);
  beta = co[1] + co[2]*s + co[3]*sa + co[4]*s*sa + co[5]*sb + co[6]*s*sb + co[7]*sa*sb + co[8]*s*sa*sb;
  tauv = if(rho == [1,0], [0,1], [1,0]);
  c = if(tauv == [1,0], b, a); sc = if(tauv == [1,0], sb, sa);
  AU = nfgaloisconj(nf0); g = 0;
  for(i = 1, #AU, my(h = Mod(AU[i], P0), ap = z -> Mod(subst(lift(z), y, lift(h)), P0));
     if(ap(s) == s && ap(sa) == (-1)^tauv[1]*sa && ap(sb) == (-1)^tauv[2]*sb, g = h));
  if(g == 0, error("tau not found"));
  my(ap = z -> Mod(subst(lift(z), y, lift(g)), P0));
  u = Mod(nfroots(nf0, x^2 - lift(ap(beta)/beta))[1], P0);
  if(u * ap(u) != 1, error("tau lift not an involution"));
  gm = (1 + u)^2 * beta; if(gm == 0, gm = (1 - u)^2 * beta);
  if(ap(gm) != gm, error("gamma not tau-invariant"));
  my(bas = [1, s, sc, s*sc], Mb = matrix(8, 4, i, k, polcoef(lift(bas[k]), i - 1, y)), v = vector(8, i, polcoef(lift(gm), i - 1, y))~, sol = matsolve(Mb[1..4,], v[1..4]));
  if(Mb * sol != v, error("gamma not in B(sqrt c)"));
  [lift(c), sol[1] + sol[2]*t, sol[3] + sol[4]*t, r1, r2, rho]
}
zloc(nf, p) = my(D = idealprimedec(nf, p)); prod(i = 1, #D, 1 - X^D[i].f);
isSunit(d) = { my(r = abs(d)); foreach([2, 3, 5, 241], q, r /= q^valuation(r, q)); r == 1 };
{
  if(type(PSMALL) != "t_INT", PSMALL = 2^18);
  if(type(O1) != "t_INT", O1 = 19);
  my(A = gam(O1 + 1), C = gam(O2 + 1), fh = if(type(OUT) == "t_STR", OUT, Str("deg8_", O1, "_", O2, ".json")), Bt = nfinit(t^2 - 241));
  system(Str("rm -f ", fh));
  my(R1 = rnfequation(Bt, x^2 - A[1], 1), P1 = subst(R1[1], x, z), st1 = subst(lift(R1[2]), x, z), s19 = z - R1[3]*st1);
  my(nf1 = nfinit(P1), coz = lift(Mod(subst(C[1], t, st1), P1)));
  my(R2 = rnfequation(nf1, x^2 - coz, 1), PL = subst(R2[1], x, v), zz = subst(lift(R2[2]), x, v), st = subst(subst(st1, z, zz), x, v), s19v = subst(subst(s19, z, zz), x, v), sov = v - R2[3]*zz);
  my(nfL = nfinit([polredbest(PL), [2,3,5,241]]), dL = abs(nfL.disc));
  nfL = nfinit([PL, [2,3,5,241]]);         \\ the model in v is needed for the relative equations below
  if(!isSunit(dL) || nfL.sign != [0, 4], error("F_L"));
  my(g19 = Mod(subst(A[2], t, st) + subst(A[3], t, st)*s19v, PL), gO = Mod(subst(C[2], t, st) + subst(C[3], t, st)*sov, PL));
  \\ twist representatives: complement of span(r1_19, r2_19, r1_o, r2_o)
  my(M = Mat([A[4]~, A[5]~, C[4]~, C[5]~]), basis = List());
  if(matrank(Mod(M, 2)) != 4, error("rank of the r-vectors"));
  for(i = 1, 8, my(e = vector(8, j, j == i)~, N = matconcat([M, e])); if(matrank(Mod(N, 2)) > matrank(Mod(M, 2)), M = N; listput(basis, e~)));
  if(#basis != 4, error("complement"));
  my(ws = vector(16, k, my(w = vector(8)); for(j = 1, 4, if(bittest(k - 1, j - 1), w = (w + basis[j]) % 2)); w));
  my(PR = primes([2, PSMALL]), zL = vector(#PR, i, zloc(nfL, PR[i])));
  my(s = Str("{\"pair\": [", O1, ", ", O2, "], \"c19\": ", belt(A[1]), ", \"g0_19\": ", belt(A[2]), ", \"g1_19\": ", belt(A[3]),
             ", \"cO\": ", belt(C[1]), ", \"g0_O\": ", belt(C[2]), ", \"g1_O\": ", belt(C[3]),
             ", \"r\": [", A[4], ", ", A[5], ", ", C[4], ", ", C[5], "], \"rho\": [", A[6], ", ", C[6], "]",
             ", \"dFL\": ", dL, ", \"PFL\": \"", PL, "\", \"PSMALL\": ", PSMALL, ", \"twists\": ["));
  for(k = 1, 16,
    my(T0 = getwalltime(), aw = Mod(subst(lift(alph(ws[k])), t, st), PL), gm = lift(g19 * gO * aw));
    \\ polredbest: an isomorphic field with a small defining polynomial (the Euler factors and the discriminant are
    \\ invariants of the field); the S-unit check below certifies the maximal order
    my(Rp = polredbest(rnfequation(nfL, x^2 - gm)), nfp = nfinit([Rp, [2,3,5,241]]), dp = abs(nfp.disc), Qc = dp / dL);
    if(!isSunit(dp) || nfp.sign != [0, 8] || denominator(Qc) != 1, error("F' twist ", k));
    my(loc = vector(#PR, i, my(p = PR[i], zp = zloc(nfp, p), q = zp / zL[i]);
       if(type(q) != "t_POL" || poldegree(q) > 8, error("local quotient at ", p));
       Str("\"", p, "\": ", Vec(q + O(X^9)))));
    s = Str(s, if(k > 1, ", ", ""), "{\"w\": ", ws[k], ", \"Q\": ", Qc, ", \"small\": {", strjoin(loc, ", "), "}}");
    print("twist ", k, " w = ", ws[k], " Q = ", Qc, " ~ ", Qc * 1., "  (", (getwalltime() - T0) \ 1000, " s)"));
  s = Str(s, "]}");
  write(fh, s);
  print("export8: wrote ", fh);
}
