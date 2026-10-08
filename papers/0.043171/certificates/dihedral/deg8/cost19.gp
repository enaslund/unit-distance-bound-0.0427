\\ cost study: degree-8 L-functions L(s, rho19 x rho23) = zeta(F')/zeta(F_L), F_L = B(sqrt c19, sqrt c23), F' = F_L(sqrt(gamma19 gamma23))
read("ddata27.gp");
cg(j) =
{
  my(f = FIELDS[j], r1 = f[1], r2 = f[2], rho = f[3], co = f[4], m = f0model(r1, r2), P0 = m[1], s = m[2], sa = m[3], sb = m[4], a = m[5], b = m[6], nf0 = nfinit(P0), beta, AU, tauv, g, u, gam, c, sc);
  beta = co[1] + co[2]*s + co[3]*sa + co[4]*s*sa + co[5]*sb + co[6]*s*sb + co[7]*sa*sb + co[8]*s*sa*sb;
  tauv = if(rho == [1,0], [0,1], [1,0]);
  c = if(tauv == [1,0], b, a); sc = if(tauv == [1,0], sb, sa);
  AU = nfgaloisconj(nf0); g = 0;
  for(i = 1, #AU, my(h = Mod(AU[i], P0), ap = z -> Mod(subst(lift(z), y, lift(h)), P0));
     if(ap(s) == s && ap(sa) == (-1)^tauv[1]*sa && ap(sb) == (-1)^tauv[2]*sb, g = h));
  my(ap = z -> Mod(subst(lift(z), y, lift(g)), P0));
  u = Mod(nfroots(nf0, x^2 - lift(ap(beta)/beta))[1], P0);
  gam = (1 + u)^2 * beta; if(gam == 0, gam = (1 - u)^2 * beta);
  my(bas = [1, s, sc, s*sc], Mb = matrix(8, 4, i, k, polcoef(lift(bas[k]), i - 1, y)), v = vector(8, i, polcoef(lift(gam), i - 1, y))~, sol = matsolve(Mb[1..4,], v[1..4]));
  [lift(c), sol[1] + sol[2]*t, sol[3] + sol[4]*t, r1, r2]
}
{
  my(A = cg(20), C = cg(24));                         \\ orbits 19 and 23 (FIELDS is 1-indexed)
  print("c19 = ", A[1], "   c23 = ", C[1]);
  my(Bt = nfinit(t^2 - 241));
  \\ F_L = B(sqrt c19, sqrt c23) as an absolute field; generators s19, s23 expressed in it
  my(R1 = rnfequation(Bt, x^2 - A[1], 1), P1 = subst(R1[1], x, z), st1 = subst(lift(R1[2]), x, z), s19 = z - R1[3]*st1);
  my(nf1 = nfinit(P1), c23z = lift(Mod(subst(C[1], t, st1), P1)));
  my(R2 = rnfequation(nf1, x^2 - c23z, 1), PL = subst(R2[1], x, w), zz = subst(lift(R2[2]), x, w), st = subst(subst(st1, z, zz), x, w), s19w = subst(s19, z, zz), s23w = w - R2[3]*zz);
  my(nfL = nfinit([PL, [2,3,5,241]]), dL = abs(nfL.disc));
  print("F_L degree ", poldegree(PL), " signature ", nfL.sign, " |d(F_L)| = ", dL, " = ", factor(dL));
  my(g19 = Mod(subst(A[2], t, st) + subst(A[3], t, st)*s19w, PL), g23 = Mod(subst(C[2], t, st) + subst(C[3], t, st)*s23w, PL));
  for(k = 0, 3,
    my(gm = lift(g19 * g23 * Mod(subst(lift(alph(twists(FIELDS[20][1], FIELDS[20][2])[1 + 5*k])), t, st), PL)));
    my(Rp = rnfequation(nfL, x^2 - gm), nfp = nfinit([Rp, [2,3,5,241]]), Qc = abs(nfp.disc) / dL);
    print("twist ", k, ": F' signature ", nfp.sign, "  conductor Q = |d(F')|/|d(F_L)| = ", Qc, " ~ ", Qc*1., "  4 sqrt Q ~ ", 4*sqrt(Qc*1.)));
}
