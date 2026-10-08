\\ Data for the 64 twisted dihedral L-functions of one D4 field: L_w = zeta(Bc(sqrt gamma_w))/zeta(Bc),
\\ gamma_w = gamma0 * alpha^w.  Writes ddata_<j>.gp with: c (in t), gamma0 = g0 + g1 sqrt(c) (g0, g1 in t),
\\ the 64 vectors w, the conductors Q_w, and the bad Euler denominators at 2, 3, 5.
read("dcond.gp"); read("vd4_data27.gp");
\\ local Euler denominator polynomial of zeta_K at p, as a polynomial in X (X = p^-s)
zloc(nf, p) = prod(i = 1, #idealprimedec(nf, p), 1 - X^(idealprimedec(nf, p)[i].f));
ddata(j) =
{
  my(f = FIELDS[j], r1 = f[1], r2 = f[2], rho = f[3], co = f[4], m = f0model(r1, r2), P0 = m[1], s = m[2], sa = m[3], sb = m[4], a = m[5], b = m[6], nf0 = nfinit(P0), beta, AU, tauv, g, u, gam, c, sc, ws, out);
  beta = co[1] + co[2]*s + co[3]*sa + co[4]*s*sa + co[5]*sb + co[6]*s*sb + co[7]*sa*sb + co[8]*s*sa*sb;
  tauv = if(rho == [1,0], [0,1], [1,0]);
  c = if(tauv == [1,0], b, a); sc = if(tauv == [1,0], sb, sa);
  AU = nfgaloisconj(nf0); g = 0;
  for(i = 1, #AU, my(h = Mod(AU[i], P0), ap = z -> Mod(subst(lift(z), y, lift(h)), P0));
     if(ap(s) == s && ap(sa) == (-1)^tauv[1]*sa && ap(sb) == (-1)^tauv[2]*sb, g = h));
  my(ap = z -> Mod(subst(lift(z), y, lift(g)), P0));
  u = Mod(nfroots(nf0, x^2 - lift(ap(beta)/beta))[1], P0);
  if(u * ap(u) != 1, error("tau lift not an involution"));
  gam = (1 + u)^2 * beta; if(gam == 0, gam = (1 - u)^2 * beta);
  if(ap(gam) != gam, error("gamma not tau-invariant"));
  my(bas = [1, s, sc, s*sc], Mb = matrix(8, 4, i, k, polcoef(lift(bas[k]), i - 1, y)), v = vector(8, i, polcoef(lift(gam), i - 1, y))~, sol = matsolve(Mb[1..4,], v[1..4]));
  if(Mb * sol != v, error("gamma not in B(sqrt c)"));
  my(g0 = sol[1] + sol[2]*t, g1 = sol[3] + sol[4]*t);
  my(Bt = nfinit(t^2 - 241), R = rnfequation(Bt, x^2 - c, 1), PBc = subst(R[1], x, y), st = subst(lift(R[2]), x, y), sct = y - R[3]*st, nfBc = nfinit(PBc), dBc = abs(nfBc.disc));
  my(gamBc = lift(Mod(subst(g0, t, st) + subst(g1, t, st)*sct, PBc)));
  ws = twists(r1, r2); out = vector(64);
  for(k = 1, 64, my(w = ws[k], aw = lift(Mod(subst(lift(alph(w)), t, st), PBc)), gw = lift(Mod(gamBc * aw, PBc)), K = rnfequation(nfBc, x^2 - gw), nfK = nfinit(K), Q = abs(nfK.disc) / dBc, bad = vector(3));
     for(i = 1, 3, my(p = [2,3,5][i]); bad[i] = Vec(zloc(nfK, p) / zloc(nfBc, p) + O(X^9)));
     out[k] = [w, Q, bad, K]);
  [lift(c), g0, g1, out, PBc, dBc]
}
