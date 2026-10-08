\\ For a D4 field (rows r1, r2, rho, coords of beta): the 64 twists L(s, rho x lambda_w) as quadratic Hecke
\\ L-functions over the quartic field Bc = B(sqrt c) (c = generator of F0^tau, tau a non-rho class):
\\ L(s, rho x lambda_w) = zeta(Bc(sqrt(gamma0 alpha^w))) / zeta(Bc), gamma0 = (1 + u)^2 beta, u^2 = tau(beta)/beta.
default(breakloop, 0);
KB = [-1, -71011068+4574225*t, (-6101-393*t)/2, (6101-393*t)/2, 31-2*t, 31+2*t, 326-21*t, 326+21*t];
alph(row) = prod(i=1,8, if(row[i], KB[i], 1));
\\ F0 model as in vd4.gp: returns [P0 (in y), s, sa, sb] as polmods
f0model(r1, r2) =
{
  my(a = alph(r1), b = alph(r2), Bt = nfinit(t^2 - 241), R1, P1, s1, sa1, nf1, bb, R0, P0, yy, s, sa, sb);
  R1 = rnfequation(Bt, x^2 - a, 1); P1 = R1[1]; s1 = lift(R1[2]); sa1 = x - R1[3]*s1;
  nf1 = nfinit(subst(P1, x, y));
  bb = lift(Mod(subst(lift(b), t, subst(s1, x, y)), subst(P1, x, y)));
  R0 = rnfequation(nf1, x^2 - bb, 1); P0 = R0[1]; yy = lift(R0[2]);
  P0 = subst(P0, x, y);
  s = Mod(subst(subst(s1, x, yy), x, y), P0);
  sa = Mod(subst(subst(sa1, x, yy), x, y), P0);
  sb = Mod(subst(x - R0[3]*yy, x, y), P0);
  [P0, s, sa, sb, a, b]
}
twists(r1, r2) =
{
  \\ complement of span(r1, r2) in F2^8: greedy unit vectors
  my(M = Mat([r1~, r2~]), basis = List());
  for(i = 1, 8, my(e = vector(8, j, j == i)~, N = matconcat([M, e]));
     if(matrank(Mod(N, 2)) > matrank(Mod(M, 2)), M = N; listput(basis, e~)));
  if(#basis != 6, error("complement"));
  vector(64, k, my(w = vector(8)); for(j = 1, 6, if(bittest(k - 1, j - 1), w = (w + basis[j]) % 2)); w)
}
dcond(r1, r2, rho, co) =
{
  my(m = f0model(r1, r2), P0 = m[1], s = m[2], sa = m[3], sb = m[4], a = m[5], b = m[6], nf0 = nfinit(P0), beta, AU, tauv, g, u, gam, c, sc, out = vector(64), Bc, nfBc, dBc, ws);
  beta = co[1] + co[2]*s + co[3]*sa + co[4]*s*sa + co[5]*sb + co[6]*s*sb + co[7]*sa*sb + co[8]*s*sa*sb;
  \\ tau: non-rho class; c with tau(sqrt c) = sqrt c
  tauv = if(rho == [1,0], [0,1], [1,0]);
  c = if(tauv == [1,0], b, a); sc = if(tauv == [1,0], sb, sa);
  AU = nfgaloisconj(nf0); g = 0;
  for(i = 1, #AU, my(h = Mod(AU[i], P0), ap = z -> Mod(subst(lift(z), y, lift(h)), P0));
     if(ap(s) == s && ap(sa) == (-1)^tauv[1]*sa && ap(sb) == (-1)^tauv[2]*sb, g = h));
  if(g == 0, error("tau not found"));
  my(ap = z -> Mod(subst(lift(z), y, lift(g)), P0));
  u = Mod(nfroots(nf0, x^2 - lift(ap(beta)/beta))[1], P0);
  if(u * ap(u) != 1, error("tau lift not an involution"));
  gam = (1 + u)^2 * beta;
  if(gam == 0, gam = (1 - u)^2 * beta);
  if(ap(gam) != gam, error("gamma not tau-invariant"));
  \\ gamma = g0 + g1 sqrt c with g0, g1 in B: solve in the basis {1, s, sc, s sc}
  my(bas = [1, s, sc, s*sc], Mb = matrix(8, 4, i, j, polcoef(lift(bas[j]), i - 1, y)), sol = matsolve(Mb[1..4,], vector(4, i, polcoef(lift(gam), i - 1, y))~));
  if(Mb * sol != vector(8, i, polcoef(lift(gam), i - 1, y))~, error("gamma not in B(sqrt c)"));
  \\ B(sqrt c) absolute: Bc in variable y
  my(Bt = nfinit(t^2 - 241), R = rnfequation(Bt, x^2 - c, 1), PBc = subst(R[1], x, y), st = subst(lift(R[2]), x, y), sct = y - R[3]*st);
  nfBc = nfinit(PBc); dBc = abs(nfBc.disc);
  my(g0 = sol[1] + sol[2]*st, g1 = sol[3] + sol[4]*st, gamBc = lift(Mod(g0 + g1*sct, PBc)));
  ws = twists(r1, r2);
  for(k = 1, 64, my(w = ws[k], aw = lift(Mod(subst(lift(alph(w)), t, st), PBc)), gw = lift(Mod(gamBc * aw, PBc)), K = rnfequation(nfBc, x^2 - gw), dK = abs(nfdisc(K)));
     out[k] = [w, dK / dBc, polsturm(K)]);
  [out, dBc, polsturm(PBc), gamBc, PBc]
}
