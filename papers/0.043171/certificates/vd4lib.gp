\\ Shared verification routine for D4 fields (used by vd4.gp and dihedral/vplane.gp).
default(breakloop, 0);
KB = [-1, -71011068+4574225*t, (-6101-393*t)/2, (6101-393*t)/2, 31-2*t, 31+2*t, 326-21*t, 326+21*t];
alph(row) = prod(i=1,8, if(row[i], KB[i], 1));
vd4(r1, r2, rho, co) =
{
  my(a = alph(r1), b = alph(r2), Bt, R1, P1, nf1, s1, sa1, R0, P0, nf0, s, sa, sb, beta, fa, ok, AU, g, sig, q, rt, u, w, tp, Mt, Mpol, dM, bad);
  Bt = nfinit(t^2 - 241);
  R1 = rnfequation(Bt, x^2 - a, 1);            \\ [P1, t in terms of theta1, k1]: theta1 = sqrt(a) + k1 t
  P1 = R1[1]; s1 = lift(R1[2]); sa1 = x - R1[3]*s1;
  nf1 = nfinit(subst(P1, x, y));
  my(bb = lift(Mod(subst(lift(b), t, subst(s1, x, y)), subst(P1, x, y))));
  R0 = rnfequation(nf1, x^2 - bb, 1);          \\ theta0 = sqrt(b) + k0 theta1
  P0 = R0[1];
  my(yy = lift(R0[2]));
  P0 = subst(P0, x, y);
  s = Mod(subst(subst(s1, x, yy), x, y), P0);
  sa = Mod(subst(subst(sa1, x, yy), x, y), P0);
  sb = Mod(subst(x - R0[3]*yy, x, y), P0);
  if(sa^2 != subst(lift(a), t, s) || sb^2 != subst(lift(b), t, s) || s^2 != 241, error("embedding check"));
  beta = co[1] + co[2]*s + co[3]*sa + co[4]*s*sa + co[5]*sb + co[6]*s*sb + co[7]*sa*sb + co[8]*s*sa*sb;
  nf0 = nfinit(P0);
  \\ (1) S-unit: ideal factorization supported above 2, 3, 5
  fa = idealfactor(nf0, lift(beta)); bad = 0;
  for(i = 1, #fa~, if(!setsearch([2,3,5], fa[i,1].p), bad = 1));
  if(bad, error("beta not an S-unit"));
  \\ (2) Galois automorphisms over B: images of sa, sb
  tp = vector(3); my(found = vector(3));
  AU = nfgaloisconj(nf0);
  for(i = 1, #AU, g = Mod(AU[i], P0);
     my(ap = z -> Mod(subst(lift(z), y, lift(g)), P0));
     if(ap(s) != s, next);
     my(ea = ap(sa) == -sa, eb = ap(sb) == -sb, k);
     if(!ea && !eb, next);
     k = if(ea && !eb, 1, if(!ea && eb, 2, 3));
     q = ap(beta) / beta; rt = nfroots(nf0, x^2 - lift(q));
     if(#rt == 0, error(Str("sigma(beta)/beta not a square, k=", k)));
     u = Mod(rt[1], P0); w = u * ap(u);
     if(w == 1, tp[k] = 0, if(w == -1, tp[k] = 1, error("t not +-1")));
     found[k] = 1);
  if(found != [1,1,1], error("automorphisms over B missing"));
  if(tp != [rho == [1,0], rho == [0,1], rho == [1,1]], error(Str("t-pattern ", tp)));
  \\ (3) the octic-over-B field Mtilde = F0(sqrt beta): absolute polynomial, relative discriminant support
  my(rd = rnfdisc(nf0, x^2 - lift(beta)), dn = idealnorm(nf0, rd[1]));
  if(dn != 2^valuation(dn, 2) * 3^valuation(dn, 3) * 5^valuation(dn, 5), error("ramified outside S"));
  Mpol = rnfequation(nf0, x^2 - lift(beta));
  [tp, factor(dn), poldegree(Mpol), Mpol, P0]
}
