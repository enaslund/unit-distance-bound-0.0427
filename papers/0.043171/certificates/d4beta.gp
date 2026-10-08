\\ For a D4 quotient of G_B given by rows r1, r2 (F2^8, bit i <-> Kummer basis element i) and the
\\ rotation class rho in F2^2 (the class whose lifts have order 4), find beta in F0 = B(sqrt a, sqrt b),
\\ a = alpha^r1, b = alpha^r2, an S-unit (S = primes above 2,3,5), with F0(sqrt beta)/B Galois of group
\\ D4 and rotation class rho.  Global state G0 = [F, nf, bnf, su, H, n].
KB = [-1, -71011068+4574225*t, (-6101-393*t)/2, (6101-393*t)/2, 31-2*t, 31+2*t, 326-21*t, 326+21*t];
alph(row) = prod(i=1,8, if(row[i], KB[i], 1));
ap(F, g, z) = lift(Mod(subst(lift(Mod(z, F)), y, g), F));
\\ discrete log modulo squares on H = [tu, fu..., S-unit gens...]
dlog(bnf, su, n, z) =
{
  my(e = bnfisunit(bnf, z, su));
  if(#e != n, error("dlog length"));
  vector(n, j, lift(e[j]) % 2)~
}
\\ t-pattern: for each sigma, u^2 = sigma(z)/z, t = u sigma(u) in {+1,-1} -> bit
tpat(F, nf, gs, z) =
{
  my(r = vector(3), q, rt, uu, w);
  for(k = 1, 3,
    q = lift(Mod(ap(F, gs[k], z) / z, F));
    rt = nfroots(nf, x^2 - q);
    if(#rt == 0, error("not invariant"));
    uu = lift(rt[1]);
    w = lift(Mod(uu * ap(F, gs[k], uu), F));
    if(w == 1, r[k] = 0, if(w == -1, r[k] = 1, error(Str("t not +-1: ", w)))));
  r
}
d4beta(r1, r2, rho) =
{
  my(a = alph(r1), b = alph(r2), P, F, nf, bnf, s, sa, sb, aF, bF, AU, Sa = 0, Sb = 0, Sab = 0, S, su, H, n, Ma, Mb, Inv, T, tgt, sol, beta, co, M, bel, gs, g, e0, e1, e2, bas, e, z, rr);
  for(c = 1, 50,
    P = polresultant((x^2 - a - c^2*b)^2 - 4*c^2*a*b, t^2 - 241, t);
    if(poldegree(P) == 8 && polisirreducible(P), break));
  if(poldegree(P) != 8 || !polisirreducible(P), error("bad P"));
  F = subst(polredbest(P), x, y);
  bnf = bnfinit(F, 1); nf = bnf.nf;
  my(roots241 = nfroots(nf, x^2 - 241), ok = 0, ra, rb);
  for(i = 1, #roots241, s = lift(roots241[i]);
    aF = lift(Mod(subst(lift(a), t, s), F)); bF = lift(Mod(subst(lift(b), t, s), F));
    ra = nfroots(nf, x^2 - aF); rb = nfroots(nf, x^2 - bF);
    if(#ra && #rb, ok = 1; break));
  if(!ok, error("F0 does not contain sqrt a, sqrt b"));
  sa = lift(ra[1]); sb = lift(rb[1]);
  AU = nfgaloisconj(nf);
  for(i = 1, #AU, g = AU[i]; e0 = ap(F, g, s) == s; e1 = ap(F, g, sa) == sa; e2 = ap(F, g, sb) == sb;
     if(e0, if(!e1 && e2, Sa = g); if(e1 && !e2, Sb = g); if(!e1 && !e2, Sab = g)));
  if(Sa == 0 || Sb == 0 || Sab == 0, error("automorphisms not found"));
  gs = [Sa, Sb, Sab];
  S = concat([idealprimedec(nf, 2), idealprimedec(nf, 3), idealprimedec(nf, 5)]);
  su = bnfunits(bnf, S);
  H = apply(z -> lift(nfbasistoalg(nf, nffactorback(nf, z))), su[1]);
  n = #H;
  for(j = 1, n, if(dlog(bnf, su, n, H[j]) != matid(n)[, j], error(Str("dlog basis check failed at ", j))));
  Ma = matrix(n, n, i, j, dlog(bnf, su, n, ap(F, Sa, H[j]))[i]);
  Mb = matrix(n, n, i, j, dlog(bnf, su, n, ap(F, Sb, H[j]))[i]);
  Inv = matker(Mod(matconcat([Ma - 1; Mb - 1]), 2));
  T = matrix(3, #Inv); bel = vector(#Inv);
  for(j = 1, #Inv, e = lift(Inv[, j]); z = 1;
     for(i = 1, n, if(e[i], z = lift(Mod(z * H[i], F))));
     bel[j] = z; rr = tpat(F, nf, gs, z); for(i = 1, 3, T[i, j] = rr[i]));
  tgt = [rho == [1,0], rho == [0,1], rho == [1,1]]~;
  sol = matsolvemod(T, 2, tgt);
  if(sol === 0, return([0, "no S-unit solution", T, #Inv, n]));
  sol = lift(Mod(sol, 2));
  bas = [1, s, sa, s*sa, sb, s*sb, sa*sb, s*sa*sb];
  M = matrix(8, 8, i, j, polcoef(lift(Mod(bas[j], F)), i - 1, y));
  my(Ker = lift(matker(Mod(T, 2))), best = 0, bsz = 0, cand, cco, sz);
  forvec(w = vector(#Ker, i, [0, 1]),
    my(ss = lift(Mod(sol + Ker * w~, 2)));
    cand = 1; for(j = 1, #Inv, if(ss[j], cand = lift(Mod(cand * bel[j], F))));
    cco = matsolve(M, vector(8, i, polcoef(cand, i - 1, y))~);
    sz = vecmax(apply(c -> max(abs(numerator(c)), denominator(c)), cco));
    if(best == 0 || sz < bsz, best = cand; bsz = sz; co = cco));
  beta = best;
  [beta, co, tpat(F, nf, gs, beta), F, #Inv, n, T]
}
