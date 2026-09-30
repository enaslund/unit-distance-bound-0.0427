\\ Stream E (root discriminant): dyadic certificate for the prime above p1 = (pi2).
\\ Reproduce: gp -q scripts/sqrt241/dyadic_certificate.gp < /dev/null > /tmp/cert.txt
\\
\\ F = Q(r, t, g, s) with r^2 = 241, t^2 = 2, g^2 = pi2'(r) = (6101 - 393 r)/2,
\\ s^2 = beta1 = (-25 + 2 r) + (-139 - 9 r) g   (degree 16).
\\ Its prime Q above p1 has e = 8, f = 1 and different exponent 18.
\\ y = explicit generator of Q (norm 2); f = charpoly(y) (monic, Z-coefficients),
\\ f = X^8 G + 2 Kp with Kp(0) = 1, f' = X^18 Z + f W with Z(0) odd,
\\ u = y^8 / pi2 (a unit), h = charpoly(u).
\\ Coordinates are with respect to r^a t^b g^c s^d, index a + 2b + 4c + 8d.
default(parisize,"4G");
F = y^16 - 16*y^14 + 74*y^12 - 96*y^10 + 93*y^8 - 1528*y^6 + 3620*y^4 - 1448*y^2 + 900;
nf = nfinit([F,[2,3,5,241]]);
rr = nfroots(nf, x^2-241);
r = 0; for(i=1,#rr, if(#nfroots(nf, x^2 - (6101 - 393*rr[i])/2) > 0, r = rr[i]));
t = nfroots(nf, x^2-2)[1];
pi2 = (-6101 - 393*r)/2; pi2p = (6101 - 393*r)/2;
g = nfroots(nf, x^2 - pi2p)[1];
beta1 = (-25 + 2*r) + (-139 - 9*r)*g;
s = nfroots(nf, x^2 - beta1)[1];
Pd = idealprimedec(nf, 2); Q = Pd[1];
B = vector(16, k, my(a=(k-1)%2, b=((k-1)\2)%2, c=((k-1)\4)%2, d=((k-1)\8)%2); r^a * t^b * g^c * s^d);
M = matrix(16,16,i,j, polcoeff(lift(B[j]), i-1));
coords(z) = matsolve(M, vector(16,i,polcoeff(lift(z),i-1))~);
cb = [201/8, 13/8, 20, 5/4, -1599/8, -103/8, 885/16, 57/16, 191/8, -9/8, 1, 1/4, 175/8, 11/8, -1227/16, -79/16];
yy = sum(k=1,16, cb[k]*B[k]);
f = charpoly(yy);
fp = deriv(f);
Kp = sum(i=0,7, polcoeff(f,i)/2 * x^i);
G = (f - 2*Kp)/x^8;
Xinv = Mod(-(f - polcoeff(f,0))/x / polcoeff(f,0), f);
Z = lift(Mod(fp,f) * Xinv^18);
W = (fp - x^18*Z)/f;
uu = yy^8/pi2;
h = charpoly(uu);
uc = coords(uu);
\\ sanity checks
if(norm(yy) != 2 || nfeltval(nf, yy, Q) != 1 || Q.e != 8 || Q.f != 1, error("generator"));
if(idealval(nf, nf.diff, Q) != 18, error("different"));
if(polcoeff(Kp,0) != 1 || polcoeff(Z,0) % 2 != 1, error("units"));
if(denominator(content(Z)) != 1 || denominator(content(W)) != 1 || denominator(content(h)) != 1, error("integrality"));
if(fp - x^18*Z - f*W != 0 || f - x^8*G - 2*Kp != 0, error("identities"));
if(subst(f, x, yy) != 0 || subst(h, x, uu) != 0 || pi2*uu != yy^8, error("model"));
\\ output (coefficient lists, constant term first)
L(p) = Vec(Polrev(Vec(p)));
lst(p) = my(v = Vecrev(p)); Str(v);
fr(q) = if(denominator(q)==1, Str(q), Str("(", numerator(q), "/", denominator(q), ")"));
elt(c) = Str("⟨⟨⟨⟨", fr(c[1]), ", ", fr(c[2]), "⟩, ⟨", fr(c[3]), ", ", fr(c[4]), "⟩⟩, ⟨⟨", fr(c[5]), ", ", fr(c[6]), "⟩, ⟨", fr(c[7]), ", ", fr(c[8]), "⟩⟩⟩, ⟨⟨⟨", fr(c[9]), ", ", fr(c[10]), "⟩, ⟨", fr(c[11]), ", ", fr(c[12]), "⟩⟩, ⟨⟨", fr(c[13]), ", ", fr(c[14]), "⟩, ⟨", fr(c[15]), ", ", fr(c[16]), "⟩⟩⟩⟩");
print("yM := ", elt(cb));
print("uM := ", elt(uc));
print("fL := ", lst(f));
print("hL := ", lst(h));
print("GL := ", lst(G));
print("KpL := ", lst(Kp));
print("ZL := ", lst(Z));
print("WL := ", lst(W));
