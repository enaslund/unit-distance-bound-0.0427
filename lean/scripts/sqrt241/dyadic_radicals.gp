\\ Explicit dyadic ramified directions of the tower over B = Q(sqrt 241).
\\ Reproduce: gp -q scripts/sqrt241/dyadic_radicals.gp < /dev/null
\\ Kummer basis (0-based): a0=-1, a1=eps, a2=pi2, a3=pi2', a4=pi3, a5=pi3', a6=pi5, a7=pi5'.
\\ The functional x3*x5 (resp. (x0+x2)*x4) of the relation annihilator detects the local
\\ commutator [y,z] at the first (resp. second) dyadic prime; it is realized by the D4
\\ extension B(sqrt a, sqrt b, sqrt beta) with beta in B(sqrt a), N(beta) = b.
default(parisize,"4G");
K = bnfinit(y^2 - 241, 1);
P2 = idealprimedec(K,2);
p2 = (-6101 - 393*y)/2; p2p = (6101 - 393*y)/2; p3 = 31 - 2*y; p3p = 31 + 2*y;
print("valuations of pi2 at the two dyadic primes: ", [nfeltval(K,p2,P2[1]), nfeltval(K,p2,P2[2])]);
T1 = rnfisnorminit(K, x^2 - p2p); r1 = rnfisnorm(T1, p3p, 100);
T2 = rnfisnorminit(K, x^2 + p2);  r2 = rnfisnorm(T2, p3, 100);
print("beta1 (in B(sqrt pi2'), x = sqrt pi2'): ", lift(r1[1]), "   q = ", r1[2]);
print("beta2 (in B(sqrt -pi2), x = sqrt -pi2): ", lift(r2[1]), "   q = ", r2[2]);
\\ absolute models: s = sqrt(pi2'), sqrt241 = (6101 - 2 s^2)/393
f4 = y^4 - 6101*y^2 - 2; Y = (6101 - 2*y^2)/393;
beta1 = Mod((2*Y - 25) + (-9*Y - 139)*y, f4); p3pm = Mod(31 + 2*Y, f4);
b1c = Mod(subst(lift(beta1), y, -y), f4);
print("N(beta1) = pi3': ", lift(beta1*b1c) == lift(p3pm));
nf4 = nfinit([f4, [2,3,5,241]]);
f16 = polredbest(rnfequation(nf4, x^4 - 2*(beta1+p3pm)*x^2 + (beta1-p3pm)^2));
nf16 = nfinit([subst(f16,x,y), [2,3,5,241]]);
P = idealprimedec(nf16, 2);
print("F16 = B(sqrt pi2', sqrt pi3', sqrt beta1): disc ", factor(abs(nf16.disc)), "; 2-primes (e,f) ", vector(#P,i,[P[i].e,P[i].f]), "; v(diff) ", vector(#P,i,idealval(nf16,nf16.diff,P[i])));
f32 = polredbest(rnfequation(nf16, x^2 - 2));
nf32 = nfinit([f32, [2,3,5,241]]);
Q = idealprimedec(nf32, 2);
print("F32 = F16(sqrt 2): disc ", factor(abs(nf32.disc)), "; 2-primes (e,f) ", vector(#Q,i,[Q[i].e,Q[i].f]), "; v(diff)/e ", vector(#Q,i,idealval(nf32,nf32.diff,Q[i])/Q[i].e));
quit
