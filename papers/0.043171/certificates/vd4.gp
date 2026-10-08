\\ Verification of the fifteen D4 fields of d4fields15.json (data in vd4_data.gp, written by d4fields.py).
\\ For each field, with F0 = B(sqrt a, sqrt b) built by two relative equations (independently of the
\\ search in d4beta.gp) and beta given by its coordinates:
\\   (1) beta is an S-unit of F0 (its ideal factorization involves only primes above 2, 3, 5);
\\   (2) for each sigma != 1 in Gal(F0/B), sigma(beta)/beta = u^2 is a square, and t = u sigma(u) = +-1,
\\       with t = -1 exactly for the sigma acting by (-1)^rho on (sqrt a, sqrt b): F0(sqrt beta)/B is
\\       Galois with group D4 and rotation class rho;
\\   (3) the relative discriminant of F0(sqrt beta)/F0 has norm divisible only by 2, 3, 5.
\\ Writes mtilde15.gp: absolute polynomials of the fields F0(sqrt beta) (degree 16), for rootcheck.py.
read("vd4lib.gp");
read("vd4_data.gp");
MP = vector(#FIELDS); NOK = 0;
{
  for(j = 1, #FIELDS,
    my(f = FIELDS[j], r = vd4(f[1], f[2], f[3], f[4]));
    MP[j] = r[4]; NOK++;
    print("field ", j, ": t ", r[1], "  N(disc) ", r[2], "  degree ", r[3]));
}
system("rm -f mtilde15.gp");    \\ write() appends
write("mtilde15.gp", "MP = ", MP, ";");
if(NOK == 15 && #FIELDS == 15, print("vd4: PASS all 15 fields"), print("vd4: FAIL"));
