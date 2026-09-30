\\ Exact PARI/GP computation for K = B(\u221aη), with
\\ B = Q(√−35), η = 17 + 2√−35, and x^2 = η.
\\ Run from GP as: gp -q h6-plus-quartic-local-factors.gp
\\ A guarded PASS run is recorded in h6-plus-quartic-pari-receipt-20260923.json.
\\ That receipt pins the exact source SHA used for the run; this status comment
\\ was refreshed afterward and does not change any executable GP statements.

{
  my(x = 'x, y = 'y, T = 'T);
  my(P = x^4 - 34*x^2 + 429);
  my(B, nf, cert, baseDec, topDec, baseDen, topDen, qr, Qp);
  my(primes = [2, 3, 5, 7, 11, 13, 17]);
  my(expected = [1, 1-T, 1+T, 1+T, 1-T, 1+T, (1-T)^2]);
  my(i, j, p, expectedQ);

  if (!polisirreducible(P), error("quartic polynomial is reducible"));

  \\ Let alpha be a root of P and y=(alpha^2-17)/2. Then y^2=-35
  \\ and alpha^2=17+2y, identifying Q(alpha) with
  \\ Q(sqrt(-35), sqrt(17+2sqrt(-35))).
  B = nfinit(y^2 + 35);
  if (B.disc != -35, error("unexpected base-field discriminant"));
  if (#nfcertify(B) != 0, error("base nfinit data did not certify"));

  \\ Certify the maximal order and its field discriminant. nf.index is
  \\ [O_K : Z[alpha]], where alpha is a root of P.
  nf = nfinit(P);
  cert = nfcertify(nf);
  if (#cert != 0, error("quartic nfinit data did not certify"));
  if (nf.sign != [0, 2], error("unexpected quartic signature"));
  \\ These are predicted for the plus field from Q=240240 and
  \\ |disc(B)|=35: |disc(K)|=35*240240=8408400, with index 16.
  \\ The exact PARI data below test these predictions; they are not
  \\ assumed to be computation results.
  if (nf.disc != 8408400, error("unexpected quartic field discriminant"));
  if (nf.index != 16, error("unexpected power-order index"));
  if (poldisc(P) != nf.disc * nf.index^2,
      error("polynomial discriminant/index identity failed"));
  print("P = ", P);
  print("polynomial discriminant = ", poldisc(P));
  print("field discriminant = ", nf.disc);
  print("power-order index = ", nf.index);
  print("integral basis = ", nf.zk);

  \\ At p, if q runs over primes of B and P runs over primes of K, then
  \\ ζ_K/ζ_B has local factor
  \\   prod_q (1 - T^f(q/p)) / prod_P (1 - T^f(P/p)).
  \\ Thus Q_p(T), its reciprocal Euler denominator polynomial, is the
  \\ exact quotient topDen/baseDen. Compute both decompositions directly
  \\ in the certified absolute maximal orders; the .f entries are residue
  \\ degrees over Q, which are the exponents used here.
  for (i = 1, #primes,
    p = primes[i];
    baseDec = idealprimedec(B, p);
    topDec = idealprimedec(nf, p);
    baseDen = 1;
    topDen = 1;
    for (j = 1, #baseDec, baseDen *= 1 - T^baseDec[j].f);
    for (j = 1, #topDec, topDen *= 1 - T^topDec[j].f);
    qr = divrem(topDen, baseDen);
    if (qr[2] != 0, error("Euler quotient is not a polynomial at p = ", p));
    Qp = qr[1];
    expectedQ = expected[i];
    print("p = ", p,
      "; base residue degrees = ", vector(#baseDec, j, baseDec[j].f),
      "; quartic residue degrees = ", vector(#topDec, j, topDec[j].f),
      "; Q_p(T) = ", Qp);
    if (Qp != expectedQ, error("H6 twist+1 table mismatch at p = ", p));
  );

  print("PASS: seven exact local quotient polynomials match the pinned H6 twist+1 row.");
}
