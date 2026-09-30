\\ check255.gp -- checks all 255 rows of lrows241.json against PARI/GP.
\\
\\ For e in F_2^8 \ {0} let alpha_e = prod alpha_i^{e_i}, B_e = B(sqrt(alpha_e)),
\\ B = Q(sqrt 241), and let chi_e be the quadratic character of B_e/B.
\\ The file lrows241.json, written by lfun241.py, records for each e the
\\ conductor Q_e = 241 N(f_e) of L(s, chi_e) = zeta_{B_e}(s)/zeta_B(s), its
\\ gamma type, a cutoff N_e and the Dirichlet coefficients a_1, ..., a_{N_e}.
\\ These rows are the input of the certified evaluation afe241.py.
\\
\\ For every row this program computes, independently, with PARI's number
\\ field and L-function routines:
\\   * the discriminant of the maximal order of B_e, and checks
\\     |disc(B_e)| = 241 * Q_e (conductor-discriminant formula);
\\   * the signature of B_e, and checks the gamma type: "pure0" (Gamma_R(s)^2)
\\     means B_e totally real, "pure1" (Gamma_R(s+1)^2) totally imaginary,
\\     "quadratic" (Gamma_R(s) Gamma_R(s+1)) two real places;
\\   * the Dirichlet coefficients of zeta_{B_e}/zeta_B up to N_e, and checks
\\     that they equal the recorded a_1, ..., a_{N_e}.
\\ It then prints the number of characters of each gamma type, the table of
\\ conductors by 2-part and odd part of Q_e/241, and the ranges of Q_e, N_e
\\ and t (N_e + 1), where t = 2 pi / sqrt(Q_e).
\\
\\ Run from the certificates directory, after lfun241.py has written
\\ lrows241.json:  gp -q check255.gp
\\ The last line printed is "check255: PASS" or "check255: FAIL".

default(parisizemax, "4G");

\\ The Kummer basis alpha_0, ..., alpha_7 of the paper, with y = sqrt(241).
B = nfinit(y^2 - 241);
ALPHA = [-1, -71011068 + 4574225*y, (-6101 - 393*y)/2, (6101 - 393*y)/2, 31 - 2*y, 31 + 2*y, 326 - 21*y, 326 + 21*y];
print("norms of alpha_0, ..., alpha_7: ", vector(8, i, norm(Mod(ALPHA[i], y^2 - 241))));
alpha(e) = lift(prod(i = 1, 8, if (bittest(e, i - 1), Mod(ALPHA[i], y^2 - 241), 1)));

\\ The text of s between the first occurrence of key and the next occurrence of stop.
field(s, key, stop) = strsplit(strsplit(s, key)[2], stop)[1];

\\ Read lrows241.json and split it into rows [e, kind, Q_e, N_e, coefficients].
{
  my(L = iferr(readstr("lrows241.json"), E, 0));
  if (L === 0,
    print("lrows241.json not found: run lfun241.py in this directory first.");
    quit);
  my(pieces = strsplit(concat(L), "{\"label\": \"e="));
  ROWS = vector(#pieces - 1, k,
    my(p = pieces[k + 1]);
    [eval(strsplit(p, "\"")[1]),
     field(p, "\"kind\": \"", "\""),
     eval(field(p, "\"conductor\": ", ",")),
     eval(field(p, "\"N\": ", ",")),
     eval(concat(["[", field(p, "\"coefficients\": [", "]"), "]"]))]);
  print("rows read from lrows241.json: ", #ROWS);
}

{
  my(nmax = vecmax(vector(#ROWS, k, ROWS[k][4])));
  my(ab = lfunan(lfuncreate(x^2 - 241), nmax));    \\ coefficients of zeta_B
  my(two = [1, 4, 8, 16, 32, 64], odd = [1, 3, 5, 9, 15, 25, 45, 75, 225]);
  my(table = matrix(#two, #odd), kinds = ["pure0", "quadratic", "pure1"], count = [0, 0, 0]);
  my(nbad = 0, seen = vector(255));
  for (k = 1, #ROWS,
    my(r = ROWS[k], e = r[1], kind = r[2], Q = r[3], N = r[4], a = r[5]);
    my(P = polredbest(rnfequation(B, x^2 - alpha(e))), nf = nfinit(P));
    my(r1 = nf.sign[1], kindQ = if (r1 == 4, "pure0", r1 == 2, "quadratic", "pure1"));
    my(aQ = lfunan(lfuncreate(P), N), c = vector(N));
    for (n = 1, N,
      my(t = aQ[n]);
      fordiv(n, d, if (d < n, t -= c[d] * ab[n / d]));
      c[n] = t);
    my(ok = (abs(nf.disc) == 241 * Q) && (kindQ == kind) && (#a == N + 1) && (a[1] == 0) && (c == a[2 .. N + 1]));
    if (!ok,
      nbad++;
      print("MISMATCH e=", e, ": |disc|/241 = ", abs(nf.disc) / 241, " vs Q_e = ", Q, ", signature type ", kindQ, " vs ", kind));
    seen[e]++;
    count[select(z -> z == kindQ, kinds, 1)[1]]++;
    my(m = Q / 241, m2 = 2^valuation(m, 2));
    my(i = select(z -> z == m2, two, 1), j = select(z -> z == m / m2, odd, 1));
    if (#i == 1 && #j == 1,
      table[i[1], j[1]]++,
      nbad++; print("conductor outside the table: e=", e)));
  if (seen != vector(255, e, 1), nbad++; print("not every e in 1..255 occurs exactly once"));
  print("rows checked: ", #ROWS, ", mismatches: ", nbad);
  print("gamma types from the signatures of B_e: Gamma_R(s)^2: ", count[1], ", Gamma_R(s)Gamma_R(s+1): ", count[2], ", Gamma_R(s+1)^2: ", count[3]);
  print("number of e by 2-part (rows ", two, ") and odd part (columns ", odd, ") of Q_e/241:");
  printp(table);
  print("row sums: ", vector(#two, i, vecsum(table[i, ])), "; column sums: ", vector(#odd, j, vecsum(table[, j])));
  my(qs = vector(#ROWS, k, ROWS[k][3]), ns = vector(#ROWS, k, ROWS[k][4]));
  my(ts = vector(#ROWS, k, 2 * Pi * (ns[k] + 1) / sqrt(qs[k])));
  my(cut = vector(#ROWS, k, ns[k] == 4 * sqrtint(qs[k]) + 1) == vector(#ROWS, k, 1));
  print("range of Q_e: [", vecmin(qs), ", ", vecmax(qs), "]; range of N_e: [", vecmin(ns), ", ", vecmax(ns), "]");
  print("N_e = 4 floor(sqrt(Q_e)) + 1 for every e: ", cut);
  print("range of t (N_e + 1): [", vecmin(ts), ", ", vecmax(ts), "]");
  print(if (nbad == 0 && #ROWS == 255 && cut, "check255: PASS", "check255: FAIL"));
}
quit
