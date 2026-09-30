\\ lvalues255.gp -- compares PARI/GP values of the 255 L-values with the
\\ enclosures of afe241.py.
\\
\\ For e in F_2^8 \ {0} let alpha_e = prod alpha_i^{e_i}, B_e = B(sqrt(alpha_e)),
\\ B = Q(sqrt 241), and L(s, chi_e) = zeta_{B_e}(s)/zeta_B(s). The file
\\ afe241_301_300.json, written by afe241.py, records for each e an interval
\\ containing L(301/300, chi_e), obtained from a certified approximate
\\ functional equation in ball arithmetic (its endpoints are stored as
\\ double-precision numbers), and an enclosure of (1/512) log zeta_E(301/300),
\\ where E = B(sqrt(alpha_0), ..., sqrt(alpha_7)).
\\
\\ This program evaluates the same values numerically with PARI's own
\\ L-function package, which is independent of afe241.py, and checks:
\\   * that each PARI value L(301/300, chi_e) lies in the recorded interval;
\\   * the functional equation of each zeta_{B_e}, with PARI's own test
\\     (the largest value of lfuncheckfeq is printed, in bits; -121 means
\\     agreement to 2^-121, and PASS requires at most -100);
\\   * that the PARI value of (1/512) log zeta_E(301/300), computed as
\\     (log zeta_B + sum over e of log L(301/300, chi_e))/512, lies in the
\\     recorded enclosure.
\\ It also prints the smallest and largest recorded endpoints and the largest
\\ relative width of the 255 intervals. PARI's values carry no error bound;
\\ this is a consistency check, not part of the certified evaluation.
\\
\\ Run from the certificates directory:  gp -q lvalues255.gp
\\ It takes a few minutes. The last line printed is "lvalues255: PASS" or
\\ "lvalues255: FAIL".

default(parisizemax, "4G");
default(realprecision, 38);

\\ The Kummer basis alpha_0, ..., alpha_7 of the paper, with y = sqrt(241).
B = nfinit(y^2 - 241);
ALPHA = [-1, -71011068 + 4574225*y, (-6101 - 393*y)/2, (6101 - 393*y)/2, 31 - 2*y, 31 + 2*y, 326 - 21*y, 326 + 21*y];
alpha(e) = lift(prod(i = 1, 8, if (bittest(e, i - 1), Mod(ALPHA[i], y^2 - 241), 1)));

\\ The text of s between the first occurrence of key and the next occurrence of stop.
field(s, key, stop) = strsplit(strsplit(s, key)[2], stop)[1];

\\ Read afe241_301_300.json: the enclosure of (1/512) log zeta_E and the rows [e, lo, hi].
{
  my(L = iferr(readstr("afe241_301_300.json"), E, 0));
  if (L === 0,
    print("afe241_301_300.json not found: run this program in the certificates directory.");
    quit);
  my(s = concat(L));
  my(ends = strsplit(field(s, "\"normalized_log_zeta_EB\": [", "],"), "\"["));
  YLO = eval(strsplit(ends[2], " +/-")[1]);
  YHI = eval(strsplit(ends[3], " +/-")[1]);
  my(pieces = strsplit(s, "\"label\": \"e="));
  ROWS = vector(#pieces - 1, k,
    my(p = pieces[k + 1], v = eval(concat(["[", field(p, "\"L\": [", "]"), "]"])));
    [eval(strsplit(p, "\"")[1]), v[1], v[2]]);
  print("rows read from afe241_301_300.json: ", #ROWS);
}

{
  my(sigma = 301/300, LB = lfuncreate(x^2 - 241), zB = lfun(LB, sigma));
  my(total = log(zB), nout = 0, worst = lfuncheckfeq(LB), seen = vector(255));
  for (k = 1, #ROWS,
    my(e = ROWS[k][1], lo = ROWS[k][2], hi = ROWS[k][3]);
    my(Le = lfuncreate(polredbest(rnfequation(B, x^2 - alpha(e)))));
    my(v = lfun(Le, sigma) / zB);
    worst = max(worst, lfuncheckfeq(Le));
    if (!(lo < v && v < hi),
      nout++;
      print("OUTSIDE e=", e, ": PARI value ", v, " not in [", lo, ", ", hi, "]"));
    seen[e]++;
    total += log(v));
  my(ypari = total / 512, yin = (YLO < ypari && ypari < YHI));
  my(los = vector(#ROWS, k, ROWS[k][2]), his = vector(#ROWS, k, ROWS[k][3]));
  my(width = vecmax(vector(#ROWS, k, (his[k] - los[k]) / los[k])));
  print("values outside their recorded intervals: ", nout, " of ", #ROWS);
  print("largest lfuncheckfeq over zeta_B and the 255 zeta_{B_e}: ", worst, " bits");
  print("recorded intervals: smallest endpoint ", vecmin(los), ", largest endpoint ", vecmax(his), ", largest relative width ", width);
  print("PARI value of (1/512) log zeta_E(301/300): ", ypari);
  print("certified enclosure from afe241.py: [", YLO, ", ", YHI, "]; PARI value inside: ", yin);
  my(ok = (nout == 0) && yin && (#ROWS == 255) && (seen == vector(255, e, 1)) && (worst <= -100));
  print(if (ok, "lvalues255: PASS", "lvalues255: FAIL"));
}
quit
