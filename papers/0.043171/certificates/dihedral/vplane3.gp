\\ Verification of the five D4 fields of W' (orbits 10, 23, 24, 19, 20 of d4all27.json; GP indices 11, 24, 25, 20, 21):
\\ S-unit beta, D4 pattern with the stated rotation class, F0(sqrt beta)/F0 unramified outside S (as vd4.gp).
read("../vd4lib.gp");
read("vd4_data27.gp");
NOK = 0; SEL = [11, 24, 25, 20, 21];
{
  for(jj = 1, #SEL, my(j = SEL[jj], f = FIELDS[j], r = vd4(f[1], f[2], f[3], f[4]));
    NOK++; print("orbit ", j - 1, ": t ", r[1], "  N(disc) ", r[2], "  degree ", r[3]));
}
if(NOK == 5, print("vplane3: PASS orbits 10, 23, 24, 19, 20"), print("vplane3: FAIL"));
