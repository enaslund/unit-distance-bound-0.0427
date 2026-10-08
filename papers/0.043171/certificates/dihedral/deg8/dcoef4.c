/* dcoef4.c: Dirichlet coefficients of the 64 twisted dihedral L-functions L_w = zeta(K_w)/zeta(Bc) of one D4 field
 * (export of deg8/exportg.gp; the rule of dcoeffs.py) and, for every twist, the per-cell kernel moments
 *
 *     M_ij = sum_{n in cell i} a_n u_n^j,  u_n = x_n / c_i - 1,  x_n = (t n)^d  (j = 0..D),   A_i = sum |a_n|,
 *
 * cell i = {nb[i+1] < n <= nb[i]} (gkernel.py grid of the twist's gamma type).  Kahan sums in double.
 *
 * Coefficients: Euler factors at p <= PSMALL from PARI; for PSMALL < p (p^2 > N, only a_p enters), at each degree-one
 * prime P = (p, sqrt241 - r) of B with G_i = g_i(r) alpha^w(r):  c(r) a square: a_P = (G0 + G1 sc | p) + (G0 - G1 sc | p);
 * c(r) a nonsquare: a_P = 0 (one prime of norm p^2).  A vanishing symbol (gamma_w not a unit at a prime of Bc above P)
 * is fatal: rerun with a larger PSMALL.  The rule is compared with PARI at every unramified 1000 < p <= PSMALL.
 *
 * Usage: dcoef4 INPUT OUTPUT        (NTW <= 64 twists of one gamma grid per run)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

typedef unsigned __int128 u128;
#define MAXTW 64
static int NTW;                                       /* number of twists in this run (<= 64) */
#define MAXD 24
#define MAXCELL 2048

static void die(const char *m, long long v) { fprintf(stderr, "dcoef4: %s (%lld)\n", m, v); exit(2); }
static inline uint64_t mulm(uint64_t a, uint64_t b, uint64_t p) { return (uint64_t)((u128)a * b % p); }
static uint64_t powm(uint64_t a, uint64_t e, uint64_t p) {
    uint64_t r = 1 % p; a %= p;
    while (e) { if (e & 1) r = mulm(r, a, p); a = mulm(a, a, p); e >>= 1; }
    return r;
}
static int jac(uint64_t a, uint64_t n) {
    a %= n; int t = 1;
    while (a) {
        while (!(a & 1)) { a >>= 1; uint64_t r = n & 7; if (r == 3 || r == 5) t = -t; }
        uint64_t x = a; a = n; n = x;
        if ((a & 3) == 3 && (n & 3) == 3) t = -t;
        a %= n;
    }
    return n == 1 ? t : 0;
}
static uint64_t sqrtm(uint64_t a, uint64_t p) {
    a %= p;
    if ((p & 3) == 3) return powm(a, (p + 1) / 4, p);
    if ((p & 7) == 5) {
        uint64_t v = powm(2 * a % p, (p - 5) / 8, p);
        uint64_t i = mulm(mulm(2 * a % p, v, p), v, p);
        return mulm(mulm(a, v, p), (i + p - 1) % p, p);
    }
    uint64_t q = p - 1; int s = 0; while (!(q & 1)) { q >>= 1; s++; }
    uint64_t z = 2; while (jac(z, p) != -1) z++;
    uint64_t c = powm(z, q, p), x = powm(a, (q + 1) / 2, p), t = powm(a, q, p); int m = s;
    while (t != 1) {
        int i = 0; uint64_t tt = t; while (tt != 1) { tt = mulm(tt, tt, p); i++; if (i == m) die("sqrtm", (long long)p); }
        uint64_t b = c; for (int j = 0; j < m - i - 1; j++) b = mulm(b, b, p);
        x = mulm(x, b, p); c = mulm(b, b, p); t = mulm(t, c, p); m = i;
    }
    return x;
}
#define MAXL 16
typedef struct { int sa, sb, la, lb; uint64_t a[MAXL], b[MAXL]; uint64_t den; } belt;
static void parse_big(const char *s, int *sg, int *len, uint64_t *limb) {
    *sg = 1; if (*s == '-') { *sg = -1; s++; } else if (*s == '+') s++;
    uint64_t L[MAXL] = {0}; int n = 1;
    for (; *s >= '0' && *s <= '9'; s++) {
        u128 carry = (uint64_t)(*s - '0');
        for (int i = 0; i < n; i++) { u128 v = (u128)L[i] * 10 + carry; L[i] = (uint64_t)v; carry = v >> 64; }
        if (carry) { if (n == MAXL) die("big integer too long", 0); L[n++] = (uint64_t)carry; }
    }
    *len = n; memcpy(limb, L, sizeof L);
}
static uint64_t big_mod(int sg, int len, const uint64_t *limb, uint64_t p) {
    u128 r = 0;
    for (int i = len - 1; i >= 0; i--) r = ((r << 64) | limb[i]) % p;
    uint64_t v = (uint64_t)r;
    return (sg < 0 && v) ? p - v : v;
}
static uint64_t belt_val(const belt *e, uint64_t r, uint64_t p) {
    uint64_t A = big_mod(e->sa, e->la, e->a, p), B = big_mod(e->sb, e->lb, e->b, p);
    uint64_t v = (A + mulm(B, r, p)) % p;
    if (e->den != 1) v = mulm(v, powm(e->den % p, p - 2, p), p);
    return v;
}
static void read_belt(FILE *f, belt *e) {
    char sa[400], sb[400]; unsigned long long den;
    if (fscanf(f, "%399s %399s %llu", sa, sb, &den) != 3) die("belt", 0);
    parse_big(sa, &e->sa, &e->la, e->a); parse_big(sb, &e->sb, &e->lb, e->b); e->den = den;
}
static void expect(FILE *f, const char *key) { char w[64]; if (fscanf(f, "%63s", w) != 1 || strcmp(w, key)) die(key, 0); }

static int D, DPOW, ncell, nsp;
static uint64_t PSMALL, NMAX, NW[MAXTW], *NB[MAXTW], *SP;
static double TW_T[MAXTW], CELLC[MAXCELL + 1];
static unsigned TWM[MAXTW];
static belt KB[8], CC, G0, G1;
static int64_t **APK, **PAR1; static int *KMAX, *PDEG;
static int qr241[241];

/* a_p(w), all twists, p > 1000 unramified odd */
static void ap_rule(uint64_t p, int64_t *ap) {
    for (int w = 0; w < NTW; w++) ap[w] = 0;
    if (!qr241[p % 241]) return;
    uint64_t r = sqrtm(241 % p, p);
    if (mulm(r, r, p) != 241 % p) die("sqrt241", (long long)p);
    for (int side = 0; side < 2; side++) {
        uint64_t rr = side ? p - r : r;
        uint64_t cv = belt_val(&CC, rr, p);
        int lc = jac(cv, p);
        if (lc == 0) die("c(r) = 0", (long long)p);
        if (lc != 1) continue;
        uint64_t sc = sqrtm(cv, p);
        if (mulm(sc, sc, p) != cv) die("sqrt c", (long long)p);
        uint64_t g0 = belt_val(&G0, rr, p), g1 = belt_val(&G1, rr, p);
        int chp = jac((g0 + mulm(g1, sc, p)) % p, p), chm = jac((g0 + p - mulm(g1, sc, p)) % p, p);
        if (chp == 0 || chm == 0) die("gamma not a unit at a prime of Bc (raise PSMALL)", (long long)p);
        unsigned vneg = 0;
        for (int k = 0; k < 8; k++) { int l = jac(belt_val(&KB[k], rr, p), p); if (l == 0) die("alpha_k = 0", (long long)p); if (l < 0) vneg |= 1u << k; }
        for (int w = 0; w < NTW; w++) ap[w] += ((__builtin_popcount(TWM[w] & vneg) & 1) ? -1 : 1) * (chp + chm);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: dcoef4 INPUT OUTPUT\n"); return 1; }
    for (int i = 1; i < 241; i++) qr241[(i * i) % 241] = 1;
    FILE *f = fopen(argv[1], "r"); if (!f) die("input", 0);
    int ntw; unsigned long long ps, nm;
    expect(f, "NTW"); if (fscanf(f, "%d", &ntw) != 1 || ntw < 1 || ntw > MAXTW) die("NTW", ntw); NTW = ntw;
    expect(f, "D"); if (fscanf(f, "%d", &D) != 1 || D < 4 || D >= MAXD) die("D", D);
    expect(f, "DPOW"); if (fscanf(f, "%d", &DPOW) != 1 || (DPOW != 1 && DPOW != 2)) die("DPOW", DPOW);
    expect(f, "PSMALL"); if (fscanf(f, "%llu", &ps) != 1) die("PSMALL", 0); PSMALL = ps;
    expect(f, "NMAX"); if (fscanf(f, "%llu", &nm) != 1) die("NMAX", 0); NMAX = nm;
    if ((u128)PSMALL * PSMALL <= NMAX) die("NMAX >= PSMALL^2", 0);
    expect(f, "KB"); for (int k = 0; k < 8; k++) read_belt(f, &KB[k]);
    expect(f, "C"); read_belt(f, &CC); expect(f, "G0"); read_belt(f, &G0); expect(f, "G1"); read_belt(f, &G1);
    expect(f, "CELLS"); if (fscanf(f, "%d", &ncell) != 1 || ncell < 2 || ncell > MAXCELL) die("CELLS", ncell);
    for (int i = 0; i <= ncell; i++) { char h[64]; if (fscanf(f, "%63s", h) != 1) die("cell", i); CELLC[i] = strtod(h, NULL); }
    expect(f, "TW");
    for (int w = 0; w < NTW; w++) {
        char th[64]; unsigned long long n;
        if (fscanf(f, "%u %63s %llu", &TWM[w], th, &n) != 3) die("TW", w);
        TW_T[w] = strtod(th, NULL); NW[w] = n; if (n > NMAX) die("N_w > NMAX", w);
        NB[w] = malloc(sizeof(uint64_t) * (ncell + 1));
        for (int i = 0; i <= ncell; i++) { unsigned long long v; if (fscanf(f, "%llu", &v) != 1) die("NB", i); NB[w][i] = v; }
        if (NB[w][0] != NW[w] || NB[w][ncell] != 0) die("NB ends", w);
        for (int i = 0; i < ncell; i++) if (NB[w][i + 1] > NB[w][i]) die("NB order", i);
    }
    expect(f, "EULER"); if (fscanf(f, "%d", &nsp) != 1) die("EULER", 0);
    SP = malloc(sizeof(uint64_t) * nsp); KMAX = malloc(sizeof(int) * nsp); PDEG = malloc(sizeof(int) * nsp);
    APK = malloc(sizeof(int64_t *) * nsp); PAR1 = malloc(sizeof(int64_t *) * nsp);
    for (int i = 0; i < nsp; i++) {
        unsigned long long p; if (fscanf(f, "%llu", &p) != 1) die("prime", i); SP[i] = p;
        int km = 1; { u128 pk = p; while (pk * p <= NMAX) { pk *= p; km++; } }
        KMAX[i] = km; PDEG[i] = 4;
        APK[i] = calloc((size_t)(km + 1) * NTW, sizeof(int64_t)); PAR1[i] = calloc(NTW, sizeof(int64_t));
        for (int w = 0; w < NTW; w++) {
            int d; long long P[9] = {0};
            if (fscanf(f, "%d", &d) != 1 || d < 0 || d > 8) die("degree", (long long)p);
            for (int j = 0; j <= d; j++) if (fscanf(f, "%lld", &P[j]) != 1) die("coeff", (long long)p);
            if (P[0] != 1) die("P(0)", (long long)p);
            if (d < PDEG[i]) PDEG[i] = d;
            PAR1[i][w] = -P[1];
            int64_t c[80] = {0}; c[0] = 1;
            for (int k = 1; k <= km; k++) { int64_t v = 0; for (int j = 1; j <= d && j <= k; j++) v -= P[j] * c[k - j]; c[k] = v; }
            for (int k = 0; k <= km; k++) APK[i][(size_t)k * NTW + w] = c[k];
        }
    }
    fclose(f);
    if (SP[nsp - 1] > PSMALL) die("Euler primes beyond PSMALL", 0);
    /* rule check */
    long nval = 0, nram = 0;
    for (int i = 0; i < nsp; i++) {
        uint64_t p = SP[i]; if (p <= 1000) continue;
        if (p == 241 || PDEG[i] < 4) { nram++; continue; }
        int64_t ap[MAXTW]; ap_rule(p, ap);
        for (int w = 0; w < NTW; w++) if (ap[w] != PAR1[i][w]) { fprintf(stderr, "p %llu w %d rule %lld PARI %lld\n", (unsigned long long)p, w, (long long)ap[w], (long long)PAR1[i][w]); die("rule disagrees with PARI", (long long)p); }
        nval++;
    }
    fprintf(stderr, "dcoef4: rule = PARI at %ld primes in (1000, %llu] (%ld ramified skipped)\n", nval, (unsigned long long)PSMALL, nram);
    /* smallest prime factors and a_p for PSMALL < p <= NMAX */
    uint32_t *spf = calloc(NMAX + 1, sizeof(uint32_t));
    for (uint64_t i = 2; i <= NMAX; i++) if (!spf[i]) { spf[i] = (uint32_t)i; if (i * i <= NMAX) for (uint64_t j = i * i; j <= NMAX; j += i) if (!spf[j]) spf[j] = (uint32_t)i; }
    int *pidx = calloc(PSMALL + 1, sizeof(int)); for (int i = 0; i < nsp; i++) pidx[SP[i]] = i;
    int8_t *apl = calloc((size_t)(NMAX + 1), 1);           /* per prime > PSMALL, one twist at a time: filled below */
    /* store a_p(w) for p > PSMALL as int8 per twist: compute once for all twists */
    uint64_t nlp = 0; for (uint64_t p = PSMALL + 1; p <= NMAX; p++) if (spf[p] == p) nlp++;
    uint64_t *LP = malloc(sizeof(uint64_t) * nlp); int8_t *LA = malloc((size_t)nlp * NTW); nlp = 0;
    for (uint64_t p = PSMALL + 1; p <= NMAX; p++) {
        if (spf[p] != p) continue;
        int64_t ap[MAXTW]; ap_rule(p, ap);
        LP[nlp] = p; for (int w = 0; w < NTW; w++) LA[nlp * NTW + w] = (int8_t)ap[w]; nlp++;
    }
    uint32_t *lpi = calloc(NMAX + 1, sizeof(uint32_t));
    for (uint64_t k = 0; k < nlp; k++) lpi[LP[k]] = (uint32_t)k;
    free(apl);
    FILE *fo = fopen(argv[2], "wb"); if (!fo) die("output", 0);
    int32_t hdr[4] = {NTW, D, ncell, 1}; fwrite(hdr, sizeof hdr, 1, fo);
    int64_t *a = malloc(sizeof(int64_t) * (NMAX + 1));
    for (int w = 0; w < NTW; w++) {
        uint64_t N = NW[w];
        a[1] = 1;
        for (uint64_t n = 2; n <= N; n++) {
            uint64_t p = spf[n], m = n; int k = 0; while (m % p == 0) { m /= p; k++; }
            int64_t ck;
            if (p <= PSMALL) { int ii = pidx[p]; if (SP[ii] != p || k > KMAX[ii]) die("small prime", (long long)p); ck = APK[ii][(size_t)k * NTW + w]; }
            else { if (k != 1) die("p^2 <= N for p > PSMALL", (long long)p); ck = LA[(size_t)lpi[p] * NTW + w]; }
            a[n] = ck * a[m];
        }
        /* moments */
        for (int i = 0; i < ncell; i++) {
            uint64_t lo = NB[w][i + 1] + 1, hi = NB[w][i];
            double S[MAXD] = {0}, C[MAXD] = {0}; uint64_t A = 0, cnt = 0;
            for (uint64_t n = lo; n <= hi && hi >= lo; n++) {
                if (!a[n]) continue;
                double x = TW_T[w] * (double)n; if (DPOW == 2) x = x * x;
                double u = x / CELLC[i] - 1.0, pw = 1.0, av = (double)a[n];
                for (int j = 0; j <= D; j++) {
                    double y = av * pw - C[j], t = S[j] + y;
                    C[j] = (t - S[j]) - y; S[j] = t; pw *= u;
                }
                A += (uint64_t)(a[n] < 0 ? -a[n] : a[n]); cnt++;
            }
            double M[MAXD]; for (int j = 0; j <= D; j++) M[j] = S[j] - C[j];
            fwrite(&cnt, sizeof cnt, 1, fo); fwrite(&A, sizeof A, 1, fo); fwrite(M, sizeof(double), D + 1, fo);
        }
        /* sum |a_p| p^-beta for PSMALL < p <= N (Rankin), beta = 1.05, 1.1, 1.2, 1.5 */
        double rk[4] = {0}; const double BT[4] = {1.05, 1.1, 1.2, 1.5};
        for (uint64_t k = 0; k < nlp && LP[k] <= N; k++) { int v = LA[k * NTW + w]; if (v) for (int b = 0; b < 4; b++) rk[b] += abs(v) * pow((double)LP[k], -BT[b]); }
        fwrite(rk, sizeof(double), 4, fo);
    }
    uint64_t tots[4] = {nlp, 0, 0, 0}; fwrite(tots, sizeof tots, 1, fo);
    int32_t ne = 0; fwrite(&ne, sizeof ne, 1, fo);
    fclose(fo);
    fprintf(stderr, "dcoef4: wrote %s (N_max %llu, %llu primes > PSMALL)\n", argv[2], (unsigned long long)NMAX, (unsigned long long)nlp);
    return 0;
}
