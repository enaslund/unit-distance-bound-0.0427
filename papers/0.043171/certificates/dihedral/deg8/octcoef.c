/* octcoef.c: Dirichlet coefficients of the 16 degree-8 L-functions L(s, rho_19 (x) rho_O (x) lambda_w) of one family
 * (deg8/export8.gp) and, for every twist, the per-cell kernel moments
 *
 *     M_ij = sum_{n in cell i} a_n u_n^j,   u_n = t n / c_i - 1  (j = 0..D),   A_i = sum_{n in cell i} |a_n|,
 *
 * cell i = {nb[i+1] < n <= nb[i]} of the conductor group of the twist (x_n = t n in (c_{i+1}, c_i], gkernel.py type
 * 'octic').  The moments are Kahan sums in double; their error bounds are applied in leval.py.
 *
 * Coefficients.  Euler factors at every p <= PSMALL are the PARI ones (exact prime decompositions in F'_w and F_L).
 * For p > PSMALL (unramified, p^2 > N_max, so only a_p enters): a_p = sum over the degree-one primes
 * P = (p, sqrt241 - r) of B of tr(rho_19 (x) rho_O (x) lambda_w)(Frob_P).  The trace vanishes unless Frob_P is
 * central in both D4 quotients, i.e. unless the four V4 generators alpha^R[0..3] are squares mod P; then it is
 * 4 eps_19 eps_O lambda_w(P), with eps_o = (gamma_o | P_o) at a prime P_o = (P, sqrt c_o - s) of Bc_o, s^2 = c_o mod P
 * (the root -s gives the same symbol: asserted), and lambda_w(P) = prod_k (alpha_k | P)^(w_k).  Before the run this
 * rule is compared with the PARI Euler factors at every unramified prime 1000 < p <= PSMALL, for all 16 twists.
 * Exceptional primes: if gamma_o vanishes mod P_o at a central side (P_o divides the square part of (gamma_o)), the
 * prime is skipped here and listed in the output; leval.py stops if there are any (their terms would have to be
 * added from PARI's Euler factor).
 *
 * Every n <= N_max < PSMALL^2 is either PSMALL-smooth or m q with q > PSMALL prime and m <= N_max / q < PSMALL:
 *   smooth part: depth-first enumeration of the smooth n with a_n(w) != 0 for some twist;
 *   prime part:  segmented sieve over q in (PSMALL, N_max] (OpenMP), the m-list for each q with a_q != 0.
 * Also written, for Rankin's tail bound: R(w, beta) = sum over q in (PSMALL, N_max] of |a_q(w)| q^-beta; and, for the
 * Euler-product test of octtest.py at s = 19/10, sum over the central sides P of q in (PSMALL, N_max] of
 * -4 log(1 - sign_w(P) q^-1.9) (the local factor (1 - sign T)^-4 of a central side).
 *
 * Usage: octcoef INPUT OUTPUT NTHREADS [validate]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>

typedef unsigned __int128 u128;
#define NTW 16
#define MAXD 24
#define MAXCELL 2048
#define NBETA 4

static void die(const char *m, long long v) { fprintf(stderr, "octcoef: %s (%lld)\n", m, v); exit(2); }

/* ---------- modular arithmetic (p < 2^50, arguments reduced) ----------
 * mulm: the quotient floor(a b / p) is estimated in double precision (a, b < p < 2^50 exact; relative error of the
 * estimate < 2^-51, so it is off by at most 1 for quotients < 2^50... here < 2^37); the remainder a b - q p is
 * computed exactly modulo 2^64 and lies in (-2p, 3p), so it is exact as a signed 64-bit integer and corrected. */
static inline uint64_t mulm(uint64_t a, uint64_t b, uint64_t p) {
    uint64_t q = (uint64_t)((double)a * (double)b / (double)p);
    int64_t r = (int64_t)(a * b - q * p);
    while (r < 0) r += (int64_t)p;
    while (r >= (int64_t)p) r -= (int64_t)p;
    return (uint64_t)r;
}
static uint64_t powm(uint64_t a, uint64_t e, uint64_t p) {
    uint64_t r = 1 % p; a %= p;
    while (e) { if (e & 1) r = mulm(r, a, p); a = mulm(a, a, p); e >>= 1; }
    return r;
}
static int jac(uint64_t a, uint64_t n) {                 /* Jacobi symbol (a/n), n odd: binary, as census_kv.c */
    unsigned t = 0;
    while (a) {
        int z = __builtin_ctzll(a);
        a >>= z;
        t ^= (unsigned)(z & ((n >> 1) ^ (n >> 2))) & 1u;
        uint64_t lt = a < n;
        t ^= (unsigned)(lt & ((a & n) >> 1));
        uint64_t d = a - n, mask = (uint64_t)0 - lt;
        n = (n & ~mask) | (a & mask);
        a = (d ^ mask) - mask;
    }
    return n == 1 ? (t ? -1 : 1) : 0;
}
static uint64_t invm(uint64_t a, uint64_t p) {          /* a^-1 mod p (extended Euclid), gcd(a, p) = 1 */
    int64_t t0 = 0, t1 = 1; uint64_t r0 = p, r1 = a % p;
    while (r1) { uint64_t q = r0 / r1, r2 = r0 - q * r1; int64_t t2 = t0 - (int64_t)q * t1; r0 = r1; r1 = r2; t0 = t1; t1 = t2; }
    if (r0 != 1) die("invm: not invertible", (long long)p);
    return t0 < 0 ? (uint64_t)(t0 + (int64_t)p) : (uint64_t)t0;
}
static uint64_t sqrtm(uint64_t a, uint64_t p) {          /* a square root of a nonzero square a mod odd prime p */
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
        int i = 0; uint64_t tt = t; while (tt != 1) { tt = mulm(tt, tt, p); i++; if (i == m) die("sqrtm: not a square", (long long)p); }
        uint64_t b = c; for (int j = 0; j < m - i - 1; j++) b = mulm(b, b, p);
        x = mulm(x, b, p); c = mulm(b, b, p); t = mulm(t, c, p); m = i;
    }
    return x;
}

/* ---------- elements of B = Q(t), t^2 = 241: (A + B t)/den with big A, B (decimal input) ---------- */
#define MAXL 16
typedef struct { int sa, sb; int la, lb; uint64_t a[MAXL], b[MAXL]; uint64_t den; } belt;
static void parse_big(const char *s, int *sg, int *len, uint64_t *limb) {
    *sg = 1; if (*s == '-') { *sg = -1; s++; } else if (*s == '+') s++;
    uint64_t L[MAXL] = {0}; int n = 1;
    for (; *s >= '0' && *s <= '9'; s++) {                /* L = 10 L + digit */
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
/* value of the element at t = r mod p, with the denominator inverted (p does not divide den) */
static uint64_t belt_val(const belt *e, uint64_t r, uint64_t p) {
    uint64_t A = big_mod(e->sa, e->la, e->a, p), B = big_mod(e->sb, e->lb, e->b, p);
    uint64_t v = (A + mulm(B, r, p)) % p;
    if (e->den != 1) v = mulm(v, invm(e->den % p, p), p);
    return v;
}

/* ---------- input ---------- */
static int D, ncells[2];
static uint64_t PSMALL, NMAX, NG[2];
static double TG[2], CELLC[MAXCELL + 1];
static uint64_t *NB[2];
static belt KB[8], C19, G019, G119, CO, G0O, G1O;
static unsigned R[4], TW[NTW]; static int TGRP[NTW];
static double BETAS[NBETA]; static int nbeta;
/* Euler data at p <= PSMALL: primes, and a_{p^k}(w) for p^k <= NMAX */
static int nsp; static uint64_t *SP; static int *KMAX; static int64_t **APK;   /* APK[i][k * NTW + w] */
static int64_t **PAR1;                                                          /* -P_1(w) per prime */
static int *PDEG;                                                               /* min degree of P over the twists */

static void read_belt(FILE *f, belt *e) {
    char sa[400], sb[400]; unsigned long long den;
    if (fscanf(f, "%399s %399s %llu", sa, sb, &den) != 3) die("belt", 0);
    parse_big(sa, &e->sa, &e->la, e->a); parse_big(sb, &e->sb, &e->lb, e->b); e->den = den;
}
static void expect(FILE *f, const char *key) { char w[64]; if (fscanf(f, "%63s", w) != 1 || strcmp(w, key)) die(key, 0); }

static void read_input(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) die("cannot open input", 0);
    int ntw; unsigned long long ps, nm;
    expect(f, "NTW"); if (fscanf(f, "%d", &ntw) != 1 || ntw != NTW) die("NTW", ntw);
    expect(f, "D"); if (fscanf(f, "%d", &D) != 1 || D < 4 || D >= MAXD) die("D", D);
    expect(f, "PSMALL"); if (fscanf(f, "%llu", &ps) != 1) die("PSMALL", 0); PSMALL = ps;
    expect(f, "NMAX"); if (fscanf(f, "%llu", &nm) != 1) die("NMAX", 0); NMAX = nm;
    if ((u128)PSMALL * PSMALL <= NMAX) die("NMAX >= PSMALL^2", 0);
    if (NMAX >= (1ULL << 40)) die("NMAX >= 2^40 (mulm needs moduli < 2^40 here)", 0);
    if (NMAX >= (1ULL << 53)) die("NMAX too large for exact doubles", 0);
    expect(f, "BETAS"); if (fscanf(f, "%d", &nbeta) != 1 || nbeta < 1 || nbeta > NBETA) die("BETAS", 0);
    for (int i = 0; i < nbeta; i++) if (fscanf(f, "%lf", &BETAS[i]) != 1) die("beta", i);
    expect(f, "KB"); for (int k = 0; k < 8; k++) read_belt(f, &KB[k]);
    expect(f, "C19"); read_belt(f, &C19); expect(f, "G0_19"); read_belt(f, &G019); expect(f, "G1_19"); read_belt(f, &G119);
    expect(f, "CO"); read_belt(f, &CO); expect(f, "G0_O"); read_belt(f, &G0O); expect(f, "G1_O"); read_belt(f, &G1O);
    expect(f, "R"); for (int i = 0; i < 4; i++) if (fscanf(f, "%u", &R[i]) != 1) die("R", i);
    expect(f, "TW"); for (int w = 0; w < NTW; w++) if (fscanf(f, "%u %d", &TW[w], &TGRP[w]) != 2 || TGRP[w] < 0 || TGRP[w] > 1) die("TW", w);
    expect(f, "CELLS"); int nc; if (fscanf(f, "%d", &nc) != 1 || nc < 2 || nc > MAXCELL) die("CELLS", nc);
    for (int i = 0; i <= nc; i++) { char h[64]; if (fscanf(f, "%63s", h) != 1) die("cell", i); CELLC[i] = strtod(h, NULL); }
    for (int g = 0; g < 2; g++) {
        expect(f, "GROUP"); int gg; char th[64]; unsigned long long ng;
        if (fscanf(f, "%d %63s %llu", &gg, th, &ng) != 3 || gg != g) die("GROUP", g);
        TG[g] = strtod(th, NULL); NG[g] = ng; ncells[g] = nc;
        NB[g] = malloc(sizeof(uint64_t) * (nc + 1));
        for (int i = 0; i <= nc; i++) { unsigned long long v; if (fscanf(f, "%llu", &v) != 1) die("NB", i); NB[g][i] = v; }
        if (NB[g][0] != NG[g] || NG[g] > NMAX) die("NB[0] != N_g", g);
        for (int i = 0; i < nc; i++) if (NB[g][i + 1] > NB[g][i]) die("NB not decreasing", i);
        if (NB[g][nc] != 0) die("cells do not reach n = 1", g);
    }
    if (NMAX != (NG[0] > NG[1] ? NG[0] : NG[1])) die("NMAX != max N_g", 0);
    expect(f, "EULER"); if (fscanf(f, "%d", &nsp) != 1) die("EULER", 0);
    SP = malloc(sizeof(uint64_t) * nsp); KMAX = malloc(sizeof(int) * nsp);
    APK = malloc(sizeof(int64_t *) * nsp); PAR1 = malloc(sizeof(int64_t *) * nsp); PDEG = malloc(sizeof(int) * nsp);
    for (int i = 0; i < nsp; i++) {
        unsigned long long p; if (fscanf(f, "%llu", &p) != 1) die("prime", i); SP[i] = p;
        int km = 0; { u128 pk = p; while (pk * p <= NMAX) { pk *= p; km++; } } km += 1;
        KMAX[i] = km;
        APK[i] = calloc((size_t)(km + 1) * NTW, sizeof(int64_t)); PAR1[i] = calloc(NTW, sizeof(int64_t));
        PDEG[i] = 8;
        for (int w = 0; w < NTW; w++) {
            int d; long long P[9] = {0};
            if (fscanf(f, "%d", &d) != 1 || d < 0 || d > 8) die("degree", (long long)p);
            if (d < PDEG[i]) PDEG[i] = d;
            for (int j = 0; j <= d; j++) if (fscanf(f, "%lld", &P[j]) != 1) die("coeff", (long long)p);
            if (P[0] != 1) die("P(0) != 1", (long long)p);
            PAR1[i][w] = -P[1];
            /* 1/P(X) up to X^km */
            int64_t c[64] = {0}; c[0] = 1;
            for (int k = 1; k <= km; k++) { int64_t v = 0; for (int j = 1; j <= d && j <= k; j++) v -= P[j] * c[k - j]; c[k] = v; }
            for (int k = 0; k <= km; k++) APK[i][k * NTW + w] = c[k];
        }
    }
    if (SP[nsp - 1] != PSMALL && SP[nsp - 1] > PSMALL) die("Euler primes beyond PSMALL", 0);
    fclose(f);
}

/* ---------- the rule for p > PSMALL ---------- */
static int qr241[241];
/* a_p(w) for all twists at an odd prime p (not 241, unramified); returns 1 if some a_p(w) != 0, 0 if none, -1 if
   gamma_o vanishes at a prime P_o above a central side (exceptional: a_p not computed).  cnt: central sides */
static int ap_rule_s(uint64_t p, int64_t *ap, int *cnt, int sgn[2][NTW]) {
    for (int w = 0; w < NTW; w++) { ap[w] = 0; sgn[0][w] = sgn[1][w] = 0; }
    *cnt = 0;
    if (!qr241[p % 241]) return 0;                        /* inert in B: no degree-one prime */
    uint64_t r = sqrtm(241 % p, p);
    if (mulm(r, r, p) != 241 % p) die("sqrt 241", (long long)p);
    int any = 0;
    for (int side = 0; side < 2; side++) {
        uint64_t rr = side ? p - r : r;
        uint64_t al[8];
        for (int k = 0; k < 8; k++) { al[k] = belt_val(&KB[k], rr, p); if (!al[k]) die("alpha_k = 0 mod P", (long long)p); }
        int central = 1;
        for (int i = 0; i < 4 && central; i++) {
            uint64_t v = 1;
            for (int k = 0; k < 8; k++) if ((R[i] >> k) & 1) v = mulm(v, al[k], p);
            if (jac(v, p) != 1) central = 0;
        }
        if (!central) continue;
        (*cnt)++;
        unsigned vneg = 0;
        for (int k = 0; k < 8; k++) if (jac(al[k], p) == -1) vneg |= 1u << k;
        int eps = 1;
        for (int o = 0; o < 2; o++) {
            const belt *c = o ? &CO : &C19, *g0 = o ? &G0O : &G019, *g1 = o ? &G1O : &G119;
            uint64_t cv = belt_val(c, rr, p);
            if (jac(cv, p) != 1) die("c_o not a square at a central prime", (long long)p);
            uint64_t s = sqrtm(cv, p);
            if (mulm(s, s, p) != cv) die("sqrt c_o", (long long)p);
            uint64_t a0 = belt_val(g0, rr, p), a1 = belt_val(g1, rr, p);
            int e1 = jac((a0 + mulm(a1, s, p)) % p, p), e2 = jac((a0 + p - mulm(a1, s, p)) % p, p);
            if (e1 == 0 || e2 == 0) return -1;
            if (e1 != e2) die("eps_o: symbols at the two primes of Bc_o differ", (long long)p);
            eps *= e1;
        }
        for (int w = 0; w < NTW; w++) {
            int sg = eps * ((__builtin_popcount(TW[w] & vneg) & 1) ? -1 : 1);
            ap[w] += 4 * sg; sgn[side][w] = sg;
        }
        any = 1;
    }
    if (any) { any = 0; for (int w = 0; w < NTW; w++) if (ap[w]) any = 1; }
    return any;
}

static int ap_rule(uint64_t p, int64_t *ap, int *cnt) { int sg[2][NTW]; return ap_rule_s(p, ap, cnt, sg); }

/* ---------- moments ---------- */
typedef struct { double *S, *C; uint64_t *A, *cnt; double *rk, *eul; } acc;   /* per twist x cell x (D+1) */
static size_t IDX(int w, int i, int j) { return ((size_t)w * MAXCELL + i) * (MAXD) + j; }
static acc acc_new(void) {
    acc a;
    a.S = calloc((size_t)NTW * MAXCELL * MAXD, sizeof(double)); a.C = calloc((size_t)NTW * MAXCELL * MAXD, sizeof(double));
    a.A = calloc((size_t)NTW * MAXCELL, sizeof(uint64_t)); a.cnt = calloc((size_t)NTW * MAXCELL, sizeof(uint64_t));
    a.rk = calloc((size_t)NTW * NBETA, sizeof(double)); a.eul = calloc(NTW, sizeof(double));
    if (!a.S || !a.C || !a.A || !a.cnt || !a.rk || !a.eul) die("alloc", 0);
    return a;
}
static inline int cell_of(int g, uint64_t n) {          /* i with NB[i+1] < n <= NB[i] */
    int lo = 0, hi = ncells[g] - 1;
    while (lo < hi) { int mid = (lo + hi + 1) >> 1; if (NB[g][mid] >= n) lo = mid; else hi = mid - 1; }
    if (!(NB[g][lo] >= n && NB[g][lo + 1] < n)) die("cell search", (long long)n);
    return lo;
}
/* add a_n(w) (all twists) at n */
static inline void add_term(acc *a, uint64_t n, const int64_t *an) {
    for (int g = 0; g < 2; g++) {
        if (n > NG[g]) continue;
        int nz = 0; for (int w = 0; w < NTW; w++) if (TGRP[w] == g && an[w]) { nz = 1; break; }
        if (!nz) continue;
        int i = cell_of(g, n);
        double u = TG[g] * (double)n / CELLC[i] - 1.0;
        double pw[MAXD]; pw[0] = 1.0; for (int j = 1; j <= D; j++) pw[j] = pw[j - 1] * u;
        for (int w = 0; w < NTW; w++) {
            if (TGRP[w] != g || !an[w]) continue;
            double av = (double)an[w];
            size_t b = IDX(w, i, 0);
            for (int j = 0; j <= D; j++) {
                double y = av * pw[j] - a->C[b + j];
                double t = a->S[b + j] + y;
                a->C[b + j] = (t - a->S[b + j]) - y;
                a->S[b + j] = t;
            }
            a->A[(size_t)w * MAXCELL + i] += (uint64_t)(an[w] < 0 ? -an[w] : an[w]);
            a->cnt[(size_t)w * MAXCELL + i]++;
        }
    }
}

/* smooth part: depth-first over the primes SP[] */
static uint64_t n_smooth = 0;
static void dfs(acc *a, uint64_t n, const int64_t *vec, int start) {
    for (int i = start; i < nsp; i++) {
        uint64_t p = SP[i];
        if ((u128)n * p > NMAX) break;
        uint64_t pk = 1;
        for (int k = 1; k <= KMAX[i]; k++) {
            if ((u128)n * pk * p > NMAX) break;
            pk *= p;
            const int64_t *c = APK[i] + (size_t)k * NTW;
            int64_t nv[NTW]; int nz = 0;
            for (int w = 0; w < NTW; w++) { nv[w] = vec[w] * c[w]; if (nv[w]) nz = 1; }
            if (!nz) continue;
            add_term(a, n * pk, nv); n_smooth++;
            dfs(a, n * pk, nv, i + 1);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: octcoef INPUT OUTPUT NTHREADS [validate]\n"); return 1; }
    int validate_only = argc > 4 && !strcmp(argv[4], "validate");
    for (int i = 0; i < 241; i++) qr241[i] = 0;
    for (int i = 1; i < 241; i++) qr241[(i * i) % 241] = 1;
    read_input(argv[1]);
    fprintf(stderr, "octcoef: D %d PSMALL %llu NMAX %llu N_g %llu %llu cells %d, %d Euler primes\n", D,
            (unsigned long long)PSMALL, (unsigned long long)NMAX, (unsigned long long)NG[0], (unsigned long long)NG[1], ncells[0], nsp);
    /* 1. validation of the rule against PARI at 1000 < p <= PSMALL */
    long nval = 0, ncentral = 0, nboth = 0, ninert = 0, nexc = 0, nram = 0;
    for (int i = 0; i < nsp; i++) {
        uint64_t p = SP[i];
        if (p <= 1000) continue;
        if (p == 241 || PDEG[i] < 8) { nram++; continue; }          /* ramified (degree < 8): PARI only */
        int64_t ap[NTW]; int cnt;
        if (ap_rule(p, ap, &cnt) < 0) { nexc++; continue; }
        for (int w = 0; w < NTW; w++) if (ap[w] != PAR1[i][w]) { fprintf(stderr, "p %llu w %d rule %lld PARI %lld\n", (unsigned long long)p, w, (long long)ap[w], (long long)PAR1[i][w]); die("rule disagrees with PARI", (long long)p); }
        nval++; ncentral += cnt; if (cnt == 2) nboth++; if (!qr241[p % 241]) ninert++;
    }
    fprintf(stderr, "octcoef: rule = PARI at %ld primes in (1000, %llu] (%ld inert in B, %ld central sides, %ld primes with both sides central; skipped: %ld ramified, %ld exceptional)\n",
            nval, (unsigned long long)PSMALL, ninert, ncentral, nboth, nram, nexc);
    if (validate_only) return 0;
    int nth = atoi(argv[3]); omp_set_num_threads(nth);
    /* 2. a_m for m <= MS (all prime factors <= PSMALL): sieve */
    uint64_t MS = NMAX / (PSMALL + 1);
    int64_t *am = calloc((size_t)(MS + 1) * NTW, sizeof(int64_t));
    uint32_t *spf = calloc(MS + 1, sizeof(uint32_t));
    for (uint64_t i = 2; i <= MS; i++) if (!spf[i]) for (uint64_t j = i; j <= MS; j += i) if (!spf[j]) spf[j] = (uint32_t)i;
    int *pidx = calloc(MS + 2, sizeof(int));
    for (int i = 0; i < nsp && SP[i] <= MS; i++) pidx[SP[i]] = i;
    for (int w = 0; w < NTW; w++) am[NTW + w] = 1;
    for (uint64_t m = 2; m <= MS; m++) {
        uint64_t p = spf[m], mm = m; int k = 0; while (mm % p == 0) { mm /= p; k++; }
        int ii = pidx[p]; if (SP[ii] != p) die("small prime index", (long long)p);
        if (k > KMAX[ii]) die("kmax", (long long)p);
        for (int w = 0; w < NTW; w++) am[m * NTW + w] = APK[ii][(size_t)k * NTW + w] * am[mm * NTW + w];
    }
    uint64_t nS = 0; for (uint64_t m = 1; m <= MS; m++) { int nz = 0; for (int w = 0; w < NTW; w++) if (am[m * NTW + w]) nz = 1; if (nz) nS++; }
    uint64_t *Sm = malloc(sizeof(uint64_t) * nS); int64_t *Sa = malloc(sizeof(int64_t) * nS * NTW); nS = 0;
    for (uint64_t m = 1; m <= MS; m++) {
        int nz = 0; for (int w = 0; w < NTW; w++) if (am[m * NTW + w]) nz = 1;
        if (!nz) continue;
        Sm[nS] = m; memcpy(Sa + nS * NTW, am + m * NTW, sizeof(int64_t) * NTW); nS++;
    }
    fprintf(stderr, "octcoef: %llu m <= %llu with a_m != 0\n", (unsigned long long)nS, (unsigned long long)MS);
    /* 3. smooth part */
    acc a0 = acc_new();
    { int64_t one[NTW]; for (int w = 0; w < NTW; w++) one[w] = 1; add_term(&a0, 1, one); n_smooth = 1; dfs(&a0, 1, one, 0); }
    fprintf(stderr, "octcoef: %llu smooth n with a_n != 0\n", (unsigned long long)n_smooth);
    /* 4. prime part */
    uint64_t L = (uint64_t)sqrt((double)NMAX) + 2;
    char *comp = calloc(L + 1, 1); uint64_t *bp = malloc(sizeof(uint64_t) * (L / 2 + 16)); size_t nbp = 0;
    for (uint64_t i = 2; i <= L; i++) if (!comp[i]) { bp[nbp++] = i; for (uint64_t j = i * i; j <= L; j += i) comp[j] = 1; }
    const uint64_t SEG = 1ULL << 22;                    /* odd numbers per segment */
    uint64_t lo0 = PSMALL + 1, nseg = (NMAX - lo0) / (2 * SEG) + 1;
    acc *TA = malloc(sizeof(acc) * nth); for (int t = 0; t < nth; t++) TA[t] = acc_new();
    uint64_t tot_central = 0, tot_q = 0, tot_pairs = 0;
    uint64_t *EXC = malloc(sizeof(uint64_t) * 100000); int nEXC = 0;
    #pragma omp parallel reduction(+:tot_central,tot_q,tot_pairs)
    {
        int tid = omp_get_thread_num();
        acc *a = &TA[tid];
        uint8_t *sv = malloc(SEG);
        #pragma omp for schedule(static, 1)          /* static: the per-thread sums, hence the output, are reproducible for a given NTHREADS */
        for (uint64_t sg = 0; sg < nseg; sg++) {
            uint64_t base = lo0 + sg * 2 * SEG; if (!(base & 1)) base++;     /* odd numbers base + 2i */
            uint64_t top = base + 2 * (SEG - 1); if (top > NMAX) top = NMAX;
            if (base > NMAX) continue;
            memset(sv, 0, SEG);
            for (size_t k = 1; k < nbp; k++) {                                  /* skip 2 */
                uint64_t q = bp[k]; if (q * q > top) break;
                uint64_t st = (base + q - 1) / q * q; if (st < q * q) st = q * q; if (!(st & 1)) st += q;
                for (uint64_t x = st; x <= top; x += 2 * q) sv[(x - base) >> 1] = 1;
            }
            for (uint64_t i = 0; base + 2 * i <= top; i++) {
                if (sv[i]) continue;
                uint64_t q = base + 2 * i;
                tot_q++;
                int64_t aq[NTW]; int cnt, sg[2][NTW];
                int st = ap_rule_s(q, aq, &cnt, sg);
                if (st < 0) {
                    #pragma omp critical
                    { if (nEXC >= 100000) die("too many exceptional primes", (long long)q); EXC[nEXC++] = q; }
                    continue;
                }
                if (cnt) {
                    double qs = pow((double)q, -1.9);
                    for (int w = 0; w < NTW; w++) for (int sd = 0; sd < 2; sd++) if (sg[sd][w]) a->eul[w] += -4.0 * log1p(-sg[sd][w] * qs);
                }
                if (!st) continue;
                tot_central++;
                for (int w = 0; w < NTW; w++) {
                    double ab = (double)(aq[w] < 0 ? -aq[w] : aq[w]);
                    if (ab > 0) for (int b = 0; b < nbeta; b++) a->rk[w * NBETA + b] += ab * pow((double)q, -BETAS[b]);
                }
                uint64_t mmax = NMAX / q;
                for (uint64_t s = 0; s < nS && Sm[s] <= mmax; s++) {
                    int64_t an[NTW]; int nz = 0;
                    for (int w = 0; w < NTW; w++) { an[w] = Sa[s * NTW + w] * aq[w]; if (an[w]) nz = 1; }
                    if (!nz) continue;
                    add_term(a, Sm[s] * q, an); tot_pairs++;
                }
            }
        }
        free(sv);
    }
    fprintf(stderr, "octcoef: %llu primes q in (%llu, %llu], %llu with a_q != 0, %llu terms m q\n", (unsigned long long)tot_q,
            (unsigned long long)PSMALL, (unsigned long long)NMAX, (unsigned long long)tot_central, (unsigned long long)tot_pairs);
    /* 5. merge (sum - comp per thread, then over threads; the merge error is covered in leval.py) and write */
    FILE *fo = fopen(argv[2], "wb"); if (!fo) die("output", 0);
    int32_t hdr[4] = {NTW, D, ncells[0], nth};
    fwrite(hdr, sizeof hdr, 1, fo);
    for (int w = 0; w < NTW; w++) {
        for (int i = 0; i < ncells[0]; i++) {
            uint64_t A = a0.A[(size_t)w * MAXCELL + i], c = a0.cnt[(size_t)w * MAXCELL + i];
            double M[MAXD];
            for (int j = 0; j <= D; j++) M[j] = a0.S[IDX(w, i, j)] - a0.C[IDX(w, i, j)];
            for (int t = 0; t < nth; t++) {
                A += TA[t].A[(size_t)w * MAXCELL + i]; c += TA[t].cnt[(size_t)w * MAXCELL + i];
                for (int j = 0; j <= D; j++) M[j] += TA[t].S[IDX(w, i, j)] - TA[t].C[IDX(w, i, j)];
            }
            fwrite(&c, sizeof c, 1, fo); fwrite(&A, sizeof A, 1, fo); fwrite(M, sizeof(double), D + 1, fo);
        }
        double rk[NBETA] = {0};
        for (int t = 0; t < nth; t++) for (int b = 0; b < nbeta; b++) rk[b] += TA[t].rk[w * NBETA + b];
        fwrite(rk, sizeof(double), NBETA, fo);
    }
    uint64_t tots[4] = {n_smooth, tot_q, tot_central, tot_pairs};
    fwrite(tots, sizeof tots, 1, fo);
    int32_t ne = nEXC; fwrite(&ne, sizeof ne, 1, fo); fwrite(EXC, sizeof(uint64_t), nEXC, fo);
    { double eul[NTW] = {0}; for (int t = 0; t < nth; t++) for (int w = 0; w < NTW; w++) eul[w] += TA[t].eul[w];
      fwrite(eul, sizeof(double), NTW, fo); }
    fprintf(stderr, "octcoef: %d exceptional primes q > PSMALL (gamma_o not a unit at P_o)\n", nEXC);
    fclose(fo);
    fprintf(stderr, "octcoef: wrote %s\n", argv[2]);
    return 0;
}
