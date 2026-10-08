/* Faster version of census_d3k.c (same primes, same D4 test, same bins); see census_d3k.c for the setting.
 *
 * Census of the degree-one primes P = (p, sqrt241 - r) of B = Q(sqrt 241) with norm p in (XLO, XHI] that split
 * completely in the Kummer field E (vector 0), with the D4 test of d4fields15.h.  Differences from census_d3k.c:
 *
 *  - Montgomery arithmetic modulo p (p < 2^62); Jacobi symbols are taken of normal forms, and of 120 beta
 *    instead of beta ((120/p) = 1, since p = 1, 49 mod 120);
 *  - the nonresidue for Tonelli-Shanks is the least prime l >= 7 with (p/l) = -1 (= (l/p), as p = 1 mod 4);
 *  - vector 0: alpha_0 = -1, alpha_2 alpha_3 = 2, alpha_4 alpha_5 = -3, alpha_6 alpha_7 = -5, and the conjugates
 *    are alpha_1' = -1/alpha_1, alpha_2' = -alpha_3, alpha_3' = -alpha_2, alpha_4' = alpha_5, alpha_6' = alpha_7.
 *    As (-1/p) = (2/p) = (3/p) = (5/p) = 1, P has vector 0 iff alpha_1, alpha_2, alpha_4, alpha_6 are squares mod P,
 *    and then so does the conjugate prime.  The square roots of the other alpha_k, on both sides, are formed from
 *    those four and sqrt(-1), sqrt 2, sqrt 3, sqrt 5; every root is checked by squaring.  Mode "check" also runs
 *    the eight-element test of census_d3k.c on both sides for every candidate;
 *  - mode "W" decides the four fields of the masks MW1 | MW2 first, and only for sides with Frobenius in ker W
 *    (even parities, as in census_d3k.c) the remaining fields, until one detects.  It writes only .binsBW.  A zero
 *    value (beta = 0 mod the prime) in a field of MW1 | MW2 excludes the side from .binsBW (counted as zeroW);
 *  - mode "full" (and "check") computes all 15 fields and writes .bins, .binsB1, .binsBW as census_d3k.c.
 *
 * Usage: census_kw XLO XHI nthreads prefix CH MW1 MW2 MODE        (MODE = W, full or check)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
#include "d4fields15.h"

typedef unsigned __int128 u128;
static const int64_t GA[8] = {-1, -71011068, -6101, 6101, 31, 31, 326, 326};
static const int64_t GB[8] = {0, 4574225, -393, -393, -2, 2, -21, 21};
static const int64_t GD[8] = {1, 1, 2, 2, 1, 1, 1, 1};
#define H_BIN (1.0 / 65536.0)

typedef struct { uint64_t p, ninv, one, r2; } mont;
static inline uint64_t mmul(uint64_t a, uint64_t b, const mont *m) {   /* a b / 2^64 mod p, a b < p 2^64 */
    u128 t = (u128)a * b;
    uint64_t q = (uint64_t)t * m->ninv;
    u128 u = t + (u128)q * m->p;
    uint64_t r = (uint64_t)(u >> 64);
    return r >= m->p ? r - m->p : r;
}
static inline void mont_init(mont *m, uint64_t p) {
    uint64_t x = p;                                   /* p^-1 mod 2^3 */
    for (int i = 0; i < 5; i++) x *= 2 - p * x;      /* Newton: 2^96 */
    m->p = p; m->ninv = (uint64_t)0 - x;
    m->one = ((uint64_t)0 - p) % p;                   /* 2^64 mod p */
    m->r2 = (uint64_t)(((u128)m->one * m->one) % p);  /* 2^128 mod p */
}
static inline uint64_t to_m(uint64_t a, const mont *m) { return mmul(a, m->r2, m); }   /* a < p */
static inline uint64_t from_m(uint64_t a, const mont *m) { return mmul(a, 1, m); }
static inline uint64_t addm(uint64_t a, uint64_t b, uint64_t p) { uint64_t s = a + b; return s >= p ? s - p : s; }
static inline uint64_t subm(uint64_t a, uint64_t b, uint64_t p) { return a >= b ? a - b : a + p - b; }
static uint64_t pw(uint64_t a, uint64_t e, const mont *m) {
    uint64_t r = m->one;
    while (e) { if (e & 1) r = mmul(r, a, m); a = mmul(a, a, m); e >>= 1; }
    return r;
}
static void pw2(uint64_t a, uint64_t ea, uint64_t b, uint64_t eb, const mont *m, uint64_t *ra, uint64_t *rb) {
    uint64_t x = m->one, y = m->one;
    while (ea | eb) {
        if (ea & 1) x = mmul(x, a, m);
        if (eb & 1) y = mmul(y, b, m);
        ea >>= 1; eb >>= 1;
        if (ea) a = mmul(a, a, m);
        if (eb) b = mmul(b, b, m);
    }
    *ra = x; *rb = y;
}
static int jac(uint64_t a, uint64_t n) {               /* Jacobi (a/n), n odd, 0 <= a < n; binary, branch-free steps */
    unsigned t = 0;
    while (a) {
        int z = __builtin_ctzll(a);
        a >>= z;
        t ^= (unsigned)(z & ((n >> 1) ^ (n >> 2))) & 1u;   /* (2/n) = -1 iff n = 3, 5 mod 8 */
        uint64_t lt = a < n;                                /* swap (reciprocity: flip iff a = n = 3 mod 4) */
        t ^= (unsigned)(lt & ((a & n) >> 1));
        uint64_t d = a - n, mask = (uint64_t)0 - lt;
        n = (n & ~mask) | (a & mask);                       /* min(a, n) */
        a = (d ^ mask) - mask;                              /* |a - n|, even */
    }
    return n == 1 ? (t ? -1 : 1) : 0;
}
/* Tonelli-Shanks in Montgomery form; p - 1 = q 2^s, x = a^((q-1)/2), c0 = z^q for a nonresidue z */
static uint64_t ts_x(uint64_t a, uint64_t x, const mont *m, int s, uint64_t c0) {
    uint64_t r = mmul(a, x, m), t = mmul(r, x, m), c = c0;
    int M = s;
    while (t != m->one) {
        int i = 0; uint64_t tt = t;
        while (tt != m->one) { tt = mmul(tt, tt, m); i++; if (i >= M) return UINT64_MAX; }
        uint64_t b = c; for (int j = 0; j < M - i - 1; j++) b = mmul(b, b, m);
        M = i; c = mmul(b, b, m); t = mmul(t, c, m); r = mmul(r, b, m);
    }
    return r;
}
static inline uint64_t smod(int64_t v, uint64_t p) { int64_t t = v % (int64_t)p; if (t < 0) t += (int64_t)p; return (uint64_t)t; }
/* alpha_k(rr) in normal form, rr in Montgomery form; c * x for c < 2^64 and Montgomery x gives c x in normal form */
static inline uint64_t alpha_n(int k, uint64_t rr_m, const mont *m) {
    uint64_t p = m->p;
    uint64_t v = GB[k] >= 0 ? mmul((uint64_t)GB[k], rr_m, m) : subm(0, mmul((uint64_t)(-GB[k]), rr_m, m), p);
    v = addm(v, smod(GA[k], p), p);
    if (GD[k] == 2) v = (v & 1) ? (uint64_t)(((u128)v + p) >> 1) : v >> 1;
    return v;
}

static int64_t CC[15][8];      /* NUM * (120 / DEN) */
static int primes_l[64], nl = 0;
static unsigned char qrl[64][256];

static void die(const char *w, uint64_t p) { fprintf(stderr, "%s %llu\n", w, (unsigned long long)p); exit(2); }

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: census_kw XLO XHI nthreads prefix CH MW1 MW2 MODE\n"); return 1; }
    uint64_t XLO = (uint64_t)strtod(argv[1], NULL), XHI = (uint64_t)strtod(argv[2], NULL);
    int nth = atoi(argv[3]);
    const char *prefix = argv[4];
    int CH = atoi(argv[5]);
    unsigned MW1 = (unsigned)strtoul(argv[6], NULL, 0), MW2 = (unsigned)strtoul(argv[7], NULL, 0);
    const char *mode = argv[8];
    int modeW = !strcmp(mode, "W"), check = !strcmp(mode, "check");
    if (!modeW && !check && strcmp(mode, "full")) { fprintf(stderr, "MODE must be W, full or check\n"); return 1; }
    if (XHI >= (1ULL << 62)) { fprintf(stderr, "XHI too large\n"); return 1; }
    unsigned WM = MW1 | MW2;
    for (int i = 0; i < NF; i++) for (int j = 0; j < 8; j++) {
        if (120 % DEN[i][j]) { fprintf(stderr, "DEN does not divide 120\n"); return 1; }
        CC[i][j] = NUM[i][j] * (120 / DEN[i][j]);
        if (CC[i][j] / (120 / DEN[i][j]) != NUM[i][j] || CC[i][j] > (1LL << 62) || CC[i][j] < -(1LL << 62)) { fprintf(stderr, "coefficient overflow\n"); return 1; }
    }
    for (int l = 7; l < 256 && nl < 64; l++) {
        int pr = 1; for (int d = 2; d * d <= l; d++) if (l % d == 0) pr = 0;
        if (!pr) continue;
        primes_l[nl] = l; memset(qrl[nl], 0, 256);
        for (int x = 1; x < l; x++) qrl[nl][(x * x) % l] = 1;
        nl++;
    }
    omp_set_num_threads(nth);
    uint64_t NB = (uint64_t)ceil(log((double)XHI / (double)XLO) / log1p(H_BIN)) + 2;
    int qr241[241]; memset(qr241, 0, sizeof qr241);
    for (int i = 1; i < 241; i++) qr241[(i * i) % 241] = 1;
    uint64_t L = (uint64_t)sqrt((double)XHI) + 2;
    char *bs = calloc(L + 1, 1);
    uint64_t *bp = malloc(sizeof(uint64_t) * (L / 2 + 10)); size_t nbp = 0;
    for (uint64_t i = 2; i <= L; i++) if (!bs[i]) { bp[nbp++] = i; for (uint64_t j = i * i; j <= L; j += i) bs[j] = 1; }
    const uint64_t SEGK = 1ULL << 22;
    const uint64_t AA[2] = {1, 49};
    uint64_t kmin = (XLO + 1 > 1 ? (XLO + 1 - 1) / 120 : 0), kmax = XHI / 120 + 1;
    uint64_t nsegk = (kmax - kmin) / SEGK + 1;
    uint64_t *inv120 = malloc(sizeof(uint64_t) * nbp);
    for (size_t k = 0; k < nbp; k++) {
        uint64_t q = bp[k];
        if (q <= 5) { inv120[k] = 0; continue; }
        uint64_t r = 1, a = 120 % q, e = q - 2;
        while (e) { if (e & 1) r = (uint64_t)((u128)r * a % q); a = (uint64_t)((u128)a * a % q); e >>= 1; }
        inv120[k] = r;
    }
    uint64_t *bins = calloc(NB, sizeof(uint64_t)), *binsA = calloc(NB, sizeof(uint64_t)), *binsB = calloc(NB, sizeof(uint64_t));
    uint64_t tot_cand = 0, tot_v0 = 0, tot_det = 0, tot_zero = 0, tot_kw = 0, tot_kwdet = 0, tot_zeroW = 0;
    FILE *ftxt; char fn[512];
    snprintf(fn, sizeof fn, "%s.txt", prefix); ftxt = fopen(fn, "w");
    #pragma omp parallel
    {
        char *seg = malloc(SEGK);
        uint64_t *lb = calloc(NB, sizeof(uint64_t)), *lbA = calloc(NB, sizeof(uint64_t)), *lbB = calloc(NB, sizeof(uint64_t));
        uint64_t c_cand = 0, c_v0 = 0, c_det = 0, c_zero = 0, c_kw = 0, c_kwdet = 0, c_zeroW = 0;
        #pragma omp for schedule(dynamic, 1)
        for (uint64_t job = 0; job < 2 * nsegk; job++) {
            uint64_t a = AA[job & 1], K0 = kmin + (job >> 1) * SEGK, K1 = K0 + SEGK - 1;
            uint64_t nlo = a + 120 * K0, nhi = a + 120 * K1;
            if (nlo > XHI) continue;
            memset(seg, 0, SEGK);
            for (size_t k = 0; k < nbp; k++) {
                uint64_t q = bp[k];
                if (q <= 5) continue;
                if (q * q > nhi) break;
                uint64_t r = (uint64_t)((u128)((q - a % q) % q) * inv120[k] % q);
                uint64_t kk = K0 + (r + q - K0 % q) % q;
                uint64_t kq = (q * q > a) ? (q * q - a + 119) / 120 : 0;
                if (kk < kq) kk += ((kq - kk + q - 1) / q) * q;
                for (; kk <= K1; kk += q) seg[kk - K0] = 1;
            }
            for (uint64_t kk = K0; kk <= K1; kk++) {
                if (seg[kk - K0]) continue;
                uint64_t n = a + 120 * kk;
                if (n <= XLO || n > XHI || n < 7) continue;
                uint64_t p = n;
                if (!qr241[p % 241]) continue;
                c_cand++;
                mont M; mont_init(&M, p);
                uint64_t q = p - 1; int s = 0; while (!(q & 1)) { q >>= 1; s++; }
                uint64_t z = 0;
                for (int li = 0; li < nl; li++) if (!qrl[li][p % (uint64_t)primes_l[li]]) { z = (uint64_t)primes_l[li]; break; }
                if (!z) { z = 257; while (jac(z % p, p) != -1) z++; }
                uint64_t a241 = to_m(241 % p, &M), c0, x241;
                pw2(to_m(z, &M), q, a241, (q - 1) / 2, &M, &c0, &x241);
                uint64_t r = ts_x(a241, x241, &M, s, c0);
                if (r == UINT64_MAX || mmul(r, r, &M) != a241) die("sqrt241 failed", p);
                uint64_t rneg = subm(0, r, p);
                /* vector 0 */
                int v0 = jac(alpha_n(1, r, &M), p) == 1 && jac(alpha_n(2, r, &M), p) == 1 &&
                         jac(alpha_n(4, r, &M), p) == 1 && jac(alpha_n(6, r, &M), p) == 1;
                if (check) {
                    for (int side = 0; side < 2; side++) {
                        int v = 1;
                        for (int k = 0; k < 8; k++) if (jac(alpha_n(k, side ? rneg : r, &M), p) != 1) v = 0;
                        if (v != v0) die("vector-0 shortcut disagrees", p);
                    }
                }
                if (!v0) continue;
                c_v0 += 2;
                /* square roots: side 0 from four Tonelli-Shanks, the rest from the relations */
                uint64_t al[2][8];
                for (int side = 0; side < 2; side++) for (int k = 0; k < 8; k++) al[side][k] = to_m(alpha_n(k, side ? rneg : r, &M), &M);
                uint64_t m3 = to_m(3, &M), m5 = to_m(5, &M), x1, x2, x4, x6, x3, x5;
                pw2(al[0][1], (q - 1) / 2, al[0][2], (q - 1) / 2, &M, &x1, &x2);
                pw2(al[0][4], (q - 1) / 2, al[0][6], (q - 1) / 2, &M, &x4, &x6);
                pw2(m3, (q - 1) / 2, m5, (q - 1) / 2, &M, &x3, &x5);
                uint64_t s1 = ts_x(al[0][1], x1, &M, s, c0), s2 = ts_x(al[0][2], x2, &M, s, c0);
                uint64_t s4 = ts_x(al[0][4], x4, &M, s, c0), s6 = ts_x(al[0][6], x6, &M, s, c0);
                uint64_t r3 = ts_x(m3, x3, &M, s, c0), r5 = ts_x(m5, x5, &M, s, c0);
                uint64_t zi = c0; for (int j = 0; j < s - 2; j++) zi = mmul(zi, zi, &M);     /* sqrt(-1) */
                uint64_t z8 = c0; for (int j = 0; j < s - 3; j++) z8 = mmul(z8, z8, &M);     /* primitive 8th root */
                uint64_t r2 = mmul(z8, subm(M.one, zi, p), &M);                            /* sqrt 2 = z8 (1 - i) */
                uint64_t P12 = mmul(al[0][1], al[0][2], &M), P124 = mmul(P12, al[0][4], &M), P1246 = mmul(P124, al[0][6], &M);
                uint64_t iv = pw(P1246, p - 2, &M);                                         /* 1/(a1 a2 a4 a6) */
                uint64_t i6 = mmul(iv, P124, &M); iv = mmul(iv, al[0][6], &M);
                uint64_t i4 = mmul(iv, P12, &M); iv = mmul(iv, al[0][4], &M);
                uint64_t i2 = mmul(iv, al[0][1], &M), i1 = mmul(iv, al[0][2], &M);
                uint64_t sq[2][8];
                sq[0][0] = zi; sq[0][1] = s1; sq[0][2] = s2; sq[0][3] = mmul(mmul(r2, s2, &M), i2, &M);
                sq[0][4] = s4; sq[0][5] = mmul(mmul(mmul(zi, r3, &M), s4, &M), i4, &M);
                sq[0][6] = s6; sq[0][7] = mmul(mmul(mmul(zi, r5, &M), s6, &M), i6, &M);
                sq[1][0] = zi; sq[1][1] = mmul(mmul(zi, s1, &M), i1, &M); sq[1][2] = mmul(zi, sq[0][3], &M);
                sq[1][3] = mmul(zi, s2, &M); sq[1][4] = sq[0][5]; sq[1][5] = s4; sq[1][6] = sq[0][7]; sq[1][7] = s6;
                for (int side = 0; side < 2; side++) for (int k = 0; k < 8; k++)
                    if (al[side][k] == 0 || mmul(sq[side][k], sq[side][k], &M) != al[side][k]) die("sqrt failed", p);
                for (int side = 0; side < 2; side++) {
                    uint64_t rr = side ? rneg : r;
                    unsigned pat = 0, done = 0; int zero = 0, zeroW = 0;
                    for (int pass = 0; pass < 2; pass++) {
                        for (int i = 0; i < NF; i++) {
                            int inW = (WM >> i) & 1;
                            if (modeW && (pass == 0) != inW) continue;     /* W fields first */
                            if (!modeW && pass == 1) continue;
                            uint64_t sa = M.one, sb = M.one;
                            for (int k = 0; k < 8; k++) {
                                if ((R1[i] >> k) & 1) sa = mmul(sa, sq[side][k], &M);
                                if ((R2[i] >> k) & 1) sb = mmul(sb, sq[side][k], &M);
                            }
                            uint64_t ssb = mmul(sa, sb, &M);
                            uint64_t bas[8] = {M.one, rr, sa, mmul(rr, sa, &M), sb, mmul(rr, sb, &M), ssb, mmul(rr, ssb, &M)};
                            uint64_t val = 0;
                            for (int j = 0; j < 8; j++) {
                                int64_t c = CC[i][j];
                                if (c == 0) continue;
                                uint64_t t = mmul((uint64_t)(c > 0 ? c : -c), bas[j], &M);   /* |c| bas_j, normal form */
                                val = c > 0 ? addm(val, t, p) : subm(val, t, p);
                            }
                            int jv = jac(val, p);                                         /* (120 beta / P) = (beta / P) */
                            done |= 1u << i;
                            if (jv == -1) pat |= 1u << i;
                            if (jv == 0) { zero = 1; if (inW) zeroW = 1; }
                            if (modeW && pass == 1 && pat) break;                          /* detected */
                        }
                        if (modeW && pass == 0) {
                            int kerW = !(__builtin_popcount(pat & MW1) & 1) && !(__builtin_popcount(pat & MW2) & 1);
                            if (!kerW || zeroW || pat) break;                         /* decided */
                        }
                    }
                    if (zero) c_zero++;
                    uint64_t idx = (uint64_t)floor(log((double)p / (double)XLO) / log1p(H_BIN));
                    if (idx >= NB) idx = NB - 1;
                    int kerW = !(__builtin_popcount(pat & MW1) & 1) && !(__builtin_popcount(pat & MW2) & 1);
                    if (modeW) {
                        if (zeroW) {
                            c_zeroW++;
                            #pragma omp critical
                            { fprintf(ftxt, "zeroW %llu %llu\n", (unsigned long long)p, (unsigned long long)from_m(rr, &M)); fflush(ftxt); }
                            continue;
                        }
                        if (!kerW) continue;
                        c_kw++;
                        if (pat) { c_kwdet++; lbB[idx]++; }
                        else {
                            #pragma omp critical
                            { fprintf(ftxt, "undetected %llu %llu\n", (unsigned long long)p, (unsigned long long)from_m(rr, &M)); fflush(ftxt); }
                        }
                    } else {
                        if (pat) {
                            c_det++;
                            lb[idx]++;
                            if (!((pat >> CH) & 1)) lbA[idx]++;
                            if (kerW) lbB[idx]++;
                        } else {
                            #pragma omp critical
                            { fprintf(ftxt, "undetected %llu %llu\n", (unsigned long long)p, (unsigned long long)from_m(rr, &M)); fflush(ftxt); }
                        }
                        if (kerW) { c_kw++; if (pat) c_kwdet++; }
                        if (zeroW) c_zeroW++;
                    }
                }
            }
        }
        #pragma omp critical
        {
            for (uint64_t j = 0; j < NB; j++) { bins[j] += lb[j]; binsA[j] += lbA[j]; binsB[j] += lbB[j]; }
            tot_cand += c_cand; tot_v0 += c_v0; tot_det += c_det; tot_zero += c_zero;
            tot_kw += c_kw; tot_kwdet += c_kwdet; tot_zeroW += c_zeroW;
        }
        free(seg); free(lb); free(lbA); free(lbB);
    }
    if (modeW)
        fprintf(ftxt, "XLO %llu XHI %llu H 2^-16 NB %llu candidates %llu v0 %llu kerW %llu kerW_detected %llu zeroW %llu mode W\n",
                (unsigned long long)XLO, (unsigned long long)XHI, (unsigned long long)NB, (unsigned long long)tot_cand,
                (unsigned long long)tot_v0, (unsigned long long)tot_kw, (unsigned long long)tot_kwdet, (unsigned long long)tot_zeroW);
    else
        fprintf(ftxt, "XLO %llu XHI %llu H 2^-16 NB %llu candidates %llu v0 %llu detected %llu zero %llu\n",
                (unsigned long long)XLO, (unsigned long long)XHI, (unsigned long long)NB, (unsigned long long)tot_cand,
                (unsigned long long)tot_v0, (unsigned long long)tot_det, (unsigned long long)tot_zero);
    fclose(ftxt);
    FILE *fb;
    if (!modeW) {
        snprintf(fn, sizeof fn, "%s.bins", prefix); fb = fopen(fn, "wb"); fwrite(bins, sizeof(uint64_t), NB, fb); fclose(fb);
        snprintf(fn, sizeof fn, "%s.binsB1", prefix); fb = fopen(fn, "wb"); fwrite(binsA, sizeof(uint64_t), NB, fb); fclose(fb);
    }
    snprintf(fn, sizeof fn, "%s.binsBW", prefix); fb = fopen(fn, "wb"); fwrite(binsB, sizeof(uint64_t), NB, fb); fclose(fb);
    printf("XLO %llu XHI %llu NB %llu candidates %llu v0 %llu detected %llu zero %llu kerW %llu kerW_detected %llu zeroW %llu\n",
           (unsigned long long)XLO, (unsigned long long)XHI, (unsigned long long)NB, (unsigned long long)tot_cand,
           (unsigned long long)tot_v0, (unsigned long long)tot_det, (unsigned long long)tot_zero,
           (unsigned long long)tot_kw, (unsigned long long)tot_kwdet, (unsigned long long)tot_zeroW);
    return 0;
}
