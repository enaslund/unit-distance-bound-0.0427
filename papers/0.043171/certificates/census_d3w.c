/* [wheel version: sieves only the progressions 1, 49 mod 120]
 * Census of the primes of B = Q(sqrt 241) of degree one that split completely in the Kummer
 * field E (Frobenius vector 0), with norm p in (XLO, XHI], and the D4 test: such a prime P has
 * residue degree >= 2 in every tower field K as soon as, for one of the D4 fields
 * M_i = F0_i(sqrt beta_i) (d4fields15.h; F0_i = B(sqrt a_i, sqrt b_i) inside E), beta_i is a
 * nonsquare modulo a prime of F0_i above P.
 *
 * A degree-one prime P = (p, sqrt241 - r) has vector 0 iff the 8 Kummer basis elements
 * alpha_k = (GA_k + GB_k r)/GD_k are squares mod p.  Necessary: p = 1, 49 mod 120 and (241/p) = 1
 * (E contains sqrt(-1), sqrt 2, sqrt 3, sqrt 5, sqrt 241).
 *
 * Output (prefix given on the command line):
 *   <prefix>.bins : uint64 counts of detected primes in geometric bins
 *                   [XLO (1+H)^j, XLO (1+H)^(j+1)), j = 0..NB-1 (H = 2^-16)
 *   <prefix>.txt  : summary, and every undetected vector-0 prime
 * Usage: census_d3 XLO XHI nthreads prefix
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

static inline uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) { return (uint64_t)((u128)a * b % m); }
static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) {
    uint64_t r = 1; a %= m;
    while (e) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; }
    return r;
}
static int jacobi(uint64_t a, uint64_t n) { /* n odd, 0 <= a < n */
    int s = 1;
    while (a) {
        int tz = __builtin_ctzll(a);
        a >>= tz;
        if ((tz & 1) && ((n & 7) == 3 || (n & 7) == 5)) s = -s;
        if ((a & 3) == 3 && (n & 3) == 3) s = -s;
        uint64_t t = n % a; n = a; a = t;
    }
    return n == 1 ? s : 0;
}
static inline uint64_t modp(int64_t v, uint64_t p) {
    int64_t t = v % (int64_t)p; if (t < 0) t += (int64_t)p; return (uint64_t)t;
}
/* Tonelli-Shanks with precomputed odd part q, 2-adic exponent s, and c = z^q for a nonresidue z */
static uint64_t ts_sqrt(uint64_t a, uint64_t p, uint64_t q, int s, uint64_t cz) {
    if (a == 0) return 0;
    int m = s; uint64_t c = cz, t = powmod(a, q, p), r = powmod(a, (q + 1) / 2, p);
    while (t != 1) {
        int i = 0; uint64_t tt = t;
        while (tt != 1) { tt = mulmod(tt, tt, p); i++; if (i >= m) return UINT64_MAX; }
        uint64_t b = c; for (int j = 0; j < m - i - 1; j++) b = mulmod(b, b, p);
        m = i; c = mulmod(b, b, p); t = mulmod(t, c, p); r = mulmod(r, b, p);
    }
    return r;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: census_d3 XLO XHI nthreads prefix\n"); return 1; }
    uint64_t XLO = (uint64_t)strtod(argv[1], NULL), XHI = (uint64_t)strtod(argv[2], NULL);
    int nth = atoi(argv[3]);
    const char *prefix = argv[4];
    int debug = argc > 5;
    omp_set_num_threads(nth);
    uint64_t NB = (uint64_t)ceil(log((double)XHI / (double)XLO) / log1p(H_BIN)) + 2;
    int qr241[241]; memset(qr241, 0, sizeof qr241);
    for (int i = 1; i < 241; i++) qr241[(i * i) % 241] = 1;
    /* base primes up to sqrt(XHI) */
    uint64_t L = (uint64_t)sqrt((double)XHI) + 2;
    char *bs = calloc(L + 1, 1);
    uint64_t *bp = malloc(sizeof(uint64_t) * (L / 2 + 10)); size_t nbp = 0;
    for (uint64_t i = 2; i <= L; i++) if (!bs[i]) { bp[nbp++] = i; for (uint64_t j = i * i; j <= L; j += i) bs[j] = 1; }
    const uint64_t SEGK = 1ULL << 22;  /* progression terms per segment */
    const uint64_t AA[2] = {1, 49};
    uint64_t kmin = (XLO + 1 > 1 ? (XLO + 1 - 1) / 120 : 0), kmax = XHI / 120 + 1;
    uint64_t nsegk = (kmax - kmin) / SEGK + 1;
    uint64_t *inv120 = malloc(sizeof(uint64_t) * nbp);
    for (size_t k = 0; k < nbp; k++) inv120[k] = (bp[k] > 5) ? powmod(120 % bp[k], bp[k] - 2, bp[k]) : 0;
    uint64_t *bins = calloc(NB, sizeof(uint64_t));
    uint64_t tot_cand = 0, tot_v0 = 0, tot_det = 0, tot_zero = 0;
    FILE *ftxt; char fn[512];
    snprintf(fn, sizeof fn, "%s.txt", prefix); ftxt = fopen(fn, "w");
    #pragma omp parallel
    {
        char *seg = malloc(SEGK);
        uint64_t *lb = calloc(NB, sizeof(uint64_t));
        uint64_t c_cand = 0, c_v0 = 0, c_det = 0, c_zero = 0;
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
                uint64_t r = mulmod((q - a % q) % q, inv120[k], q);     /* q | a + 120 k  <=>  k = r mod q */
                uint64_t kk = K0 + (r + q - K0 % q) % q;
                uint64_t kq = (q * q > a) ? (q * q - a + 119) / 120 : 0; /* a + 120 k >= q^2 */
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
                /* Tonelli-Shanks data */
                uint64_t q = p - 1; int s = 0; while (!(q & 1)) { q >>= 1; s++; }
                uint64_t z = 3; while (jacobi(z % p, p) != -1) z++;
                uint64_t cz = powmod(z, q, p);
                uint64_t r = ts_sqrt(241 % p, p, q, s, cz);
                if (r == UINT64_MAX || mulmod(r, r, p) != 241 % p) { fprintf(stderr, "sqrt241 failed %llu\n", (unsigned long long)p); exit(2); }
                uint64_t inv2 = (p + 1) / 2, inv120 = powmod(120, p - 2, p);
                for (int side = 0; side < 2; side++) {
                    uint64_t rr = side ? p - r : r;
                    uint64_t al[8]; int v0 = 1;
                    for (int k = 0; k < 8 && v0; k++) {
                        uint64_t v = (modp(GA[k], p) + mulmod(modp(GB[k], p), rr, p)) % p;
                        if (GD[k] == 2) v = mulmod(v, inv2, p);
                        al[k] = v;
                        if (jacobi(v, p) != 1) v0 = 0;
                    }
                    if (!v0) continue;
                    c_v0++;
                    uint64_t sq[8];
                    for (int k = 0; k < 8; k++) {
                        sq[k] = ts_sqrt(al[k], p, q, s, cz);
                        if (sq[k] == UINT64_MAX || mulmod(sq[k], sq[k], p) != al[k]) { fprintf(stderr, "sqrt failed %llu\n", (unsigned long long)p); exit(2); }
                    }
                    int det = 0, zero = 0; char bits[NF + 1]; bits[NF] = 0;
                    for (int i = 0; i < NF && (debug || !det); i++) {
                        uint64_t sa = 1, sb = 1;
                        for (int k = 0; k < 8; k++) {
                            if ((R1[i] >> k) & 1) sa = mulmod(sa, sq[k], p);
                            if ((R2[i] >> k) & 1) sb = mulmod(sb, sq[k], p);
                        }
                        uint64_t bas[8] = {1, rr, sa, mulmod(rr, sa, p), sb, mulmod(rr, sb, p), mulmod(sa, sb, p), 0};
                        bas[7] = mulmod(rr, bas[6], p);
                        uint64_t val = 0;
                        for (int j = 0; j < 8; j++) {
                            if (NUM[i][j] == 0) continue;
                            uint64_t c = mulmod(modp(NUM[i][j], p), mulmod(inv120, (uint64_t)(120 / DEN[i][j]), p), p);
                            val = (val + mulmod(c, bas[j], p)) % p;
                        }
                        int jac = jacobi(val, p);
                        if (jac == -1) det = 1;
                        if (jac == 0) zero = 1;
                        bits[i] = jac == -1 ? '1' : (jac == 1 ? '0' : 'z');
                    }
                    if (debug) {
                        #pragma omp critical
                        { fprintf(ftxt, "bits %llu %llu %s\n", (unsigned long long)p, (unsigned long long)rr, bits); }
                    }
                    if (zero) c_zero++;
                    if (det) {
                        c_det++;
                        uint64_t idx = (uint64_t)floor(log((double)p / (double)XLO) / log1p(H_BIN));
                        if (idx >= NB) idx = NB - 1;
                        lb[idx]++;
                    } else {
                        #pragma omp critical
                        { fprintf(ftxt, "undetected %llu %llu\n", (unsigned long long)p, (unsigned long long)rr); fflush(ftxt); }
                    }
                }
            }
        }
        #pragma omp critical
        {
            for (uint64_t j = 0; j < NB; j++) bins[j] += lb[j];
            tot_cand += c_cand; tot_v0 += c_v0; tot_det += c_det; tot_zero += c_zero;
        }
        free(seg); free(lb);
    }
    fprintf(ftxt, "XLO %llu XHI %llu H 2^-16 NB %llu candidates %llu v0 %llu detected %llu zero %llu\n",
            (unsigned long long)XLO, (unsigned long long)XHI, (unsigned long long)NB, (unsigned long long)tot_cand,
            (unsigned long long)tot_v0, (unsigned long long)tot_det, (unsigned long long)tot_zero);
    fclose(ftxt);
    snprintf(fn, sizeof fn, "%s.bins", prefix);
    FILE *fb = fopen(fn, "wb"); fwrite(bins, sizeof(uint64_t), NB, fb); fclose(fb);
    printf("XLO %llu XHI %llu NB %llu candidates %llu v0 %llu detected %llu zero %llu\n",
           (unsigned long long)XLO, (unsigned long long)XHI, (unsigned long long)NB, (unsigned long long)tot_cand,
           (unsigned long long)tot_v0, (unsigned long long)tot_det, (unsigned long long)tot_zero);
    return 0;
}
