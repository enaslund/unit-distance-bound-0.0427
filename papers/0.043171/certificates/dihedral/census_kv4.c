/* census_kv4.c: census_kv.c with a third and a fourth functional MW3, MW4 (masks over the fifteen census bits, inside
 * MW1 | MW2).  Same primes, tests, .binsBW, undetected list and summary line as census_kv.c; in addition the detected
 * vector-0 sides with Frobenius in ker W' (W' = span of MW1, MW2, MW3: three parities even) and in ker W''
 * (W'' = span of MW1..MW4: four parities even) are counted in the same bins, written to <prefix>.binsBW3 and
 * <prefix>.binsBW4, with summary lines "W3 ..." and "W4 ...".  Outcome codes carry the ker W' flag as bit 2 and the
 * ker W'' flag as bit 3, so the vector/scalar comparisons also cover them.
 *
 * Original header of census_kv.c:
 * Vectorized version of census_kw.c, mode W (same primes, same tests, same .binsBW and undetected list).
 *
 * All arithmetic modulo the candidate primes runs on eight primes at a time in AVX-512 IFMA Montgomery
 * arithmetic (radix 2^52, p < 2^50):
 *  - sqrt 241 by Tonelli-Shanks, with the nonresidue of census_kw.c;
 *  - the vector-0 test: Euler's criterion for alpha_1, alpha_2, alpha_4, alpha_6 at P = (p, sqrt241 - r), as in
 *    census_kw.c (the other Kummer elements and the conjugate prime follow), in four rounds, the survivors of
 *    each round compacted before the next.  Montgomery representatives have the Legendre symbol of the value
 *    since (2^52/p) = 1, and the halving in alpha_2 is dropped since (2/p) = 1;
 *  - for the vector-0 primes, the square roots of all alpha_k on both sides as in census_kw.c (each checked by
 *    squaring, which also re-proves vector 0), and the D4 fields in the order of mode W of census_kw.c, with
 *    Euler's criterion for the symbol of 120 beta.
 * The sieve is a bit array; the multiples of 7..31 and the terms that are 0 or nonresidues mod 241 are marked by
 * periodic word patterns, the other base primes keep their next multiple from segment to segment within a block.
 * The scalar code of census_kw.c is also run, and must give the same outcome, on every vector-0 prime in mode
 * Wcheck and on those with floor(p/120) = 0 mod 16 in mode W.
 *
 * Usage: census_kv4 XLO XHI nthreads prefix CH MW1 MW2 MODE MW3 MW4   (MODE = W or Wcheck)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
#include <immintrin.h>
#include "d4fields15.h"

typedef unsigned __int128 u128;
static const int64_t GA[8] = {-1, -71011068, -6101, 6101, 31, 31, 326, 326};
static const int64_t GB[8] = {0, 4574225, -393, -393, -2, 2, -21, 21};
static const int64_t GD[8] = {1, 1, 2, 2, 1, 1, 1, 1};
#define H_BIN (1.0 / 65536.0)

/* ---------- scalar arithmetic (as census_kw.c) ---------- */
typedef struct { uint64_t p, ninv, one, r2; } mont;
static inline uint64_t mmul(uint64_t a, uint64_t b, const mont *m) {
    u128 t = (u128)a * b;
    uint64_t q = (uint64_t)t * m->ninv;
    u128 u = t + (u128)q * m->p;
    uint64_t r = (uint64_t)(u >> 64);
    return r >= m->p ? r - m->p : r;
}
static inline void mont_init(mont *m, uint64_t p) {
    uint64_t x = p;
    for (int i = 0; i < 5; i++) x *= 2 - p * x;
    m->p = p; m->ninv = (uint64_t)0 - x;
    m->one = ((uint64_t)0 - p) % p;
    m->r2 = (uint64_t)(((u128)m->one * m->one) % p);
}
static inline uint64_t to_m(uint64_t a, const mont *m) { return mmul(a, m->r2, m); }
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
static int jac(uint64_t a, uint64_t n) {
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
static inline uint64_t alpha_n(int k, uint64_t rr_m, const mont *m) {
    uint64_t p = m->p;
    uint64_t v = GB[k] >= 0 ? mmul((uint64_t)GB[k], rr_m, m) : subm(0, mmul((uint64_t)(-GB[k]), rr_m, m), p);
    v = addm(v, smod(GA[k], p), p);
    if (GD[k] == 2) v = (v & 1) ? (uint64_t)(((u128)v + p) >> 1) : v >> 1;
    return v;
}

/* ---------- vector arithmetic: 8 lanes, radix 2^52 ---------- */
typedef __m512i V;
#define VZ _mm512_setzero_si512()
static inline V vmul(V a, V b, V p, V ninv) {       /* a b / 2^52 mod p for a, b < p < 2^50 */
    V lo = _mm512_madd52lo_epu64(VZ, a, b);
    V hi = _mm512_madd52hi_epu64(VZ, a, b);
    V m = _mm512_madd52lo_epu64(VZ, lo, ninv);
    hi = _mm512_madd52hi_epu64(hi, m, p);
    V lo2 = _mm512_madd52lo_epu64(lo, m, p);           /* lo + (m p mod 2^52) = 0 or 2^52 */
    V t = _mm512_add_epi64(hi, _mm512_srli_epi64(lo2, 52));
    return _mm512_min_epu64(t, _mm512_sub_epi64(t, p));
}
static inline V vadd(V a, V b, V p) { V s = _mm512_add_epi64(a, b); return _mm512_min_epu64(s, _mm512_sub_epi64(s, p)); }
/* x^e lane-wise (e < 2^63), Montgomery form */
static inline V vpow(V x, V e, V p, V ninv, V one) {
    V r = one;
    const V v1 = _mm512_set1_epi64(1);
    while (_mm512_test_epi64_mask(e, e)) {
        __mmask8 b = _mm512_test_epi64_mask(e, v1);
        r = _mm512_mask_mov_epi64(r, b, vmul(r, x, p, ninv));
        e = _mm512_srli_epi64(e, 1);
        x = vmul(x, x, p, ninv);
    }
    return r;
}
static inline void vpow2(V x, V ex, V y, V ey, V p, V ninv, V one, V *rx, V *ry) {
    V a = one, b = one;
    const V v1 = _mm512_set1_epi64(1);
    while (_mm512_test_epi64_mask(_mm512_or_si512(ex, ey), _mm512_or_si512(ex, ey))) {
        __mmask8 bx = _mm512_test_epi64_mask(ex, v1), by = _mm512_test_epi64_mask(ey, v1);
        a = _mm512_mask_mov_epi64(a, bx, vmul(a, x, p, ninv));
        b = _mm512_mask_mov_epi64(b, by, vmul(b, y, p, ninv));
        ex = _mm512_srli_epi64(ex, 1); ey = _mm512_srli_epi64(ey, 1);
        x = vmul(x, x, p, ninv); y = vmul(y, y, p, ninv);
    }
    *rx = a; *ry = b;
}

/* x^e mod p and y^f mod q on two independent vectors in lockstep (more instruction-level parallelism) */
static inline void vpowd(V x, V e, V p, V ninv, V one, V y, V f, V q, V qinv, V qone, V *rx, V *ry) {
    V a = one, b = qone;
    const V v1 = _mm512_set1_epi64(1);
    while (_mm512_test_epi64_mask(_mm512_or_si512(e, f), _mm512_or_si512(e, f))) {
        __mmask8 bx = _mm512_test_epi64_mask(e, v1), by = _mm512_test_epi64_mask(f, v1);
        a = _mm512_mask_mov_epi64(a, bx, vmul(a, x, p, ninv));
        b = _mm512_mask_mov_epi64(b, by, vmul(b, y, q, qinv));
        e = _mm512_srli_epi64(e, 1); f = _mm512_srli_epi64(f, 1);
        x = vmul(x, x, p, ninv); y = vmul(y, y, q, qinv);
    }
    *rx = a; *ry = b;
}
static inline V vsub(V a, V b, V p) { V d = _mm512_sub_epi64(a, b); return _mm512_min_epu64(d, _mm512_add_epi64(d, p)); }
static inline V vneg(V a, V p) { return _mm512_maskz_sub_epi64(_mm512_test_epi64_mask(a, a), p, a); }
static void die(const char *w, uint64_t p);
/* Tonelli-Shanks on the lanes in `lanes`: a (Montgomery), x = a^((q-1)/2), c0 = z^q, sv = s with p - 1 = q 2^s */
static inline V vts(V a, V x, V c0, V sv, V p, V ninv, V one, __mmask8 lanes) {
    const V v1 = _mm512_set1_epi64(1);
    V r = vmul(a, x, p, ninv), t = vmul(r, x, p, ninv), c = c0, Mv = sv;
    __mmask8 act = _mm512_mask_cmpneq_epu64_mask(lanes, t, one);
    while (act) {
        V tt = t, iv = VZ; __mmask8 found = 0;
        for (int k = 1; ; k++) {
            tt = vmul(tt, tt, p, ninv);
            __mmask8 eq = _mm512_cmpeq_epu64_mask(tt, one) & act & (__mmask8)~found;
            iv = _mm512_mask_mov_epi64(iv, eq, _mm512_set1_epi64(k));
            found |= eq;
            if ((found & act) == act) break;
            if (k > 62) die("TS loop", 0);
        }
        if (_mm512_mask_cmpge_epi64_mask(act, iv, Mv)) die("not a square", 0);
        V e = _mm512_sub_epi64(_mm512_sub_epi64(Mv, iv), v1);
        V b = c;
        for (int j = 0; ; j++) {
            __mmask8 need = _mm512_mask_cmpgt_epi64_mask(act, e, _mm512_set1_epi64(j));
            if (!need) break;
            b = _mm512_mask_mov_epi64(b, need, vmul(b, b, p, ninv));
        }
        V b2 = vmul(b, b, p, ninv);
        Mv = _mm512_mask_mov_epi64(Mv, act, iv);
        c = _mm512_mask_mov_epi64(c, act, b2);
        t = _mm512_mask_mov_epi64(t, act, vmul(t, b2, p, ninv));
        r = _mm512_mask_mov_epi64(r, act, vmul(r, b, p, ninv));
        act = _mm512_mask_cmpneq_epu64_mask(act, t, one);
    }
    return r;
}
static inline V vsqr_n(V x, V cnt, V p, V ninv) {     /* x^(2^cnt) lane-wise */
    for (int j = 0; ; j++) {
        __mmask8 need = _mm512_cmpgt_epi64_mask(cnt, _mm512_set1_epi64(j));
        if (!need) break;
        x = _mm512_mask_mov_epi64(x, need, vmul(x, x, p, ninv));
    }
    return x;
}

static int64_t CC[15][8];
static int primes_l[64], nl = 0;
static unsigned char qrl[64][256];
static void die(const char *w, uint64_t p) { fprintf(stderr, "%s %llu\n", w, (unsigned long long)p); exit(2); }

/* least prime l >= 7 with (p/l) = -1 (= (l/p) as p = 1 mod 4), as census_kw.c */
static inline uint64_t find_z(uint64_t p) {
    if (!qrl[0][p % 7]) return 7;
    if (!qrl[1][p % 11]) return 11;
    if (!qrl[2][p % 13]) return 13;
    if (!qrl[3][p % 17]) return 17;
    if (!qrl[4][p % 19]) return 19;
    if (!qrl[5][p % 23]) return 23;
    if (!qrl[6][p % 29]) return 29;
    if (!qrl[7][p % 31]) return 31;
    for (int li = 8; li < nl; li++) if (!qrl[li][p % (uint64_t)primes_l[li]]) return (uint64_t)primes_l[li];
    uint64_t z = 257; while (jac(z % p, p) != -1) z++;
    return z;
}

/* per-thread work arrays for one batch of candidates */
#define BATCH 4096
typedef struct {
    uint64_t p[BATCH + 8], ninv[BATCH + 8], one[BATCH + 8], r2[BATCH + 8], rm[BATCH + 8], c0n[BATCH + 8], rn[BATCH + 8];
    uint64_t p2[BATCH + 8], ninv2[BATCH + 8], one2[BATCH + 8], r22[BATCH + 8], rm2[BATCH + 8], c0n2[BATCH + 8], rn2[BATCH + 8];
    uint64_t c0m[BATCH + 8], c0m2[BATCH + 8];
    uint64_t z[BATCH + 8];
} work;

typedef struct { uint64_t XLO; uint64_t NB; unsigned MW1, MW2, WM; uint64_t *lbB; uint64_t c_v0, c_kw, c_kwdet, c_zeroW; FILE *ftxt; int check;
                 unsigned MW3; uint64_t *lbB3; uint64_t c_kw3, c_kw3det;
                 unsigned MW4; uint64_t *lbB4; uint64_t c_kw4, c_kw4det; } ctx;

enum { OUT_NOTKW = 0, OUT_DET = 1, OUT_UND = 2, OUT_ZEROW = 3, OUT_W3 = 4, OUT_W4 = 8 };

/* scalar treatment of a vector-0 prime p with sqrt 241 = r and c0 = z^q (both in normal form), as census_kw.c:
   outcome of each side and its r in normal form */
static void scalar_v0(uint64_t p, uint64_t rnorm, uint64_t c0norm, const ctx *X, int out[2], uint64_t rrn[2]) {
    mont M; mont_init(&M, p);
    uint64_t q = p - 1; int s = 0; while (!(q & 1)) { q >>= 1; s++; }
    uint64_t c0 = to_m(c0norm, &M), r = to_m(rnorm, &M);
    if (mmul(r, r, &M) != to_m(241 % p, &M)) die("sqrt241 check failed", p);
    { uint64_t zz = c0; for (int j = 0; j < s - 1; j++) zz = mmul(zz, zz, &M); if (zz != subm(0, M.one, p)) die("c0 order", p); }
    uint64_t rneg = subm(0, r, p);
    if (!(jac(alpha_n(1, r, &M), p) == 1 && jac(alpha_n(2, r, &M), p) == 1 &&
          jac(alpha_n(4, r, &M), p) == 1 && jac(alpha_n(6, r, &M), p) == 1)) die("vector-0 disagreement", p);
    uint64_t al[2][8];
    for (int side = 0; side < 2; side++) for (int k = 0; k < 8; k++) al[side][k] = to_m(alpha_n(k, side ? rneg : r, &M), &M);
    uint64_t m3 = to_m(3, &M), m5 = to_m(5, &M), x1, x2, x4, x6, x3, x5;
    pw2(al[0][1], (q - 1) / 2, al[0][2], (q - 1) / 2, &M, &x1, &x2);
    pw2(al[0][4], (q - 1) / 2, al[0][6], (q - 1) / 2, &M, &x4, &x6);
    pw2(m3, (q - 1) / 2, m5, (q - 1) / 2, &M, &x3, &x5);
    uint64_t s1 = ts_x(al[0][1], x1, &M, s, c0), s2 = ts_x(al[0][2], x2, &M, s, c0);
    uint64_t s4 = ts_x(al[0][4], x4, &M, s, c0), s6 = ts_x(al[0][6], x6, &M, s, c0);
    uint64_t r3 = ts_x(m3, x3, &M, s, c0), r5 = ts_x(m5, x5, &M, s, c0);
    uint64_t zi = c0; for (int j = 0; j < s - 2; j++) zi = mmul(zi, zi, &M);
    uint64_t z8 = c0; for (int j = 0; j < s - 3; j++) z8 = mmul(z8, z8, &M);
    uint64_t rt2 = mmul(z8, subm(M.one, zi, p), &M);
    uint64_t P12 = mmul(al[0][1], al[0][2], &M), P124 = mmul(P12, al[0][4], &M), P1246 = mmul(P124, al[0][6], &M);
    uint64_t iv = pw(P1246, p - 2, &M);
    uint64_t i6 = mmul(iv, P124, &M); iv = mmul(iv, al[0][6], &M);
    uint64_t i4 = mmul(iv, P12, &M); iv = mmul(iv, al[0][4], &M);
    uint64_t i2 = mmul(iv, al[0][1], &M), i1 = mmul(iv, al[0][2], &M);
    uint64_t sq[2][8];
    sq[0][0] = zi; sq[0][1] = s1; sq[0][2] = s2; sq[0][3] = mmul(mmul(rt2, s2, &M), i2, &M);
    sq[0][4] = s4; sq[0][5] = mmul(mmul(mmul(zi, r3, &M), s4, &M), i4, &M);
    sq[0][6] = s6; sq[0][7] = mmul(mmul(mmul(zi, r5, &M), s6, &M), i6, &M);
    sq[1][0] = zi; sq[1][1] = mmul(mmul(zi, s1, &M), i1, &M); sq[1][2] = mmul(zi, sq[0][3], &M);
    sq[1][3] = mmul(zi, s2, &M); sq[1][4] = sq[0][5]; sq[1][5] = s4; sq[1][6] = sq[0][7]; sq[1][7] = s6;
    for (int side = 0; side < 2; side++) for (int k = 0; k < 8; k++)
        if (al[side][k] == 0 || mmul(sq[side][k], sq[side][k], &M) != al[side][k]) die("sqrt failed", p);
    for (int side = 0; side < 2; side++) {
        uint64_t rr = side ? rneg : r;
        unsigned pat = 0; int zeroW = 0;
        for (int pass = 0; pass < 2; pass++) {
            for (int i = 0; i < NF; i++) {
                int inW = (X->WM >> i) & 1;
                if ((pass == 0) != inW) continue;
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
                    uint64_t t = mmul((uint64_t)(c > 0 ? c : -c), bas[j], &M);
                    val = c > 0 ? addm(val, t, p) : subm(val, t, p);
                }
                int jv = jac(val, p);
                if (jv == -1) pat |= 1u << i;
                if (jv == 0 && inW) zeroW = 1;
                if (pass == 1 && pat) break;
            }
            if (pass == 0) {
                int kerW = !(__builtin_popcount(pat & X->MW1) & 1) && !(__builtin_popcount(pat & X->MW2) & 1);
                if (!kerW || zeroW || pat) break;
            }
        }
        int kerW = !(__builtin_popcount(pat & X->MW1) & 1) && !(__builtin_popcount(pat & X->MW2) & 1);
        int kerW3 = kerW && !(__builtin_popcount(pat & X->MW3) & 1);
        int kerW4 = kerW3 && !(__builtin_popcount(pat & X->MW4) & 1);
        rrn[side] = from_m(rr, &M);
        out[side] = zeroW ? OUT_ZEROW : (!kerW ? OUT_NOTKW : pat ? OUT_DET : OUT_UND) | (kerW3 ? OUT_W3 : 0) | (kerW4 ? OUT_W4 : 0);
    }
}

static void record(ctx *X, uint64_t p, const int out[2], const uint64_t rrn[2]) {
    X->c_v0 += 2;
    uint64_t idx = (uint64_t)floor(log((double)p / (double)X->XLO) / log1p(H_BIN));
    if (idx >= X->NB) idx = X->NB - 1;
    for (int side = 0; side < 2; side++) {
        if (out[side] == OUT_ZEROW) {
            X->c_zeroW++;
            #pragma omp critical
            { fprintf(X->ftxt, "zeroW %llu %llu\n", (unsigned long long)p, (unsigned long long)rrn[side]); fflush(X->ftxt); }
            continue;
        }
        if (out[side] == OUT_NOTKW) continue;
        int base = out[side] & 3, w3 = (out[side] & OUT_W3) != 0, w4 = (out[side] & OUT_W4) != 0;
        if (base == OUT_NOTKW) die("ker W' outside ker W", p);
        if (w4 && !w3) die("ker W'' outside ker W'", p);
        X->c_kw++;
        if (w3) X->c_kw3++;
        if (w4) X->c_kw4++;
        if (base == OUT_DET) {
            X->c_kwdet++; X->lbB[idx]++;
            if (w3) { X->c_kw3det++; X->lbB3[idx]++; }
            if (w4) { X->c_kw4det++; X->lbB4[idx]++; }
        }
        else {
            if (!w4) die("undetected outside ker W''", p);
            #pragma omp critical
            { fprintf(X->ftxt, "undetected %llu %llu\n", (unsigned long long)p, (unsigned long long)rrn[side]); fflush(X->ftxt); }
        }
    }
}

/* 120 beta_i (normal form) at the prime of F0_i given by the square roots sq[] (Montgomery) */
static inline V vfield(int i, const V *sq, V rr, V p, V ninv, V one) {
    V sa = one, sb = one;
    for (int k = 0; k < 8; k++) {
        if ((R1[i] >> k) & 1) sa = vmul(sa, sq[k], p, ninv);
        if ((R2[i] >> k) & 1) sb = vmul(sb, sq[k], p, ninv);
    }
    V ssb = vmul(sa, sb, p, ninv);
    V bas[8] = {one, rr, sa, vmul(rr, sa, p, ninv), sb, vmul(rr, sb, p, ninv), ssb, vmul(rr, ssb, p, ninv)};
    V val = VZ;
    for (int j = 0; j < 8; j++) {
        int64_t c = CC[i][j];
        if (c == 0) continue;
        V t = vmul(_mm512_set1_epi64(c > 0 ? c : -c), bas[j], p, ninv);    /* |c| < 2^46: |c| bas_j, normal form */
        val = c > 0 ? vadd(val, t, p) : vsub(val, t, p);
    }
    return val;
}

/* vector-0 primes P[0..n), n <= 8, with Montgomery data and r, c0 in Montgomery form: outcomes as scalar_v0 */
static void vector_v0(const uint64_t *P, const uint64_t *N, const uint64_t *O, const uint64_t *R2a, const uint64_t *RM,
                      const uint64_t *C0M, int n, const ctx *X, int out[8][2], uint64_t rrn[8][2]) {
    __mmask8 valid = (__mmask8)((1u << n) - 1);
    const V v1 = _mm512_set1_epi64(1);
    V p = _mm512_mask_loadu_epi64(_mm512_set1_epi64((long long)P[0]), valid, P);       /* padding lanes copy lane 0 */
    V ninv = _mm512_mask_loadu_epi64(_mm512_set1_epi64((long long)N[0]), valid, N);
    V one = _mm512_mask_loadu_epi64(_mm512_set1_epi64((long long)O[0]), valid, O);
    V r2 = _mm512_mask_loadu_epi64(_mm512_set1_epi64((long long)R2a[0]), valid, R2a);
    V rm = _mm512_mask_loadu_epi64(_mm512_set1_epi64((long long)RM[0]), valid, RM);
    V c0 = _mm512_mask_loadu_epi64(_mm512_set1_epi64((long long)C0M[0]), valid, C0M);
    V pm1 = _mm512_sub_epi64(p, v1);
    V sv = _mm512_sub_epi64(_mm512_set1_epi64(63), _mm512_lzcnt_epi64(_mm512_and_si512(pm1, _mm512_sub_epi64(VZ, pm1))));
    V qv = _mm512_srlv_epi64(pm1, sv);
    V eh = _mm512_srli_epi64(_mm512_sub_epi64(qv, v1), 1);
    V inv2 = vmul(_mm512_srli_epi64(_mm512_add_epi64(p, v1), 1), r2, p, ninv);
    V rneg = vneg(rm, p);
    V mone = _mm512_sub_epi64(p, one);                                                /* -1 */
    V al[2][8];
    for (int k = 0; k < 8; k++) {
        V gam = vmul(_mm512_set1_epi64(GA[k] >= 0 ? GA[k] : -GA[k]), r2, p, ninv);
        V gbm = vmul(_mm512_set1_epi64(GB[k] >= 0 ? GB[k] : -GB[k]), r2, p, ninv);
        if (GA[k] < 0) gam = vneg(gam, p);
        if (GB[k] < 0) gbm = vneg(gbm, p);
        for (int side = 0; side < 2; side++) {
            V v = vadd(gam, vmul(gbm, side ? rneg : rm, p, ninv), p);
            if (GD[k] == 2) v = vmul(v, inv2, p, ninv);
            al[side][k] = v;
        }
    }
    V m3 = vmul(_mm512_set1_epi64(3), r2, p, ninv), m5 = vmul(_mm512_set1_epi64(5), r2, p, ninv);
    V x1, x2, x4, x6, x3, x5;
    vpow2(al[0][1], eh, al[0][2], eh, p, ninv, one, &x1, &x2);
    vpow2(al[0][4], eh, al[0][6], eh, p, ninv, one, &x4, &x6);
    vpow2(m3, eh, m5, eh, p, ninv, one, &x3, &x5);
    V s1 = vts(al[0][1], x1, c0, sv, p, ninv, one, 0xFF), s2 = vts(al[0][2], x2, c0, sv, p, ninv, one, 0xFF);
    V s4 = vts(al[0][4], x4, c0, sv, p, ninv, one, 0xFF), s6 = vts(al[0][6], x6, c0, sv, p, ninv, one, 0xFF);
    V r3 = vts(m3, x3, c0, sv, p, ninv, one, 0xFF), r5 = vts(m5, x5, c0, sv, p, ninv, one, 0xFF);
    V zi = vsqr_n(c0, _mm512_sub_epi64(sv, _mm512_set1_epi64(2)), p, ninv);
    V z8 = vsqr_n(c0, _mm512_sub_epi64(sv, _mm512_set1_epi64(3)), p, ninv);
    V rt2 = vmul(z8, vsub(one, zi, p), p, ninv);
    V P12 = vmul(al[0][1], al[0][2], p, ninv), P124 = vmul(P12, al[0][4], p, ninv), P1246 = vmul(P124, al[0][6], p, ninv);
    V iv = vpow(P1246, _mm512_sub_epi64(p, _mm512_set1_epi64(2)), p, ninv, one);
    V i6 = vmul(iv, P124, p, ninv); iv = vmul(iv, al[0][6], p, ninv);
    V i4 = vmul(iv, P12, p, ninv); iv = vmul(iv, al[0][4], p, ninv);
    V i2 = vmul(iv, al[0][1], p, ninv), i1 = vmul(iv, al[0][2], p, ninv);
    V sq[2][8];
    sq[0][0] = zi; sq[0][1] = s1; sq[0][2] = s2; sq[0][3] = vmul(vmul(rt2, s2, p, ninv), i2, p, ninv);
    sq[0][4] = s4; sq[0][5] = vmul(vmul(vmul(zi, r3, p, ninv), s4, p, ninv), i4, p, ninv);
    sq[0][6] = s6; sq[0][7] = vmul(vmul(vmul(zi, r5, p, ninv), s6, p, ninv), i6, p, ninv);
    sq[1][0] = zi; sq[1][1] = vmul(vmul(zi, s1, p, ninv), i1, p, ninv); sq[1][2] = vmul(zi, sq[0][3], p, ninv);
    sq[1][3] = vmul(zi, s2, p, ninv); sq[1][4] = sq[0][5]; sq[1][5] = s4; sq[1][6] = sq[0][7]; sq[1][7] = s6;
    for (int side = 0; side < 2; side++) for (int k = 0; k < 8; k++)
        if (_mm512_mask_cmpeq_epu64_mask(valid, al[side][k], VZ) ||
            _mm512_mask_cmpneq_epu64_mask(valid, vmul(sq[side][k], sq[side][k], p, ninv), al[side][k])) die("vector sqrt failed", P[0]);
    V e2 = _mm512_srli_epi64(pm1, 1);
    for (int side = 0; side < 2; side++) {
        V rr = side ? rneg : rm;
        unsigned pat[8] = {0}; __mmask8 zeroW = 0;
        for (int i = 0; i < NF; i++) {
            if (!((X->WM >> i) & 1)) continue;
            V lg = vpow(vfield(i, sq[side], rr, p, ninv, one), e2, p, ninv, one);
            __mmask8 nr = _mm512_mask_cmpeq_epu64_mask(valid, lg, mone), zr = _mm512_mask_cmpeq_epu64_mask(valid, lg, VZ);
            if (valid & (__mmask8)~(nr | zr | _mm512_cmpeq_epu64_mask(lg, one))) die("Euler criterion (field)", P[0]);
            for (int l = 0; l < n; l++) if ((nr >> l) & 1) pat[l] |= 1u << i;
            zeroW |= zr;
        }
        int kerW[8];
        __mmask8 need = 0;
        for (int l = 0; l < n; l++) {
            kerW[l] = !(__builtin_popcount(pat[l] & X->MW1) & 1) && !(__builtin_popcount(pat[l] & X->MW2) & 1);
            if (!((zeroW >> l) & 1) && kerW[l] && !pat[l]) need |= (__mmask8)(1u << l);
        }
        for (int i = 0; i < NF && need; i++) {
            if ((X->WM >> i) & 1) continue;
            V lg = vpow(vfield(i, sq[side], rr, p, ninv, one), e2, p, ninv, one);
            __mmask8 nr = _mm512_mask_cmpeq_epu64_mask(need, lg, mone);
            for (int l = 0; l < n; l++) if ((nr >> l) & 1) pat[l] |= 1u << i;
            need &= (__mmask8)~nr;
        }
        uint64_t rv[8];
        _mm512_storeu_si512(rv, vmul(rr, v1, p, ninv));
        for (int l = 0; l < n; l++) {
            rrn[l][side] = rv[l];
            int kerW3 = kerW[l] && !(__builtin_popcount(pat[l] & X->MW3) & 1);
            int kerW4 = kerW3 && !(__builtin_popcount(pat[l] & X->MW4) & 1);
            out[l][side] = ((zeroW >> l) & 1) ? OUT_ZEROW : (!kerW[l] ? OUT_NOTKW : pat[l] ? OUT_DET : OUT_UND) | (kerW3 ? OUT_W3 : 0) | (kerW4 ? OUT_W4 : 0);
        }
    }
}

/* the candidates W->p[0..n): sqrt 241, vector-0 test, then process_v0 on the survivors */
static void process_batch(work *W, int n, ctx *X) {
    if (n == 0) return;
    for (int i = n; i < ((n + 7) & ~7); i++) { W->p[i] = W->p[n - 1]; W->z[i] = W->z[n - 1]; }   /* padding lanes */
    int nv = (n + 7) & ~7;
    const V v1 = _mm512_set1_epi64(1);
    for (int i = 0; i < nv; i += 8) {
        V p = _mm512_loadu_si512(W->p + i);
        /* -p^-1 mod 2^52 */
        V x = p;
        for (int k = 0; k < 5; k++) x = _mm512_mullo_epi64(x, _mm512_sub_epi64(_mm512_set1_epi64(2), _mm512_mullo_epi64(p, x)));
        V ninv = _mm512_and_si512(_mm512_sub_epi64(VZ, x), _mm512_set1_epi64((1LL << 52) - 1));
        /* 2^52 mod p and 2^104 mod p by doubling */
        V one = v1;
        for (int k = 0; k < 52; k++) one = vadd(one, one, p);
        V r2 = one;
        for (int k = 0; k < 52; k++) r2 = vadd(r2, r2, p);
        V qv, sv;
        {   /* p - 1 = q 2^s */
            V pm1 = _mm512_sub_epi64(p, v1);
            V low = _mm512_and_si512(pm1, _mm512_sub_epi64(VZ, pm1));               /* lowest set bit */
            sv = _mm512_sub_epi64(_mm512_set1_epi64(63), _mm512_lzcnt_epi64(low));
            qv = _mm512_srlv_epi64(pm1, sv);
        }
        V zm = vmul(_mm512_loadu_si512(W->z + i), r2, p, ninv);
        V am = vmul(_mm512_set1_epi64(241), r2, p, ninv);
        V c0, xa;
        vpow2(zm, qv, am, _mm512_srli_epi64(_mm512_sub_epi64(qv, v1), 1), p, ninv, one, &c0, &xa);
        /* Tonelli-Shanks */
        V r = vmul(am, xa, p, ninv), t = vmul(r, xa, p, ninv), c = c0, Mv = sv;
        __mmask8 act = _mm512_cmpneq_epu64_mask(t, one);
        while (act) {
            V tt = t, iv = VZ; __mmask8 found = 0;
            for (int k = 1; ; k++) {
                tt = vmul(tt, tt, p, ninv);
                __mmask8 eq = _mm512_cmpeq_epu64_mask(tt, one) & act & (__mmask8)~found;
                iv = _mm512_mask_mov_epi64(iv, eq, _mm512_set1_epi64(k));
                found |= eq;
                if ((found & act) == act) break;
                if (k > 62) die("TS loop", 0);
            }
            if (_mm512_mask_cmpge_epi64_mask(act, iv, Mv)) die("241 not a square", 0);
            V e = _mm512_sub_epi64(_mm512_sub_epi64(Mv, iv), v1);
            V b = c;
            for (int j = 0; ; j++) {
                __mmask8 need = _mm512_mask_cmpgt_epi64_mask(act, e, _mm512_set1_epi64(j));
                if (!need) break;
                b = _mm512_mask_mov_epi64(b, need, vmul(b, b, p, ninv));
            }
            V b2 = vmul(b, b, p, ninv);
            Mv = _mm512_mask_mov_epi64(Mv, act, iv);
            c = _mm512_mask_mov_epi64(c, act, b2);
            t = _mm512_mask_mov_epi64(t, act, vmul(t, b2, p, ninv));
            r = _mm512_mask_mov_epi64(r, act, vmul(r, b, p, ninv));
            act = _mm512_mask_cmpneq_epu64_mask(act, t, one);
        }
        if (_mm512_cmpneq_epu64_mask(vmul(r, r, p, ninv), am)) die("vector sqrt241 failed", 0);
        _mm512_storeu_si512(W->ninv + i, ninv); _mm512_storeu_si512(W->one + i, one); _mm512_storeu_si512(W->r2 + i, r2);
        _mm512_storeu_si512(W->rm + i, r);
        _mm512_storeu_si512(W->rn + i, vmul(r, v1, p, ninv));       /* normal forms */
        _mm512_storeu_si512(W->c0n + i, vmul(c0, v1, p, ninv));
        _mm512_storeu_si512(W->c0m + i, c0);
    }
    /* four rounds of Euler's criterion with compaction; arrays alternate between W->x and W->x2 */
    static const int KS[4] = {1, 2, 4, 6};
    int cnt = n;
    uint64_t *P = W->p, *N = W->ninv, *O = W->one, *R2a = W->r22 - 0, *RM = W->rm, *C0 = W->c0n, *RN = W->rn;
    R2a = W->r2;
    uint64_t *Pn = W->p2, *Nn = W->ninv2, *On = W->one2, *R2n = W->r22, *RMn = W->rm2, *C0n = W->c0n2, *RNn = W->rn2;
    uint64_t *CM = W->c0m, *CMn = W->c0m2;
    for (int round = 0; round < 4 && cnt > 0; round++) {
        int k = KS[round];
        int out = 0;
        for (int i = 0; i < cnt; i += 16) {
            V pv[2], nv[2], ov[2], r2v[2], rmv[2], alv[2], ev[2], lg[2];
            __mmask8 valid[2];
            for (int h = 0; h < 2; h++) {
                int j = i + 8 * h;
                valid[h] = (cnt - j >= 8) ? 0xFF : (cnt - j <= 0) ? 0 : (__mmask8)((1u << (cnt - j)) - 1);
                V p = _mm512_maskz_loadu_epi64(valid[h], P + j);
                p = _mm512_mask_mov_epi64(_mm512_set1_epi64(7), valid[h], p);         /* inactive lanes: p = 7 */
                V ninv = _mm512_maskz_loadu_epi64(valid[h], N + j), one = _mm512_maskz_loadu_epi64(valid[h], O + j);
                V r2 = _mm512_maskz_loadu_epi64(valid[h], R2a + j), rm = _mm512_maskz_loadu_epi64(valid[h], RM + j);
                /* alpha_k = GA + GB r (the halving of alpha_2 is dropped) in Montgomery form */
                V ga = _mm512_set1_epi64(GA[k] >= 0 ? GA[k] : -GA[k]), gb = _mm512_set1_epi64(GB[k] >= 0 ? GB[k] : -GB[k]);
                V gam = vmul(ga, r2, p, ninv), gbm = vmul(gb, r2, p, ninv);
                if (GA[k] < 0) gam = vneg(gam, p);
                if (GB[k] < 0) gbm = vneg(gbm, p);
                pv[h] = p; nv[h] = ninv; ov[h] = one; r2v[h] = r2; rmv[h] = rm;
                alv[h] = vadd(gam, vmul(gbm, rm, p, ninv), p);
                ev[h] = _mm512_srli_epi64(_mm512_sub_epi64(p, _mm512_set1_epi64(1)), 1);
            }
            vpowd(alv[0], ev[0], pv[0], nv[0], ov[0], alv[1], ev[1], pv[1], nv[1], ov[1], &lg[0], &lg[1]);
            for (int h = 0; h < 2; h++) {
                int j = i + 8 * h;
                if (!valid[h]) continue;
                __mmask8 ok = _mm512_mask_cmpeq_epu64_mask(valid[h], lg[h], ov[h]);
                __mmask8 bad = _mm512_mask_cmpneq_epu64_mask(valid[h], lg[h], _mm512_sub_epi64(pv[h], ov[h])) & (__mmask8)~ok;
                if (bad) die("Euler criterion neither 1 nor -1", 0);
                _mm512_mask_compressstoreu_epi64(Pn + out, ok, pv[h]);
                _mm512_mask_compressstoreu_epi64(Nn + out, ok, nv[h]);
                _mm512_mask_compressstoreu_epi64(On + out, ok, ov[h]);
                _mm512_mask_compressstoreu_epi64(R2n + out, ok, r2v[h]);
                _mm512_mask_compressstoreu_epi64(RMn + out, ok, rmv[h]);
                _mm512_mask_compressstoreu_epi64(C0n + out, ok, _mm512_maskz_loadu_epi64(valid[h], C0 + j));
                _mm512_mask_compressstoreu_epi64(RNn + out, ok, _mm512_maskz_loadu_epi64(valid[h], RN + j));
                _mm512_mask_compressstoreu_epi64(CMn + out, ok, _mm512_maskz_loadu_epi64(valid[h], CM + j));
                out += __builtin_popcount(ok);
            }
        }
        uint64_t *t;
        t = P; P = Pn; Pn = t;  t = N; N = Nn; Nn = t;  t = O; O = On; On = t;  t = R2a; R2a = R2n; R2n = t;
        t = RM; RM = RMn; RMn = t;  t = C0; C0 = C0n; C0n = t;  t = RN; RN = RNn; RNn = t;  t = CM; CM = CMn; CMn = t;
        cnt = out;
    }
    for (int i = 0; i < cnt; i += 8) {
        int m = cnt - i < 8 ? cnt - i : 8;
        int out[8][2]; uint64_t rrn[8][2];
        vector_v0(P + i, N + i, O + i, R2a + i, RM + i, CM + i, m, X, out, rrn);
        for (int l = 0; l < m; l++) {
            if (X->check == 1 || ((P[i + l] / 120) & 15) == 0) {          /* Wcheck: all; W: about 1 in 16 */
                int o2[2]; uint64_t r2n[2];
                scalar_v0(P[i + l], RN[i + l], C0[i + l], X, o2, r2n);
                if (o2[0] != out[l][0] || o2[1] != out[l][1] || r2n[0] != rrn[l][0] || r2n[1] != rrn[l][1]) die("vector/scalar outcome mismatch", P[i + l]);
            }
            record(X, P[i + l], out[l], rrn[l]);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 11 || (strcmp(argv[8], "W") && strcmp(argv[8], "Wcheck"))) { fprintf(stderr, "usage: census_kv4 XLO XHI nthreads prefix CH MW1 MW2 W|Wcheck MW3 MW4\n"); return 1; }
    int check = !strcmp(argv[8], "Wcheck");
    uint64_t XLO = (uint64_t)strtod(argv[1], NULL), XHI = (uint64_t)strtod(argv[2], NULL);
    int nth = atoi(argv[3]);
    const char *prefix = argv[4];
    unsigned MW1 = (unsigned)strtoul(argv[6], NULL, 0), MW2 = (unsigned)strtoul(argv[7], NULL, 0), MW3 = (unsigned)strtoul(argv[9], NULL, 0);
    if (MW3 == 0 || (MW3 & ~(MW1 | MW2)) || MW3 == MW1 || MW3 == MW2 || MW3 == (MW1 ^ MW2)) { fprintf(stderr, "MW3 must be a new functional inside MW1 | MW2\n"); return 1; }
    unsigned MW4 = (unsigned)strtoul(argv[10], NULL, 0);
    { int dep = 0; for (int m = 0; m < 8; m++) { unsigned v = ((m & 1) ? MW1 : 0) ^ ((m & 2) ? MW2 : 0) ^ ((m & 4) ? MW3 : 0); if (v == MW4) dep = 1; }
      if (MW4 == 0 || (MW4 & ~(MW1 | MW2)) || dep) { fprintf(stderr, "MW4 must be a new functional inside MW1 | MW2\n"); return 1; } }
    if (XHI >= (1ULL << 50) || XLO < 1000) { fprintf(stderr, "need 1000 <= XLO < XHI < 2^50\n"); return 1; }
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
    if (primes_l[0] != 7 || primes_l[7] != 31) { fprintf(stderr, "prime table\n"); return 1; }
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
    uint64_t kmin = XLO / 120, kmax = XHI / 120 + 1;
    uint64_t nsegk = (kmax - kmin) / SEGK + 1;
    uint64_t SPB = (nsegk + 63) / 64;                                 /* segments per block */
    uint64_t nblk = (nsegk + SPB - 1) / SPB;
    uint64_t *rq[2];
    for (int ai = 0; ai < 2; ai++) {                                   /* q | a + 120 k  <=>  k = rq mod q */
        rq[ai] = malloc(sizeof(uint64_t) * nbp);
        for (size_t k = 0; k < nbp; k++) {
            uint64_t q = bp[k];
            if (q <= 5) { rq[ai][k] = 0; continue; }
            uint64_t r = 1, a = 120 % q, e = q - 2;
            while (e) { if (e & 1) r = (uint64_t)((u128)r * a % q); a = (uint64_t)((u128)a * a % q); e >>= 1; }
            rq[ai][k] = (uint64_t)((u128)((q - AA[ai] % q) % q) * r % q);
        }
    }
    /* periodic word patterns: the term a + 120 k is marked if it is divisible by l = 7..31, or if it is 0 or a
       nonresidue mod 241; PAT[ai][mi][ph] has bit t set iff the term with k = ph + t mod MODS[mi] is marked */
    static const uint64_t MODS[9] = {241, 7, 11, 13, 17, 19, 23, 29, 31};
    uint64_t *PAT[2][9];
    for (int ai = 0; ai < 2; ai++) for (int mi = 0; mi < 9; mi++) {
        uint64_t m = MODS[mi];
        PAT[ai][mi] = malloc(sizeof(uint64_t) * m);
        for (uint64_t ph = 0; ph < m; ph++) {
            uint64_t w = 0;
            for (int t = 0; t < 64; t++) {
                uint64_t v = (AA[ai] + 120 * ((ph + t) % m)) % m;
                if (mi == 0 ? (v == 0 || !qr241[v]) : (v == 0)) w |= 1ULL << t;
            }
            PAT[ai][mi][ph] = w;
        }
    }
    const uint64_t NW = SEGK / 64;
    uint64_t *bins = calloc(NB, sizeof(uint64_t)), *bins3 = calloc(NB, sizeof(uint64_t)), *bins4 = calloc(NB, sizeof(uint64_t));
    uint64_t tot_cand = 0, tot_v0 = 0, tot_kw = 0, tot_kwdet = 0, tot_zeroW = 0, tot_kw3 = 0, tot_kw3det = 0, tot_kw4 = 0, tot_kw4det = 0;
    FILE *ftxt; char fn[512];
    snprintf(fn, sizeof fn, "%s.txt", prefix); ftxt = fopen(fn, "w");
    #pragma omp parallel
    {
        uint64_t *seg = malloc(sizeof(uint64_t) * (SEGK / 64));
        uint64_t *nxt = malloc(sizeof(uint64_t) * nbp);
        work *W = aligned_alloc(64, (sizeof(work) + 63) / 64 * 64);
        ctx X = {XLO, NB, MW1, MW2, MW1 | MW2, calloc(NB, sizeof(uint64_t)), 0, 0, 0, 0, ftxt, check,
                 MW3, calloc(NB, sizeof(uint64_t)), 0, 0, MW4, calloc(NB, sizeof(uint64_t)), 0, 0};
        uint64_t c_cand = 0;
        #pragma omp for schedule(dynamic, 1)
        for (uint64_t job = 0; job < 2 * nblk; job++) {
            int ai = (int)(job & 1);
            uint64_t a = AA[ai];
            uint64_t S0 = (job >> 1) * SPB, S1 = S0 + SPB; if (S1 > nsegk) S1 = nsegk;
            if (S0 >= S1) continue;
            uint64_t K0b = kmin + S0 * SEGK;
            for (size_t k = 0; k < nbp; k++) {                         /* first sieve index >= K0b and >= q^2 */
                uint64_t q = bp[k];
                if (q <= 5) { nxt[k] = UINT64_MAX; continue; }
                uint64_t kk = K0b + (rq[ai][k] + q - K0b % q) % q;
                uint64_t kq = (q * q > a) ? (q * q - a + 119) / 120 : 0;
                if (kk < kq) kk += ((kq - kk + q - 1) / q) * q;
                nxt[k] = kk;
            }
            for (uint64_t sg = S0; sg < S1; sg++) {
                uint64_t K0 = kmin + sg * SEGK, K1 = K0 + SEGK - 1;
                uint64_t nlo = a + 120 * K0, nhi = a + 120 * K1;
                if (nlo > XHI) break;
                uint64_t ph[9], st[9];
                for (int mi = 0; mi < 9; mi++) { ph[mi] = K0 % MODS[mi]; st[mi] = 64 % MODS[mi]; }
                for (uint64_t w = 0; w < NW; w++) {
                    uint64_t x = 0;
                    for (int mi = 0; mi < 9; mi++) {
                        x |= PAT[ai][mi][ph[mi]];
                        ph[mi] += st[mi]; if (ph[mi] >= MODS[mi]) ph[mi] -= MODS[mi];
                    }
                    seg[w] = x;
                }
                for (size_t k = 0; k < nbp; k++) {
                    uint64_t q = bp[k];
                    if (q <= 31) continue;
                    if (q * q > nhi) break;
                    uint64_t kk = nxt[k];
                    for (; kk <= K1; kk += q) { uint64_t o = kk - K0; seg[o >> 6] |= 1ULL << (o & 63); }
                    nxt[k] = kk;
                }
                int n = 0;
                for (uint64_t w = 0; w < NW; w++) {
                  uint64_t bits = ~seg[w];
                  while (bits) {
                    int t = __builtin_ctzll(bits); bits &= bits - 1;
                    uint64_t kk = K0 + 64 * w + (uint64_t)t;
                    uint64_t p = a + 120 * kk;
                    if (p <= XLO || p > XHI) continue;
                    if (!qr241[p % 241]) die("sieve pattern", p);
                    c_cand++;
                    uint64_t z = find_z(p);
                    W->p[n] = p; W->z[n] = z; n++;
                    if (n == BATCH) { process_batch(W, n, &X); n = 0; }
                  }
                }
                process_batch(W, n, &X);
            }
        }
        #pragma omp critical
        {
            for (uint64_t j = 0; j < NB; j++) { bins[j] += X.lbB[j]; bins3[j] += X.lbB3[j]; bins4[j] += X.lbB4[j]; }
            tot_cand += c_cand; tot_v0 += X.c_v0; tot_kw += X.c_kw; tot_kwdet += X.c_kwdet; tot_zeroW += X.c_zeroW;
            tot_kw3 += X.c_kw3; tot_kw3det += X.c_kw3det; tot_kw4 += X.c_kw4; tot_kw4det += X.c_kw4det;
        }
        free(seg); free(nxt); free(W); free(X.lbB); free(X.lbB3); free(X.lbB4);
    }
    fprintf(ftxt, "XLO %llu XHI %llu H 2^-16 NB %llu candidates %llu v0 %llu kerW %llu kerW_detected %llu zeroW %llu mode W\n",
            (unsigned long long)XLO, (unsigned long long)XHI, (unsigned long long)NB, (unsigned long long)tot_cand,
            (unsigned long long)tot_v0, (unsigned long long)tot_kw, (unsigned long long)tot_kwdet, (unsigned long long)tot_zeroW);
    fprintf(ftxt, "W3 MW3 0x%x kerW3 %llu kerW3_detected %llu\n", MW3, (unsigned long long)tot_kw3, (unsigned long long)tot_kw3det);
    fprintf(ftxt, "W4 MW4 0x%x kerW4 %llu kerW4_detected %llu\n", MW4, (unsigned long long)tot_kw4, (unsigned long long)tot_kw4det);
    fclose(ftxt);
    snprintf(fn, sizeof fn, "%s.binsBW", prefix);
    FILE *fb = fopen(fn, "wb"); fwrite(bins, sizeof(uint64_t), NB, fb); fclose(fb);
    snprintf(fn, sizeof fn, "%s.binsBW3", prefix);
    fb = fopen(fn, "wb"); fwrite(bins3, sizeof(uint64_t), NB, fb); fclose(fb);
    snprintf(fn, sizeof fn, "%s.binsBW4", prefix);
    fb = fopen(fn, "wb"); fwrite(bins4, sizeof(uint64_t), NB, fb); fclose(fb);
    printf("XLO %llu XHI %llu NB %llu candidates %llu v0 %llu kerW %llu kerW_detected %llu zeroW %llu\n",
           (unsigned long long)XLO, (unsigned long long)XHI, (unsigned long long)NB, (unsigned long long)tot_cand,
           (unsigned long long)tot_v0, (unsigned long long)tot_kw, (unsigned long long)tot_kwdet, (unsigned long long)tot_zeroW);
    printf("W3 MW3 0x%x kerW3 %llu kerW3_detected %llu\n", MW3, (unsigned long long)tot_kw3, (unsigned long long)tot_kw3det);
    printf("W4 MW4 0x%x kerW4 %llu kerW4_detected %llu\n", MW4, (unsigned long long)tot_kw4, (unsigned long long)tot_kw4det);
    return 0;
}
