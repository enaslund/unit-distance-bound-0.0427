/* Frobenius census for the tower over B = Q(sqrt 241).
 *
 * For every prime ideal P of B with norm N(P) <= X, not above 2,3,5,7,29:
 *   v(P) = degree-one Frobenius vector: bit i set iff alpha_i is a nonsquare mod P
 *   f_rel(P) >= 1 if v = 0; >= 2 if v != 0; >= 4 if v != 0 and S(v) not in R2.
 * Accumulates  sum_P a1(N(P)^f) / (2 f),  a1(q) = -log(1 - 1/q),
 * separately for the three categories, in long double.
 * Usage: census241 X nthreads
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>

typedef unsigned __int128 u128;
static const int64_t GA[8] = {-1, -71011068, -6101, 6101, 31, 31, 326, 326};
static const int64_t GB[8] = {0, 4574225, -393, -393, -2, 2, -21, 21};
static const int64_t GD[8] = {1, 1, 2, 2, 1, 1, 1, 1};
static const int64_t NORMS[8] = {1, -1, -2, -2, -3, -3, -5, -5};
static int SQINR[256];

static uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) { return (uint64_t)((u128)a * b % m); }
static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m) {
    uint64_t r = 1; a %= m;
    while (e) { if (e & 1) r = mulmod(r, a, m); a = mulmod(a, a, m); e >>= 1; }
    return r;
}
static int jacobi(int64_t a0, uint64_t n) { /* n odd positive */
    uint64_t a; int s = 1;
    int64_t t = a0 % (int64_t)n; if (t < 0) t += n; a = (uint64_t)t;
    while (a) {
        while (!(a & 1)) { a >>= 1; uint64_t r = n & 7; if (r == 3 || r == 5) s = -s; }
        uint64_t tmp = a; a = n; n = tmp;
        if ((a & 3) == 3 && (n & 3) == 3) s = -s;
        a %= n;
    }
    return n == 1 ? s : 0;
}
static uint64_t sqrtmod(uint64_t a, uint64_t p) {
    a %= p;
    if ((p & 3) == 3) return powmod(a, (p + 1) / 4, p);
    uint64_t q = p - 1; int s = 0;
    while (!(q & 1)) { q >>= 1; s++; }
    uint64_t z = 2; while (jacobi((int64_t)z, p) != -1) z++;
    int m = s; uint64_t c = powmod(z, q, p), t = powmod(a, q, p), r = powmod(a, (q + 1) / 2, p);
    while (t != 1) {
        int i = 0; uint64_t tt = t;
        while (tt != 1) { tt = mulmod(tt, tt, p); i++; }
        uint64_t b = c; for (int j = 0; j < m - i - 1; j++) b = mulmod(b, b, p);
        m = i; c = mulmod(b, b, p); t = mulmod(t, c, p); r = mulmod(r, b, p);
    }
    return r;
}
static long double a1(long double q) { return -log1pl(-1.0L / q); }

int main(int argc, char **argv) {
    uint64_t X = (uint64_t)strtod(argv[1], NULL);
    int nth = argc > 2 ? atoi(argv[2]) : 8;
    FILE *fp = fopen("sqinR.txt", "r");
    for (int i = 0; i < 256; i++) if (fscanf(fp, "%d", &SQINR[i]) != 1) return 1;
    fclose(fp);
    uint64_t sq = (uint64_t)sqrtl((long double)X) + 2;
    /* base primes up to sqrt(X) */
    char *small = calloc(sq + 1, 1);
    uint64_t *bp = malloc(sizeof(uint64_t) * (sq + 1)); size_t nbp = 0;
    for (uint64_t i = 2; i <= sq; i++) if (!small[i]) { bp[nbp++] = i; for (uint64_t j = i * i; j <= sq; j += i) small[j] = 1; }
    long double S1 = 0, S2 = 0, S4 = 0; long long n1 = 0, n2 = 0, n4 = 0;
    const uint64_t SEG = 1u << 22;
    uint64_t nseg = X / SEG + 1;
    omp_set_num_threads(nth);
#pragma omp parallel for schedule(dynamic, 4) reduction(+:S1,S2,S4,n1,n2,n4)
    for (uint64_t sg = 0; sg < nseg; sg++) {
        uint64_t lo = sg * SEG, hi = lo + SEG; if (hi > X + 1) hi = X + 1; if (lo >= hi) continue;
        char *mark = calloc(SEG, 1);
        for (size_t k = 0; k < nbp; k++) {
            uint64_t p = bp[k]; if (p * p >= hi) break;
            uint64_t st = (lo + p - 1) / p * p; if (st < p * p) st = p * p;
            for (uint64_t j = st; j < hi; j += p) mark[j - lo] = 1;
        }
        for (uint64_t n = (lo < 2 ? 2 : lo); n < hi; n++) {
            if (mark[n - lo]) continue;
            uint64_t p = n;
            if (p == 2 || p == 3 || p == 5 || p == 7 || p == 29) continue;
            if (p == 241) {
                int code = 0;
                for (int i = 0; i < 8; i++) { int64_t x = GA[i] % 241; if (GD[i] == 2) x = x * 121 % 241; /* 2^-1 = 121 mod 241 */
                    if (jacobi(x, 241) == -1) code |= 1 << i; }
                int f = code == 0 ? 1 : (SQINR[code] ? 2 : 4);
                long double c = a1(powl(241.0L, f)) / (2 * f);
                if (f == 1) { S1 += c; n1++; } else if (f == 2) { S2 += c; n2++; } else { S4 += c; n4++; }
                continue;
            }
            int j = jacobi(241, p);
            if (j == 1) {
                uint64_t r = sqrtmod(241, p);
                uint64_t inv2 = (p + 1) / 2;
                for (int side = 0; side < 2; side++) {
                    uint64_t rr = side ? p - r : r; int code = 0;
                    for (int i = 0; i < 8; i++) {
                        int64_t a = GA[i] % (int64_t)p; if (a < 0) a += p;
                        int64_t b = GB[i] % (int64_t)p; if (b < 0) b += p;
                        uint64_t x = ((uint64_t)a + mulmod((uint64_t)b, rr, p)) % p;
                        if (GD[i] == 2) x = mulmod(x, inv2, p);
                        if (jacobi((int64_t)x, p) == -1) code |= 1 << i;
                    }
                    int f = code == 0 ? 1 : (SQINR[code] ? 2 : 4);
                    long double c = a1(powl((long double)p, f)) / (2 * f);
                    if (f == 1) { S1 += c; n1++; } else if (f == 2) { S2 += c; n2++; } else { S4 += c; n4++; }
                }
            } else if (j == -1) {
                if ((u128)p * p > X) continue;
                int code = 0;
                for (int i = 0; i < 8; i++) if (jacobi(NORMS[i], p) == -1) code |= 1 << i;
                int f = code == 0 ? 1 : (SQINR[code] ? 2 : 4);
                long double c = a1(powl((long double)p, 2 * f)) / (2 * f);
                if (f == 1) { S1 += c; n1++; } else if (f == 2) { S2 += c; n2++; } else { S4 += c; n4++; }
            }
        }
        free(mark);
    }
    printf("X %llu\n", (unsigned long long)X);
    printf("v0 (f>=1): count %lld sum %.15Le\n", n1, S1);
    printf("f>=2     : count %lld sum %.15Le\n", n2, S2);
    printf("f>=4     : count %lld sum %.15Le\n", n4, S4);
    printf("middle total %.15Le\n", S1 + S2 + S4);
    return 0;
}
