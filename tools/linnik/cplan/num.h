/* The integers of the planner: Python's unbounded integers where they are wider than 64 bits, as fixed widths with
   every overflow fatal (the plan is then exactly the Python planner's, or the program stops), and Python's mixed
   integer and float arithmetic (an integer rounded to a float, an integer compared with a float, both exact). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

typedef __int128 i128;
typedef unsigned __int128 u128;
typedef uint64_t u64;
typedef int64_t i64;
typedef uint32_t u32;

#include <setjmp.h>

/* a run that may fail without stopping the program (the generator's reading of a part's hints in the other format,
   `gen.h`): a failed check returns to it */
static jmp_buf *DIEJMP;
static void die(const char *msg) {
    if (DIEJMP) longjmp(*DIEJMP, 1);
    fprintf(stderr, "hint_plan: %s\n", msg);
    exit(3);
}
#define CHECK(c, msg) do { if (!(c)) die(msg); } while (0)

static inline i64 tsub(i64 a, i64 b) { return a > b ? a - b : 0; }
static inline i128 tsubI(i128 a, i128 b) { return a > b ? a - b : 0; }
static inline i64 min64(i64 a, i64 b) { return b < a ? b : a; }    /* Python's min: the first on a tie */
static inline i64 max64(i64 a, i64 b) { return b > a ? b : a; }
static inline i128 minI(i128 a, i128 b) { return b < a ? b : a; }
static inline i128 maxI(i128 a, i128 b) { return b > a ? b : a; }
/* (a + b - 1) // b for a >= 0, b > 0 */
static inline i128 cdivI(i128 a, i128 b) {
    CHECK(a >= 0 && b > 0, "cdiv of a negative");
    return (a + b - 1) / b;
}
static inline i128 fdivI(i128 a, i128 b) {          /* a // b, b > 0 */
    CHECK(b > 0, "floor division by a nonpositive");
    i128 q = a / b;
    if ((a % b != 0) && (a < 0)) q -= 1;
    return q;
}

/* ---------------------------------------------------------------------------------------------------------------
   U: 256-bit unsigned. */
typedef struct { u64 w[4]; } U;

static inline U U0(void) { U r = {{0, 0, 0, 0}}; return r; }
static inline U Uu(u128 x) { U r = {{(u64)x, (u64)(x >> 64), 0, 0}}; return r; }
static inline U Ui(i128 x) { CHECK(x >= 0, "U of a negative"); return Uu((u128)x); }
static inline int Uz(U a) { return (a.w[0] | a.w[1] | a.w[2] | a.w[3]) == 0; }
static inline int Ufits(U a) { return (a.w[2] | a.w[3]) == 0; }
static inline u128 Uto(U a) { CHECK(Ufits(a), "U wider than 128 bits"); return ((u128)a.w[1] << 64) | a.w[0]; }
static inline i128 UtoI(U a) {
    u128 x = Uto(a);
    CHECK(x >> 127 == 0, "U wider than a signed 128");
    return (i128)x;
}
static inline int Ucmp(U a, U b) {
    for (int i = 3; i >= 0; i--)
        if (a.w[i] != b.w[i]) return a.w[i] < b.w[i] ? -1 : 1;
    return 0;
}
static inline int Ult(U a, U b) { return Ucmp(a, b) < 0; }
static inline int Ule(U a, U b) { return Ucmp(a, b) <= 0; }
static inline U Uadd(U a, U b) {
    U r;
    u128 c = 0;
    for (int i = 0; i < 4; i++) {
        c += (u128)a.w[i] + b.w[i];
        r.w[i] = (u64)c;
        c >>= 64;
    }
    CHECK(c == 0, "U add overflow");
    return r;
}
static inline U Usub(U a, U b) {
    U r;
    u64 br = 0;
    for (int i = 0; i < 4; i++) {
        u128 t = (u128)a.w[i] - b.w[i] - br;
        r.w[i] = (u64)t;
        br = (u64)(t >> 127);
    }
    CHECK(br == 0, "U sub underflow");
    return r;
}
static inline U Ust(U a, U b) { return Ucmp(a, b) > 0 ? Usub(a, b) : U0(); }   /* `sub`/`tsub` */
static inline U Umax(U a, U b) { return Ucmp(b, a) > 0 ? b : a; }
static inline U Umin(U a, U b) { return Ucmp(b, a) < 0 ? b : a; }
static inline U Umul(U a, U b) {
    if (!(a.w[2] | a.w[3] | b.w[2] | b.w[3])) {
        /* both below 2^128: the four products */
        u128 p00 = (u128)a.w[0] * b.w[0], p01 = (u128)a.w[0] * b.w[1], p10 = (u128)a.w[1] * b.w[0],
             p11 = (u128)a.w[1] * b.w[1];
        u128 mid = (p00 >> 64) + (u64)p01 + (u64)p10;
        U o;
        o.w[0] = (u64)p00;
        o.w[1] = (u64)mid;
        u128 hi = (mid >> 64) + (p01 >> 64) + (p10 >> 64) + p11;
        o.w[2] = (u64)hi;
        o.w[3] = (u64)(hi >> 64);
        return o;
    }
    u64 r[8] = {0, 0, 0, 0, 0, 0, 0, 0};
    for (int i = 0; i < 4; i++) {
        if (!a.w[i]) continue;
        u128 c = 0;
        for (int j = 0; j < 4; j++) {
            c += (u128)a.w[i] * b.w[j] + r[i + j];
            r[i + j] = (u64)c;
            c >>= 64;
        }
        for (int k = i + 4; c && k < 8; k++) {
            c += r[k];
            r[k] = (u64)c;
            c >>= 64;
        }
    }
    CHECK((r[4] | r[5] | r[6] | r[7]) == 0, "U mul overflow");
    U o = {{r[0], r[1], r[2], r[3]}};
    return o;
}
static inline U Umul2(u128 a, u128 b) { return Umul(Uu(a), Uu(b)); }
static inline U Ushr(U a, int n) {
    if (n <= 0) return a;
    if (n >= 256) return U0();
    U r = U0();
    int q = n / 64, s = n % 64;
    for (int i = 0; i + q < 4; i++) {
        u64 lo = a.w[i + q] >> s;
        u64 hi = (s && i + q + 1 < 4) ? a.w[i + q + 1] << (64 - s) : 0;
        r.w[i] = lo | hi;
    }
    return r;
}
static inline int Ubits(U a) {
    for (int i = 3; i >= 0; i--)
        if (a.w[i]) return 64 * i + 64 - __builtin_clzll(a.w[i]);
    return 0;
}
static inline U Ushl(U a, int n) {
    if (n <= 0) return a;
    CHECK(Ubits(a) + n <= 256, "U shl overflow");
    U r = U0();
    int q = n / 64, s = n % 64;
    for (int i = 3; i >= q; i--) {
        u64 hi = a.w[i - q] << s;
        u64 lo = (s && i - q - 1 >= 0) ? a.w[i - q - 1] >> (64 - s) : 0;
        r.w[i] = hi | lo;
    }
    return r;
}
static inline int Ubit(U a, int i) { return (int)((a.w[i / 64] >> (i % 64)) & 1); }
static inline void Usetbit(U *a, int i) { a->w[i / 64] |= (u64)1 << (i % 64); }
/* a // d and a % d */
static U Udiv(U a, U d, U *rem) {
    CHECK(!Uz(d), "U division by zero");
    if (Ucmp(a, d) < 0) {
        if (rem) *rem = a;
        return U0();
    }
    if (Ufits(a)) {
        u128 x = ((u128)a.w[1] << 64) | a.w[0], y = ((u128)d.w[1] << 64) | d.w[0];
        if (!(x >> 64)) {
            u64 xx = (u64)x, yy = (u64)y;
            if (rem) *rem = Uu(xx % yy);
            return Uu(xx / yy);
        }
#if defined(__x86_64__)
        if (!(y >> 64)) {
            /* 128 bits by 64: the high word's quotient, then `divq` on the remainder and the low word */
            u64 dd = (u64)y, hi = (u64)(x >> 64), lo = (u64)x;
            u64 qhi = hi / dd, r = hi % dd, qlo, r2;
            __asm__("divq %4" : "=a"(qlo), "=d"(r2) : "a"(lo), "d"(r), "rm"(dd));
            if (rem) *rem = Uu(r2);
            return Uu(((u128)qhi << 64) | qlo);
        }
#endif
        if (rem) *rem = Uu(x % y);
        return Uu(x / y);
    }
    int sh = Ubits(a) - Ubits(d);
    U dd = Ushl(d, sh), q = U0(), r = a;
    for (int i = sh; i >= 0; i--) {
        if (Ucmp(r, dd) >= 0) {
            r = Usub(r, dd);
            Usetbit(&q, i);
        }
        dd = Ushr(dd, 1);
    }
    if (rem) *rem = r;
    return q;
}
static inline U Ucdiv(U a, U d) {           /* (a + d - 1) // d */
    U r, q = Udiv(a, d, &r);
    return Uz(r) ? q : Uadd(q, Uu(1));
}
static inline U Ufdiv(U a, U d) { return Udiv(a, d, NULL); }

/* ---------------------------------------------------------------------------------------------------------------
   BN: an unsigned integer of up to 32 limbs, for the products of the cells' factors (`dropCost`): multiplied by
   128-bit factors and divided by a power of 2^64. */
#define BNL 32
typedef struct { int n; u64 w[BNL]; } BN;

static inline void bn_set(BN *a, u128 x) {
    a->w[0] = (u64)x;
    a->w[1] = (u64)(x >> 64);
    a->n = a->w[1] ? 2 : (a->w[0] ? 1 : 0);
}
static inline void bn_mul(BN *a, u128 x) {
    if (a->n == 0) return;
    if (x == 0) {
        a->n = 0;
        return;
    }
    u64 x0 = (u64)x, x1 = (u64)(x >> 64);
    u64 r[BNL + 2];
    memset(r, 0, sizeof(u64) * (a->n + 2));
    u128 c = 0;
    for (int i = 0; i < a->n; i++) {
        c += (u128)a->w[i] * x0 + r[i];
        r[i] = (u64)c;
        c >>= 64;
    }
    r[a->n] = (u64)c;
    if (x1) {
        c = 0;
        for (int i = 0; i < a->n; i++) {
            c += (u128)a->w[i] * x1 + r[i + 1];
            r[i + 1] = (u64)c;
            c >>= 64;
        }
        r[a->n + 1] = (u64)c;
    }
    int n = a->n + 2;
    while (n > 0 && r[n - 1] == 0) n--;
    CHECK(n <= BNL, "BN overflow");
    memcpy(a->w, r, sizeof(u64) * n);
    a->n = n;
}
/* ⌈a / 2^(64m)⌉ as U */
static inline U bn_cshr(const BN *a, int m) {
    int nz = 0;
    for (int i = 0; i < m && i < a->n; i++)
        if (a->w[i]) nz = 1;
    U r = U0();
    for (int i = m; i < a->n; i++) {
        CHECK(i - m < 4, "BN quotient wider than 256 bits");
        r.w[i - m] = a->w[i];
    }
    return nz ? Uadd(r, Uu(1)) : r;
}

/* ---------------------------------------------------------------------------------------------------------------
   Python's mixed arithmetic. */
static inline int clz128(u128 x) {
    u64 hi = (u64)(x >> 64);
    return hi ? __builtin_clzll(hi) : 64 + __builtin_clzll((u64)x);
}
/* float(x): rounded to nearest, ties to even */
static double u128_to_double(u128 m) {
    if (m < ((u128)1 << 53)) return (double)(u64)m;
    int nb = 128 - clz128(m), sh = nb - 53;
    u128 top = m >> sh, rem = m & (((u128)1 << sh) - 1), half = (u128)1 << (sh - 1);
    if (rem > half || (rem == half && (top & 1))) top++;
    return ldexp((double)(u64)top, sh);
}
static double i128_to_double(i128 x) {
    if (x < 0) return -u128_to_double((u128)0 - (u128)x);
    return u128_to_double((u128)x);
}
static double U_to_double(U a) {
    int nb = Ubits(a);
    if (nb <= 128) return u128_to_double(Uto(a));
    int sh = nb - 53;
    U top = Ushr(a, sh);
    u64 t = (u64)Uto(top);
    /* the bits below: above, below or at the half */
    int cmp = 0;
    if (Ubit(a, sh - 1)) {
        cmp = 0;
        for (int i = 0; i < sh - 1 && !cmp; i++)
            if (Ubit(a, i)) cmp = 1;
        if (cmp || (t & 1)) t++;
    }
    return ldexp((double)t, sh);
}
/* x / 2^64 as Python's true division of integers (correctly rounded) */
static inline double U_div_S(U a) { return ldexp(U_to_double(a), -64); }
/* the sign of x - d, exactly (d finite) */
static int cmp_i128_double(i128 x, double d) {
    CHECK(isfinite(d), "comparison with a non-finite float");
    double fl = floor(d);
    if (fl >= 1.6e38) return -1;
    if (fl <= -1.6e38) return 1;
    i128 f = (i128)fl;
    if (x < f) return -1;
    if (x > f) return 1;
    return d > fl ? -1 : 0;
}
/* Python's `int + float`: the integer rounded to a float, then added */
static inline double addIF(i128 x, double d) { return i128_to_double(x) + d; }
