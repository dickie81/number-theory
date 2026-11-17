/* hint_plan: the planner of tools/linnik/hint_cert.py (its `row_job`'s search: `Planner.plan`, the hints of its
   lazy leaves, and the cell planned again where one has none) in C. Each function is the Python method of the same
   name, in the same order of operations, so that the plan, its cost and the search's counts are the Python
   planner's (`Planner.rescap = 0`, the memo never emptied): the integers are exact (an overflow stops the program)
   and the floats are evaluated as Python evaluates them, a sum from the left as PyPy's `sum` does it.

       hint_plan PARAMS [cut] < CELLS > PLANS
       hint_plan PARAMS gen < COMMANDS > PARTS

   PARAMS is written by tools/linnik/cplan.py (the certificate's parameters and the constants of the tests, read
   from the Python modules); CELLS has a line `a b` for each cell of the first prime; for each, PLANS has the plan's
   cost, the search's counts and the plan's nodes in prefix order (see `emit`), or with `cut`, for a heavy cell, the
   counts of its plan's steps and its cut into parts by the generator (gen.h). With `gen`, the generator runs the
   commands of `genMain` (the parts of light cells, the cut of a plan given, the transcoding of a part's hints).
   With CPLAN_DEBUG set, the memo's size and a line every 2^20 boxes on stderr; with CPLAN_MAXCALLS=N the program
   stops after N boxes (to profile).

   Two things differ from the Python planner in how, not in what. The memo of the window's tests keeps only the
   entries that can change an answer (`resHint`): a key of the test at the two corners that fails the loose filter
   is kept as None only where the strict filter passes, since elsewhere a missing key and None answer every later
   visit alike; and the float filters' answers are cached by key, the cache emptied when it is full. Both are pure,
   so the plan is the same with less memory: a cell near x^0.3 at 2100/1000, 11.4·10^6 boxes, in 0.6 GB. */
#include "num.h"
#include "res.h"

#define MAXB 16

typedef struct { i64 lo, hi; } Cell;
typedef struct { int kind; u32 s0, sr, s1; int e; } Cfg;
typedef struct { int ok; i64 f; Cfg cfg; } FC;               /* `(f, cfg)` or None */

static i64 DEN;
static i128 KC, BIG, CAPK;

enum { KV, KE, KD, KR, KB, KF, KP, KS, NKIND };
static const char KCH[NKIND] = {'V', 'E', 'D', 'R', 'B', 'F', 'P', 'S'};

static struct {
    i64 Ln, Ld;
    i64 hI, hF, hR, hQ, wmin, kappa;
    int depth, depthR, depthF, maxlen, fuel;
    int pos, skip, skipmin, energy, res, resF, cof, lv, lazy, rmerge, split, ycorner, exh, split2, blk, blkF, hl;
    int redo, merge;
    double lamK;
    i64 dm0, dm1;
    double SEC[NKIND][2];
    int SECp[NKIND][2];
    int nlx;
    i64 LX[32][12];
    i128 TOPK, W1K, LD, LNT[17];
} G;

static i128 restLo, restHi, uC0, uA, uB, uC, vA, vB, vC, umC0, umA, D1max, T5, T6, T5E, u3, fmax3, fillLo;

/* ---------------------------------------------------------------------------------------------------------------
   mirror8.py */
static inline i128 cdivM(i128 a, i128 b) { return b ? cdivI(a, b) : 0; }

static i128 omF(i128 P, i128 Q) {
    CHECK(Q > 0 && P >= 2 * Q, "omF: v outside [2, 3]");
    i128 k = 16 * (P - 2 * Q) / Q;
    CHECK(0 <= k && k <= 16, "omF: k");
    i128 A = 16 * (P - Q), B = (16 + k) * Q;
    i128 inner = 2 * A * B * (G.LD + G.LNT[k]) + (A * A - B * B) * G.LD;
    CHECK(inner >= 0, "omF: a negative numerator");
    U num = Umul(Umul2((u128)(KC * Q), 1), Uu((u128)inner));
    U den = Umul(Uu((u128)(2 * A * B * G.LD)), Uu((u128)P));
    return UtoI(Ucdiv(num, den));
}
static i128 invKw(i128 s, i128 t, i128 W, i128 w) {
    if (DEN <= s + 2 * t + W + w) return KC;
    return cdivM(KC * (t + w), DEN - s - t - W);
}
static i128 omKw(i128 s, i128 t, i128 W, i128 w) {
    if (DEN < s + 2 * t) return 0;
    if (s + 4 * t + W + 3 * w <= DEN) return G.TOPK;
    if (DEN < s + 3 * t) return invKw(s, t, W, w);
    i128 p1 = (s + 3 * t + W + 2 * w <= DEN) ? 0 : invKw(s, t, W, w);
    i128 p2;
    if (100 * (DEN + 1 - s - t) <= 276 * t)
        p2 = omF(DEN + 1 - s - t, t);
    else if (277 * (t + w) <= 100 * tsubI(tsubI(tsubI(DEN, s), t), W))
        p2 = omF(DEN - s - t - W, t + w);
    else
        p2 = G.W1K;
    i128 p3 = (s + 4 * t <= DEN) ? G.TOPK : 0;
    return maxI(maxI(p1, p2), p3);
}

/* ---------------------------------------------------------------------------------------------------------------
   tree_cert.py: the box's sums, the costs of a dropped box */
static inline i64 loSum(const Cell *b, int n) {
    i64 s = 0;
    for (int i = 0; i < n; i++) s += b[i].lo;
    return s;
}
static inline i64 hiSum(const Cell *b, int n) {
    i64 s = 0;
    for (int i = 0; i < n; i++) s += b[i].hi;
    return s;
}
static inline i64 mSum(int j, const Cell *b, int n, u32 m) {
    i64 s = 0;
    for (int i = 0; i < n && i < 32; i++)
        if (m >> i & 1) s += j ? b[i].hi : b[i].lo;
    return s;
}
static inline i64 lomin(const Cell *b, int n) {      /* min([DEN] + [c[0] for c in bl]) */
    i64 m = DEN;
    for (int i = 0; i < n; i++) m = min64(m, b[i].lo);
    return m;
}

static u128 trF(i64 a, i64 w) {
    CHECK(a >= 0 && w >= 0, "trF of a negative");
    U num = Ushl(Umul(Uu((u128)w), Uu((u128)(2 * a + w))), 64);
    U den = Umul(Uu((u128)(2 * a)), Uu((u128)(a + w)));
    if (Uz(den)) return 0;
    return Uto(Ucdiv(num, den));
}
static u128 exF(i64 a, i64 w) {
    CHECK(a >= 0 && w >= 0, "exF of a negative");
    U num = Ushl(Umul(Uu((u128)DEN), Uu((u128)w)), 64);
    U den = Umul(Uu((u128)a), Uu((u128)(a + w)));
    if (Uz(den)) return 0;
    return Uto(Ucdiv(num, den));
}

static int cellsOK(const Cell *b, int n) {
    for (int i = 0; i < n; i++)
        if (!(0 < b[i].lo && b[i].lo < b[i].hi)) return 0;
    return 1;
}
static int vanishOK(const Cell *bl, int n) {
    if (n == 0) return 0;
    Cell c = bl[0];
    return c.hi + hiSum(bl + 1, n - 1) + 1 <= DEN && DEN + 1 <= c.lo + loSum(bl + 1, n - 1) + c.lo;
}
static int dropOK(const Cell *bl, int n) { return n > 0 && cellsOK(bl, n) && hiSum(bl, n) <= DEN; }

static i128 dropCost(const Cell *bl, int n) {
    if (n == 0) return 0;
    Cell c = bl[0];
    const Cell *b = bl + 1;
    int nb = n - 1;
    BN t;
    bn_set(&t, 1);
    for (int i = 0; i < nb; i++) bn_mul(&t, trF(b[i].lo, b[i].hi - b[i].lo));
    bn_mul(&t, exF(c.lo, c.hi - c.lo));
    i128 om = omKw(loSum(b, nb), c.lo, tsub(c.hi + hiSum(b, nb), c.lo + loSum(b, nb)), c.hi - c.lo);
    bn_mul(&t, (u128)om);
    return UtoI(bn_cshr(&t, nb + 1));
}
static int dropBOK(const Cell *bl, int n) {
    return n >= 2 && cellsOK(bl, n) && DEN + 1 <= loSum(bl, n) + bl[0].lo && hiSum(bl + 1, n - 1) < DEN;
}
static i128 dropBCost(const Cell *bl, int n) {
    const Cell *b = bl + 1;
    int nb = n - 1;
    BN t;
    bn_set(&t, (u128)KC * (u128)DEN);
    for (int i = 0; i < nb; i++) bn_mul(&t, trF(b[i].lo, b[i].hi - b[i].lo));
    /* ⌈X / (Y·2^(64 nb))⌉ = ⌈⌈X / 2^(64 nb)⌉ / Y⌉ */
    U x = bn_cshr(&t, nb);
    return UtoI(Ucdiv(x, Uu((u128)(DEN - hiSum(b, nb)))));
}
/* `dropC`: the cost, or -1 for None */
static i128 dropC(const Cell *bl, int n, int par) {
    if (par) {
        if (dropOK(bl, n)) return dropCost(bl, n);
        if (dropBOK(bl, n)) return dropBCost(bl, n);
    }
    return -1;
}

/* rev_cert.py */
static int vanishK(Cell ctx, const Cell *ch, int n) {
    if (n == 0) return 0;
    Cell c = ch[0];
    return c.hi + hiSum(ch + 1, n - 1) + 1 <= ctx.lo && ctx.hi + 1 <= c.lo + loSum(ch + 1, n - 1) + c.lo;
}
static i128 dropK(Cell ctx, const Cell *ch, int n, int par) {
    if (n == 0) return -1;
    Cell c = ch[0];
    const Cell *b = ch + 1;
    int nb = n - 1;
    if (par && cellsOK(ch, n) && c.hi + hiSum(b, nb) + 1 <= ctx.lo) {
        BN t;
        bn_set(&t, 1);
        for (int i = 0; i < nb; i++) bn_mul(&t, trF(b[i].lo, tsub(b[i].hi, b[i].lo)));
        bn_mul(&t, exF(c.lo, tsub(c.hi, c.lo)));
        i128 om = omKw(loSum(b, nb) + tsub(DEN, ctx.hi), c.lo,
                       tsub(c.hi + hiSum(b, nb), c.lo + loSum(b, nb)) + (tsub(ctx.hi, ctx.lo) + 1), tsub(c.hi, c.lo));
        bn_mul(&t, (u128)om);
        return UtoI(bn_cshr(&t, nb + 1));
    }
    return -1;
}
static i128 bdK(Cell ctx, i64 y) {
    i128 om = omKw(tsub(tsub(tsub(DEN, ctx.hi), y), 1), y, tsub(ctx.hi, ctx.lo) + 2, 1);
    return cdivM(om * DEN, y);
}

/* ---------------------------------------------------------------------------------------------------------------
   The tests (tree_cert.Tests, fill_cert.TestsF) */
static inline i128 uOf(i128 r1) {
    i128 Ln = G.Ln, Ld = G.Ld;
    return maxI(cdivM(2 * Ld * DEN, 3 * Ln), cdivM(tsubI(62505 * Ld * DEN + 27637 * Ln, 27637 * Ln * r1), 62500 * Ln));
}
static inline i128 vOf(i128 r2) {
    i128 Ln = G.Ln, Ld = G.Ld;
    return minI(tsubI(tsubI(3 * Ln * DEN, 2 * Ld * DEN) / (3 * Ln), r2 + 1),
                tsubI(tsubI(62500 * Ln * DEN, 62505 * Ld * DEN), 34863 * Ln * (r2 + 1)) / (62500 * Ln));
}
static inline int zone(i128 r1, i128 r2, i128 u, i128 v) {
    i128 Ln = G.Ln, Ld = G.Ld;
    return Ld * DEN + 2000 * Ln <= 2000 * Ln * r1 && 2 * Ld * DEN <= 3 * Ln * u &&
           2 * Ld * DEN + 3 * Ln * (r2 + 1 + v) <= 3 * Ln * DEN &&
           62505 * Ld * DEN + 27637 * Ln <= 62500 * Ln * u + 27637 * Ln * r1 &&
           62505 * Ld * DEN + 62500 * Ln * v + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN &&
           125005 * Ld * DEN + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN;
}
/* the leaves' tests (`Tests.leaves`, `pStar`, `thetaL`, `leavesE`). With PS1 = ⌊(Ln·DEN − Ld·DEN − 1)/Ln⌋,
   PS2 = ⌊(2Ln·DEN − Ld·DEN − 1)/(2Ln)⌋ and PS3 = ⌊(2Ln·DEN − 2Ld·DEN − 1)/Ln⌋, the three inequalities of `leaves` on
   sizes D1, D2 ≥ 0 are D1 ≤ PS1, D1 + D2 ≤ PS2 and D1 + 2·D2 ≤ PS3; `pStar D2` is the largest D1 with them (PS1,
   PS2 − D2, PS3 − 2·D2), and `thetaL D1` the largest D2 with the last two. So in `leavesE`, once P = pStar D2 and
   th = thetaL D1 are at least 1, `leaves P D2` holds and `leaves D1 th` is D1 ≤ PS1 */
static i64 PS1, PS2, PS3, TH0;
static int LXn[32][2], LXj[32][2][6];
static i64 LXc[32][2][6];
static void leavesInit(void) {
    i64 Ln = G.Ln, Ld = G.Ld;
    PS1 = (Ln * DEN - Ld * DEN - 1) / Ln;
    PS2 = (2 * Ln * DEN - Ld * DEN - 1) / (2 * Ln);
    PS3 = (2 * Ln * DEN - 2 * Ld * DEN - 1) / Ln;
    TH0 = 2 * Ln * DEN - 2 * Ld * DEN - 1;
    CHECK(PS1 > 0 && PS2 > 0 && PS3 > 0 && TH0 > 0, "the leaves' constants");
    for (int i = 0; i < G.nlx; i++)
        for (int side = 0; side < 2; side++) {
            LXn[i][side] = 0;
            for (int j = 0; j < 6; j++)
                if (G.LX[i][6 * side + j]) {
                    LXj[i][side][LXn[i][side]] = j;
                    LXc[i][side][LXn[i][side]++] = G.LX[i][6 * side + j];
                }
        }
}
static inline __attribute__((always_inline)) int leavesT(i128 D1, i128 D2) {
    CHECK(D1 >= 0 && D2 >= 0, "a leaf of negative size");
    return D1 <= PS1 && D1 + D2 <= PS2 && D1 + 2 * D2 <= PS3;
}
static inline i128 pStar(i128 D2) { return minI(minI(PS1, tsubI(PS2, D2)), tsubI(PS3, 2 * D2)); }
static inline i128 thetaL(i128 D1) { return minI(tsubI(PS2, D1), tsubI(TH0, G.Ln * D1) / (2 * G.Ln)); }
static inline int leafXR(i128 D, i128 P1, i128 P2, i128 R1, i128 R2) {
    i128 Ln = G.Ln, Ld = G.Ld;
    i128 at[6] = {Ln * P1, Ln * P2, Ln * R1, Ln * R2, Ld * D, Ln * D};
    for (int i = 0; i < G.nlx; i++) {
        i128 l = 0, r = 0;
        for (int q = 0; q < LXn[i][0]; q++) l += (i128)LXc[i][0][q] * at[LXj[i][0][q]];
        for (int q = 0; q < LXn[i][1]; q++) r += (i128)LXc[i][1][q] * at[LXj[i][1][q]];
        if (!(l <= r)) return 0;
    }
    return 1;
}
static inline __attribute__((always_inline)) int leavesE(i128 D1, i128 D2) {
    if (!(D1 + D2 < DEN)) return 0;
    if (!(D1 <= PS1)) return 0;
    i128 P = pStar(D2);
    if (!(1 <= P)) return 0;
    i128 th = thetaL(D1);
    if (!(1 <= th)) return 0;
    return leafXR(DEN, P - 1, D1 + 1, th - 1, D2 + 1);
}
static int cellsIn(i64 f, const Cell *bl, int n) {       /* all(f <= c[0] <= c[1] <= DEN) */
    for (int i = 0; i < n; i++)
        if (!(f <= bl[i].lo && bl[i].lo <= bl[i].hi && bl[i].hi <= DEN)) return 0;
    return 1;
}
static int chkJ2(const Cell *bl, int n, i64 f, u32 s0, u32 sr, u32 s1, int e, i128 u, i128 v, i128 t) {
    i128 r1 = mSum(0, bl, n, sr), r2 = mSum(1, bl, n, sr);
    i128 h1 = mSum(1, bl, n, s1), hs = hiSum(bl, n);
    i128 D1 = h1 + (e ? t : 0), D2 = tsubI(hs, h1) + (e ? 0 : t);
    return 0 < f && n <= 13 && cellsIn(f, bl, n) && (s0 & sr) == 0 && zone(r1, r2, u, v) && u + f < v &&
           u <= t + mSum(0, bl, n, s0) && mSum(1, bl, n, s0) < v && (leavesT(D1, D2) || (G.energy && leavesE(D1, D2)));
}
static int okJ2(const Cell *bl, int n, i64 f, const Cfg *c) {
    i128 u = uOf(mSum(0, bl, n, c->sr)), v = vOf(mSum(1, bl, n, c->sr));
    return chkJ2(bl, n, f, c->s0, c->sr, c->s1, c->e, u, v, tsubI(u, mSum(0, bl, n, c->s0)));
}
static int chkI2(const Cell *bl, int n, u32 s0, u32 sr) {
    i128 Ln = G.Ln, Ld = G.Ld;
    i128 r1 = mSum(0, bl, n, sr), r2 = mSum(1, bl, n, sr), u = mSum(0, bl, n, s0), v = mSum(1, bl, n, s0);
    if (!(n <= 13)) return 0;
    for (int i = 0; i < n; i++)
        if (!(1 <= bl[i].lo && bl[i].lo <= bl[i].hi && bl[i].hi <= DEN)) return 0;
    return (s0 & sr) == 0 && Ld * DEN + 2000 * Ln <= 2000 * Ln * r1 && 2 * Ld * DEN + 3 * Ln <= 3 * Ln * u &&
           2 * Ld * DEN + 3 * Ln * (r2 + 1 + v) <= 3 * Ln * DEN &&
           62505 * Ld * DEN + 90137 * Ln <= 62500 * Ln * u + 27637 * Ln * r1 &&
           62505 * Ld * DEN + 62500 * Ln * v + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN &&
           125005 * Ld * DEN + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN;
}
static int chkJ3(const Cell *bl, int n, i64 f, u32 s0, u32 s1, int e, i128 u, i128 v, i128 t, i128 r1, i128 r2) {
    i128 D1 = mSum(1, bl, n, s1) + (e ? t + r2 : 0);
    i128 D2 = tsubI(hiSum(bl, n), mSum(1, bl, n, s1)) + (e ? 0 : t + r2);
    return 0 < f && n <= 13 && cellsIn(f, bl, n) && zone(r1, r2, u, v) && r1 + f < r2 && u + f < v &&
           u <= t + mSum(0, bl, n, s0) && mSum(1, bl, n, s0) < v && (leavesT(D1, D2) || (G.energy && leavesE(D1, D2)));
}
static int okJ3(const Cell *bl, int n, i64 f, const Cfg *c) {
    i128 r1 = fillLo, r2 = fillLo + f + 1;
    i128 u = uOf(r1), v = vOf(r2);
    return chkJ3(bl, n, f, c->s0, c->s1, c->e, u, v, tsubI(u, mSum(0, bl, n, c->s0)), r1, r2);
}
static inline int okI_T(const Cell *bl, int n, const Cfg *c) { return chkI2(bl, n, c->s0, c->sr); }
static inline int okJ_T(const Cell *bl, int n, i64 f, const Cfg *c) {
    return c->kind == 2 ? okJ3(bl, n, f, c) : okJ2(bl, n, f, c);
}

/* ---------------------------------------------------------------------------------------------------------------
   The search over the sets of a box's cells (tree_cert.Search) */
static inline int restOK(i64 lo, i64 hi) { return restLo <= lo && hi <= restHi; }
static inline i128 uOfF(i128 r1) { return maxI(uC0, tsubI(tsubI(uA, uB * r1) + uC, 1) / uC); }
static inline i128 vOfF(i128 r2) { return minI(tsubI(vA, r2 + 1), tsubI(vB, vC * (r2 + 1)) / uC); }
static inline i128 uminOf(i128 r1) { return maxI(umC0, tsubI(tsubI(umA, uB * r1) + uC, 1) / uC); }

/* None is -1 */
static i64 findSub2(i128 umin, i128 vmax, u32 skip, const Cell *cs, int n, u32 bit, i64 slo, i64 shi, u32 mask,
                    i64 rem) {
    if (vmax < shi) return -1;
    if (umin <= slo) return mask;
    if (n == 0 || slo + rem < umin) return -1;
    Cell c = cs[0];
    if (bit == skip) return findSub2(umin, vmax, skip, cs + 1, n - 1, 2 * bit, slo, shi, mask, rem);
    i64 m = findSub2(umin, vmax, skip, cs + 1, n - 1, 2 * bit, slo + c.lo, shi + c.hi, mask + bit, tsub(rem, c.lo));
    if (m >= 0) return m;
    return findSub2(umin, vmax, skip, cs + 1, n - 1, 2 * bit, slo, shi, mask, tsub(rem, c.lo));
}
typedef struct { i64 slo; u32 mask; } SM;
static SM bestSub(i128 v, u32 skip, const Cell *cs, int n, u32 bit, i64 slo, i64 shi, u32 mask, i64 rem, SM best) {
    if (slo + rem <= best.slo) return best;
    if (n == 0) {
        SM r = {slo, mask};
        return r;
    }
    Cell c = cs[0];
    if (bit == skip) return bestSub(v, skip, cs + 1, n - 1, 2 * bit, slo, shi, mask, rem, best);
    if (shi + c.hi < v)
        best = bestSub(v, skip, cs + 1, n - 1, 2 * bit, slo + c.lo, shi + c.hi, mask + bit, tsub(rem, c.lo), best);
    return bestSub(v, skip, cs + 1, n - 1, 2 * bit, slo, shi, mask, tsub(rem, c.lo), best);
}
static i64 findSub1(i128 lo, i128 hi, const Cell *cs, int n, u32 bit, i64 s, u32 mask, i64 rem) {
    if (hi < s || s + rem < lo) return -1;
    if (n == 0) return mask;
    Cell c = cs[0];
    i64 m = findSub1(lo, hi, cs + 1, n - 1, 2 * bit, s + c.hi, mask + bit, tsub(rem, c.hi));
    if (m >= 0) return m;
    return findSub1(lo, hi, cs + 1, n - 1, 2 * bit, s, mask, tsub(rem, c.hi));
}
static void subsE(const Cell *cs, int n, i128 lo, i128 hi, i64 rem, u32 bit, i64 s, u32 mask, u32 *out, int *no,
                  int cap) {
    if (*no >= cap || hi < s || s + rem < lo) return;
    if (n == 0) {
        out[(*no)++] = mask;
        return;
    }
    Cell c = cs[0];
    subsE(cs + 1, n - 1, lo, hi, tsub(rem, c.hi), 2 * bit, s + c.hi, mask + bit, out, no, cap);
    subsE(cs + 1, n - 1, lo, hi, tsub(rem, c.hi), 2 * bit, s, mask, out, no, cap);
}

typedef struct { int ok; u32 m; int e; } SP;
static SP leavesOf(const Cell *bl, int n, i64 hs, i128 t) {
    SP r = {0, 0, 0};
    if (T5 < hs + t) return r;
    i128 lo = tsubI(2 * (hs + t), T6);
    i64 m = -1;
    if (t <= D1max) m = findSub1(tsubI(lo, t), tsubI(D1max, t), bl, n, 1, 0, 0, hs);
    if (m >= 0) {
        r.ok = 1, r.m = (u32)m, r.e = 1;
        return r;
    }
    m = findSub1(lo, D1max, bl, n, 1, 0, 0, hs);
    if (m >= 0) r.ok = 1, r.m = (u32)m, r.e = 0;
    return r;
}
static SP leavesOfE(const Cell *bl, int n, i64 hs, i128 t) {
    SP r = {0, 0, 0};
    if (T5E < hs + t) return r;
    i128 Ln = G.Ln, Ld = G.Ld;
    i128 p_lo = 85 * Ld * DEN / (100 * Ln), p_hi = cdivM(125 * Ld * DEN, 100 * Ln);
    for (int ei = 0; ei < 2; ei++) {
        int e = ei == 0;
        i128 tt = e ? t : 0;
        u32 ms[24];
        int nm = 0;
        subsE(bl, n, tsubI(p_lo, tt), tsubI(p_hi, tt), hs, 1, 0, 0, ms, &nm, 24);
        for (int i = 0; i < nm; i++) {
            i64 h1 = mSum(1, bl, n, ms[i]);
            if (leavesE(h1 + tt, hs - h1 + (t - tt))) {
                r.ok = 1, r.m = ms[i], r.e = e;
                return r;
            }
        }
    }
    return r;
}
static inline i128 t5J(void) { return G.energy ? maxI(T5, T5E) : T5; }
static SP leavesOfJ2(const Cell *bl, int n, i64 hs, i128 t) {
    SP sp = leavesOf(bl, n, hs, t);
    if (!sp.ok && G.energy) sp = leavesOfE(bl, n, hs, t);
    return sp;
}
/* `propI2`: at most one configuration */
static int propI2(const Cell *bl, int n, i64 ls, Cfg *out) {
    u32 bit = 1;
    for (int i = 0; i < n; i++) {
        Cell c = bl[i];
        if (restOK(c.lo, c.hi)) {
            i64 m = findSub2(uminOf(c.lo), vOfF(c.hi), bit, bl, n, 1, 0, 0, 0, tsub(ls, c.lo));
            if (m >= 0) {
                Cfg r = {1, (u32)m, bit, 0, 0};
                *out = r;
                return 1;
            }
        }
        bit *= 2;
    }
    return 0;
}
static FC propJ2(const Cell *bl, int n, i64 lmin, i64 ls, i64 hs) {
    FC acc = {0, 0, {0, 0, 0, 0, 0}};       /* (0, None) */
    u32 bit = 1;
    for (int i = 0; i < n; i++) {
        Cell c = bl[i];
        if (lmin <= acc.f) return acc;
        if (restOK(c.lo, c.hi)) {
            i128 u = uOfF(c.lo), v = vOfF(c.hi);
            i128 f = minI(lmin, tsubI(v, u + 1));
            if (acc.f < f && hs + tsubI(u, tsub(ls, c.lo)) <= t5J()) {
                SM z = {0, 0};
                SM b = bestSub(v, bit, bl, n, 1, 0, 0, 0, tsub(ls, c.lo), z);
                SP sp = leavesOfJ2(bl, n, hs, tsubI(u, b.slo));
                if (sp.ok) {
                    acc.ok = 1;
                    acc.f = (i64)f;
                    Cfg cf = {1, b.mask, bit, sp.m, sp.e};
                    acc.cfg = cf;
                }
            }
        }
        bit *= 2;
    }
    return acc;
}
static FC tryJ3(const Cell *bl, int n, i64 ls, i64 hs, i64 f) {
    FC r = {0, 0, {0, 0, 0, 0, 0}};
    i128 r2 = restLo + f + 1;
    SM z = {0, 0};
    SM b = bestSub(vOfF(r2), 0, bl, n, 1, 0, 0, 0, ls, z);
    SP sp = leavesOfJ2(bl, n, hs, tsubI(u3, b.slo) + r2);
    if (sp.ok) {
        r.ok = 1;
        r.f = f;
        Cfg cf = {2, b.mask, 0, sp.m, sp.e};
        r.cfg = cf;
    }
    return r;
}
static FC propJ3(const Cell *bl, int n, i64 ls, i64 hs, int cnt, i64 f) {
    for (int i = 0; i < cnt; i++) {
        FC r = tryJ3(bl, n, ls, hs, f);
        if (r.ok) return r;
        f = 3 * f / 4;
    }
    FC r = {0, 0, {0, 0, 0, 0, 0}};
    return r;
}
/* `propJFl` (and FillSearch.propJ with lomin from the box): at most two proposals, in order */
static int propJF(const Cell *bl, int n, i64 lmin, FC *out) {
    i64 ls = loSum(bl, n), hs = hiSum(bl, n);
    if (t5J() < hs) return 0;
    FC r = propJ2(bl, n, lmin, ls, hs);
    int no = 0;
    if (r.f < lmin) {
        FC r3 = propJ3(bl, n, ls, hs, 8, (i64)minI(lmin, fmax3));
        if (r3.ok && r.f < r3.f) out[no++] = r3;
    }
    if (r.ok) out[no++] = r;
    return no;
}

/* ---------------------------------------------------------------------------------------------------------------
   The trees over the frozen parts (flip_cert.FlipSearch): `frz` and `fctx` */
static struct {
    int on;
    i64 e1, e2, Kb;
    Cell beta[MAXB];
    int nb;
    Cell ctx;
} FZ;

static i64 flipT(Cell ctx) { return (ctx.hi + 1) / 2; }
static int flipOK(int maxlen, const Cell *bl, int n) {
    if (!(2 <= n && n <= maxlen && maxlen <= 11)) return 0;
    Cell ctx = bl[n - 1];
    i64 t = flipT(ctx);
    return cellsOK(bl, n) && hiSum(bl, n) + 2 <= DEN && bl[n - 2].hi + 1 <= ctx.lo && 3 <= ctx.lo && t <= ctx.lo &&
           ctx.hi + t + 1 <= DEN;
}
static int widen(i64 Kb, const Cell *bl, int n, Cell *out) {
    for (int i = 0; i < n; i++) {
        out[i].lo = max64(1, tsub(bl[i].lo, Kb));
        out[i].hi = bl[i].hi + Kb;
    }
    return n;
}
static int vboxF(Cell ctx, const Cell *beta, int nb, const Cell *bl, int n, Cell *out) {
    memcpy(out, bl, sizeof(Cell) * n);
    i64 hi = tsub(tsub(DEN, ctx.lo) + 1, loSum(beta, nb));
    if (hi < 2) return n;
    out[n].lo = max64(1, tsub(tsub(DEN, ctx.hi), hiSum(beta, nb)));
    out[n].hi = hi;
    return n + 1;
}
/* the exponents of a set of bits over ch ++ β ++ [cofactor] */
static i64 loR(i64 e1, const Cell *beta, int nb, const Cell *ch, int nch, u32 m) {
    u32 mA = m >> nch;
    i64 a = (mA >> nb & 1) ? tsub(e1, tsub(hiSum(beta, nb), mSum(1, beta, nb, mA))) : mSum(0, beta, nb, mA);
    return a + mSum(0, ch, nch, m);
}
static i64 hiR(i64 e2, const Cell *beta, int nb, const Cell *ch, int nch, u32 m) {
    u32 mA = m >> nch;
    i64 a = (mA >> nb & 1) ? tsub(e2, tsub(loSum(beta, nb), mSum(0, beta, nb, mA))) : mSum(1, beta, nb, mA);
    return a + mSum(1, ch, nch, m);
}
static i64 hiRc(i64 e2, const Cell *beta, int nb, const Cell *ch, int nch, u32 m) {
    u32 mA = m >> nch;
    i64 a = (mA >> nb & 1) ? tsub(hiSum(beta, nb), mSum(1, beta, nb, mA)) : tsub(e2, mSum(0, beta, nb, mA));
    return a + tsub(hiSum(ch, nch), mSum(1, ch, nch, m));
}
static int coreI2(i128 u, i128 v, i128 r1, i128 r2) {
    i128 Ln = G.Ln, Ld = G.Ld;
    return Ld * DEN + 2000 * Ln <= 2000 * Ln * r1 && 2 * Ld * DEN + 3 * Ln <= 3 * Ln * u &&
           2 * Ld * DEN + 3 * Ln * (r2 + 1 + v) <= 3 * Ln * DEN &&
           62505 * Ld * DEN + 90137 * Ln <= 62500 * Ln * u + 27637 * Ln * r1 &&
           62505 * Ld * DEN + 62500 * Ln * v + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN &&
           125005 * Ld * DEN + 34863 * Ln * (r2 + 1) <= 62500 * Ln * DEN;
}
static int coreJ(int three, i64 f, int e, i128 u, i128 v, i128 t, i128 r1, i128 r2, i128 c0lo, i128 c0hi, i128 h1s,
                 i128 h2s) {
    i128 D1, D2;
    if (three) {
        D1 = h1s + (e ? t + r2 : 0);
        D2 = h2s + (e ? 0 : t + r2);
    } else {
        D1 = h1s + (e ? t : 0);
        D2 = h2s + (e ? 0 : t);
    }
    return 0 < f && zone(r1, r2, u, v) && (!three || r1 + f < r2) && u + f < v && u <= t + c0lo && c0hi < v &&
           (leavesT(D1, D2) || (G.energy && leavesE(D1, D2)));
}
static int allIn(const Cell *bl, int n) {          /* all(1 <= c[0] <= c[1] <= DEN) */
    for (int i = 0; i < n; i++)
        if (!(1 <= bl[i].lo && bl[i].lo <= bl[i].hi && bl[i].hi <= DEN)) return 0;
    return 1;
}
static int okIF(const Cell *bl, int n, const Cfg *c) {
    int nb = FZ.nb, nch = (int)tsub(n, nb);
    const Cell *ch = bl, *beta = FZ.beta;
    i64 e1 = FZ.e1, e2 = FZ.e2;
    return allIn(bl, n) && (c->s0 & c->sr) == 0 && 0 < loR(e1, beta, nb, ch, nch, c->sr) &&
           coreI2(loR(e1, beta, nb, ch, nch, c->s0), hiR(e2, beta, nb, ch, nch, c->s0),
                  loR(e1, beta, nb, ch, nch, c->sr), hiR(e2, beta, nb, ch, nch, c->sr));
}
static int okJF3(const Cell *bl, int n, i64 f, const Cfg *c) {
    int nb = FZ.nb, nch = (int)tsub(n, nb);
    const Cell *ch = bl, *beta = FZ.beta;
    i64 e1 = FZ.e1, e2 = FZ.e2, Kb = FZ.Kb;
    i128 r1 = fillLo, r2 = fillLo + f + 1;
    i128 u = uOf(r1), c0lo = tsub(loR(e1, beta, nb, ch, nch, c->s0), Kb);
    return 0 < f && cellsIn(f, bl, n) &&
           coreJ(1, f, c->e, u, vOf(r2), tsubI(u, c0lo), r1, r2, c0lo, hiR(e2, beta, nb, ch, nch, c->s0) + Kb,
                 hiR(e2, beta, nb, ch, nch, c->s1) + Kb, hiRc(e2, beta, nb, ch, nch, c->s1) + Kb);
}
static int okJF2(const Cell *bl, int n, i64 f, const Cfg *c) {
    int nb = FZ.nb, nch = (int)tsub(n, nb);
    const Cell *ch = bl, *beta = FZ.beta;
    i64 e1 = FZ.e1, e2 = FZ.e2, Kb = FZ.Kb;
    i128 r1 = tsub(loR(e1, beta, nb, ch, nch, c->sr), Kb), r2 = hiR(e2, beta, nb, ch, nch, c->sr) + Kb;
    i128 u = uOf(r1), c0lo = tsub(loR(e1, beta, nb, ch, nch, c->s0), Kb);
    return 0 < f && cellsIn(f, bl, n) && (c->s0 & c->sr) == 0 && 0 < loR(e1, beta, nb, ch, nch, c->sr) &&
           coreJ(0, f, c->e, u, vOf(r2), tsubI(u, c0lo), r1, r2, c0lo, hiR(e2, beta, nb, ch, nch, c->s0) + Kb,
                 hiR(e2, beta, nb, ch, nch, c->s1) + Kb, hiRc(e2, beta, nb, ch, nch, c->s1) + Kb);
}
static inline int okJm(const Cell *bl, int n, i64 f, const Cfg *c) {
    if (!FZ.on) return okJ_T(bl, n, f, c);
    return c->kind == 2 ? okJF3(bl, n, f, c) : okJF2(bl, n, f, c);
}

/* ---------------------------------------------------------------------------------------------------------------
   The planner's counts: `W['calls']`, `W['fcalls']` and `stat` (its keys in the order they appear) */
enum {
    S_revtry, S_revwin, S_fams, S_rootfail, S_fliptry, S_flipwin, S_fliproot, S_flipcap, S_postry, S_poswin,
    S_posroot, S_poscap, S_replan, S_res, S_resy, S_exh, S_exhmiss, S_jexh, S_jmiss, S_noguide, S_again,
    S_splittry, S_splitwin, NSTAT
};
static const char *SNAME[NSTAT] = {"revtry", "revwin", "fams", "rootfail", "fliptry", "flipwin", "fliproot",
                                   "flipcap", "postry", "poswin", "posroot", "poscap", "replan", "res", "resy",
                                   "exh", "exhmiss", "jexh", "jmiss", "noguide", "again", "splittry", "splitwin"};
#define NFIXED 12
static i64 ST[NSTAT];
static int STord[NSTAT], STn, STin[NSTAT];
static i128 Wcalls, Wfcalls;
static int DBG;
static long MAXCALLS;

static void statReset(void) {
    memset(ST, 0, sizeof ST);
    memset(STin, 0, sizeof STin);
    STn = 0;
    for (int i = 0; i < NFIXED; i++) {
        STord[STn++] = i;
        STin[i] = 1;
    }
}
static inline void statAdd(int k, i64 d) {
    if (!STin[k]) {
        STin[k] = 1;
        STord[STn++] = k;
    }
    ST[k] += d;
}

/* ---------------------------------------------------------------------------------------------------------------
   The plans */
typedef struct Memo Memo;
typedef struct Node Node;
struct Node {
    uint8_t k, fz, stat_;
    double secs;
    union {
        struct { u32 mask; Memo *m; } r;
        struct { int sel, nk, nbits; Node **kids; uint8_t *bits; } b;
        struct { Node *a, *b; } s;
    } u;
};
static Node NSTATIC[3][2];
static long NLIVE, NPEAK;
static inline void nlive(int d) {
    NLIVE += d;
    if (NLIVE > NPEAK) NPEAK = NLIVE;
}

static inline double secOf(int k, int fz) {
    CHECK(G.SECp[k][fz], "no kernel time for a step of this kind");
    return G.SEC[k][fz];
}
static Node *mkLeaf(int k, int fz) { return &NSTATIC[k][fz]; }
static Node *mkR(int fz, u32 mask, Memo *m) {
    Node *x = malloc(sizeof(Node));
    CHECK(x, "out of memory");
    nlive(1);
    x->k = KR;
    x->fz = fz;
    x->stat_ = 0;
    x->secs = secOf(KR, fz);
    x->u.r.mask = mask;
    x->u.r.m = m;
    return x;
}
static Node *mkBFP(int k, int fz, int sel, Node **kids, int nk, uint8_t *bits, int nbits) {
    Node *x = malloc(sizeof(Node));
    CHECK(x, "out of memory");
    nlive(1);
    x->k = k;
    x->fz = fz;
    x->stat_ = 0;
    x->u.b.sel = sel;
    x->u.b.kids = kids;
    x->u.b.nk = nk;
    x->u.b.bits = bits;
    x->u.b.nbits = nbits;
    double t = secOf(k, fz);
    for (int i = 0; i < nk; i++) t += kids[i]->secs;
    x->secs = t;
    return x;
}
static Node *mkS(int fz, Node *a, Node *b) {
    Node *x = malloc(sizeof(Node));
    CHECK(x, "out of memory");
    nlive(1);
    x->k = KS;
    x->fz = fz;
    x->stat_ = 0;
    x->u.s.a = a;
    x->u.s.b = b;
    x->secs = secOf(KS, fz) + (a->secs + b->secs);
    return x;
}
static void nfree(Node *x) {
    if (!x || x->stat_) return;
    if (x->k == KB || x->k == KF || x->k == KP) {
        for (int i = 0; i < x->u.b.nk; i++) nfree(x->u.b.kids[i]);
        free(x->u.b.kids);
        free(x->u.b.bits);
    } else if (x->k == KS) {
        nfree(x->u.s.a);
        nfree(x->u.s.b);
    }
    free(x);
    nlive(-1);
}

/* ---------------------------------------------------------------------------------------------------------------
   The memo of the window's tests (`resmemo`): a key's state is absent, None, lazy (the hint found when the plan is
   written), or its hint */
enum { MNONE = 1, MLAZY = 2, MHINT = 3 };
struct Memo {
    Memo *next;
    int8_t y;                       /* 0: `(cs, hs, mom)`; 1: `('Y', cells)` */
    int8_t n, state;                /* state 0: not in Python's memo */
    i64 hs;
    void *hint;                     /* a HintX or a HintY, once found */
    i64 key[];
};
#define MHASH (1 << 20)
static Memo **MT;
static long MN;
static u64 mhash(int y, int n, i64 hs, const i64 *key) {
    u64 h = 1469598103934665603ULL ^ (u64)(y * 31 + n);
    int m = y ? 2 * n : n;
    for (int i = 0; i < m; i++) h = (h ^ (u64)key[i]) * 1099511628211ULL;
    h = (h ^ (u64)hs) * 1099511628211ULL;
    return h ^ (h >> 29);
}
static Memo *mget(int y, int n, i64 hs, const i64 *key, int make) {
    u64 h = mhash(y, n, hs, key) & (MHASH - 1);
    int m = y ? 2 * n : n;
    for (Memo *e = MT[h]; e; e = e->next)
        if (e->y == y && e->n == n && e->hs == hs && !memcmp(e->key, key, sizeof(i64) * m)) return e;
    if (!make) return NULL;
    Memo *e = calloc(1, sizeof(Memo) + sizeof(i64) * m);
    CHECK(e, "out of memory");
    e->y = y;
    e->n = n;
    e->hs = hs;
    memcpy(e->key, key, sizeof(i64) * m);
    e->next = MT[h];
    MT[h] = e;
    MN++;
    return e;
}
static void mclear(void) {
    if (!MT) {
        MT = calloc(MHASH, sizeof(Memo *));
        CHECK(MT, "out of memory");
        return;
    }
    for (int i = 0; i < MHASH; i++) {
        Memo *e = MT[i];
        while (e) {
            Memo *nx = e->next;
            free(e->hint);
            free(e);
            e = nx;
        }
        MT[i] = NULL;
    }
    MN = 0;
}

/* The float filters' answers by key, loose and strict: pure functions of the key, kept in a cache that is emptied
   when it grows past QMAX entries (which changes the time, not the plan) */
typedef struct QE QE;
struct QE {
    QE *next;
    u64 h;
    int8_t y, n, loose, strict;
    i64 hs;
    i64 key[];
};
#define QHASH (1 << 21)
#define QMAX 3000000
static QE **QT;
static long QN;
static void qclear(void) {
    if (!QT) {
        QT = calloc(QHASH, sizeof(QE *));
        CHECK(QT, "out of memory");
    }
    for (int i = 0; i < QHASH; i++) {
        QE *e = QT[i];
        while (e) {
            QE *nx = e->next;
            free(e);
            e = nx;
        }
        QT[i] = NULL;
    }
    QN = 0;
}
static QE *qget(int y, int n, i64 hs, const i64 *key) {
    if (QN >= QMAX) qclear();
    u64 h = mhash(y, n, hs, key);
    int m = y ? 2 * n : n;
    QE **slot = &QT[h & (QHASH - 1)];
    for (QE *e = *slot; e; e = e->next)
        if (e->h == h && e->y == y && e->n == n && e->hs == hs && !memcmp(e->key, key, sizeof(i64) * m)) return e;
    QE *e = malloc(sizeof(QE) + sizeof(i64) * m);
    CHECK(e, "out of memory");
    e->h = h;
    e->y = y;
    e->n = n;
    e->hs = hs;
    e->loose = e->strict = -1;
    memcpy(e->key, key, sizeof(i64) * m);
    e->next = *slot;
    *slot = e;
    QN++;
    return e;
}
static inline int qX(QE *q, int strict) {
    if (strict) {
        if (q->strict < 0) q->strict = (int8_t)quick(q->key, q->n, q->hs, 12, -1e-7, G.lv, 15, NULL);
        return q->strict;
    }
    if (q->loose < 0) q->loose = (int8_t)quick(q->key, q->n, q->hs, 22, 1e-9, G.lv, -1, NULL);
    return q->loose;
}
static inline int qY(QE *q, const i64 *lo, const i64 *hi, int strict) {
    if (strict) {
        if (q->strict < 0) q->strict = (int8_t)quickY(lo, hi, q->n, G.lv, 1);
        return q->strict;
    }
    if (q->loose < 0) q->loose = (int8_t)quickY(lo, hi, q->n, G.lv, 0);
    return q->loose;
}

/* the window's hint of a key (`rt.hint`, `Planner.hintY`), into the entry: 1 if found */
static int memoHint(Memo *e, int fast) {
    if (!e->y) {
        HintX h;
        if (!hintX(e->key, e->n, e->hs, G.lv, fast, &h)) return 0;
        HintX *p = malloc(sizeof(int) * 2 + sizeof(u64) * (h.k ? h.k : 1));
        CHECK(p, "out of memory");
        p->k = h.k;
        p->lvf = h.lvf;
        memcpy(p->rec, h.rec, sizeof(u64) * h.k);
        free(e->hint);
        e->hint = p;
        return 1;
    }
    i64 lo[MAXT], hi[MAXT];
    for (int i = 0; i < e->n; i++) {
        lo[i] = e->key[2 * i];
        hi[i] = e->key[2 * i + 1];
    }
    HintY h;
    if (!hintYc(lo, hi, e->n, fast, &h)) return 0;
    HintY *p = malloc(sizeof(HintY));
    CHECK(p, "out of memory");
    *p = h;
    free(e->hint);
    e->hint = p;
    return 1;
}

/* `resHint`: a rest of the box that the kernel's test passes (with its hint, or lazily), as its mask and memo entry;
   with `probe`, the strict float filter's word alone (nothing kept) */
static int resHint(const Cell *bl0, int n, int probe, u32 *maskOut, Memo **eOut) {
    if (!G.res) return 0;
    if (FZ.on && !G.resF) return 0;
    if (n > 13) return 0;
    for (int i = 0; i < n; i++)
        if (!(1 <= bl0[i].lo && bl0[i].lo <= bl0[i].hi && bl0[i].hi <= DEN)) return 0;
    Cell bl[MAXB];
    memcpy(bl, bl0, sizeof(Cell) * n);
    i128 ln = G.Ln, ld = G.Ld;
    i128 need = (DEN * ld * 25002 + ln * 25000 - 1) / (ln * 25000);
    int nch = n;
    CHECK(G.resF == 0 || G.resF == 1, "res_frozen 'chain' is not supported");
    CHECK(G.cof == 0 || G.cof == 1, "res_cof 'main'/'mom' is not supported");
    if (G.cof && !FZ.on) {
        i64 slo = loSum(bl, n), shi = hiSum(bl, n);
        int one = shi + 2 <= DEN && DEN + 1 <= slo + 2 * bl[0].lo;
        if (one) {
            bl[n].lo = max64(tsub(tsub(DEN, shi), 1), bl[0].lo);
            bl[n].hi = tsub(DEN, slo) + 1;
            n = nch = n + 1;
        }
    } else if (G.cof && FZ.on && G.resF && n > FZ.nb) {
        int nc = n - FZ.nb;
        i64 slo = loSum(bl, nc), shi = hiSum(bl, nc);
        if (FZ.e2 + shi + 2 <= DEN && DEN + 1 <= FZ.e1 + slo + 2 * bl[0].lo) {
            bl[n].lo = max64(tsub(tsub(tsub(DEN, FZ.e2), shi), 1), bl[0].lo);
            bl[n].hi = tsub(tsub(DEN, FZ.e1), slo) + 1;
            n = nch = n + 1;
        }
    }
    if (nch < 2) return 0;
    u32 top = (u32)1 << nch;
    CHECK(nch == n, "the rest's bits are the box's");
    /* Σ(lo − 1) and Σhi of every set */
    static i64 SL[1 << (MAXB - 1)], SH[1 << (MAXB - 1)];
    SL[0] = SH[0] = 0;
    for (u32 m = 1; m < top; m++) {
        int j = __builtin_ctz(m);
        SL[m] = SL[m & (m - 1)] + (bl[j].lo - 1);
        SH[m] = SH[m & (m - 1)] + bl[j].hi;
    }
    for (u32 mask = 3; mask < top; mask++) {
        if ((mask & (mask - 1)) == 0) continue;
        if (SL[mask] < need) continue;
        i64 cs[MAXT], hs = SH[mask];
        int k = 0;
        for (int p = 0; p < n; p++)
            if (mask >> p & 1) cs[k++] = bl[p].lo;
        QE *q = qget(0, k, hs, cs);
        if (!qX(q, 0)) continue;
        Memo *e = mget(0, k, hs, cs, 0);
        int st = e ? e->state : 0;
        if (st == 0 && probe) {
            if (qX(q, 1)) {
                *maskOut = mask;
                *eOut = NULL;
                return 1;
            }
            continue;
        }
        if (st == 0) {
            e = mget(0, k, hs, cs, 1);
            if (G.lazy && qX(q, 1))
                e->state = MLAZY;
            else
                e->state = memoHint(e, G.lazy) ? MHINT : MNONE;
            st = e->state;
        }
        if (st != MNONE) {
            if (!probe) statAdd(S_res, 1);
            *maskOut = mask;
            *eOut = e;
            return 1;
        }
    }
    if (G.ycorner) {
        for (u32 mask = 3; mask < top; mask++) {
            if ((mask & (mask - 1)) == 0) continue;
            if (SH[mask] < need) continue;
            i64 key[2 * MAXT], lo[MAXT], hi[MAXT];
            int k = 0;
            for (int p = 0; p < n; p++)
                if (mask >> p & 1) {
                    key[2 * k] = lo[k] = bl[p].lo;
                    key[2 * k + 1] = hi[k] = bl[p].hi;
                    k++;
                }
            QE *q = qget(1, k, 0, key);
            Memo *e = mget(1, k, 0, key, 0);
            int st = e ? e->state : 0;
            if (st == 0 && probe) {
                if (qY(q, lo, hi, 1)) {
                    *maskOut = mask;
                    *eOut = NULL;
                    return 1;
                }
                continue;
            }
            if (st == 0) {
                if (!qY(q, lo, hi, 0)) {
                    /* Python keeps None here. A probe of a key that its memo lacks asks the strict filter, so the
                       None is kept only where the strict filter passes: elsewhere a missing key and None give the
                       same answer to every later visit, probe or not */
                    if (qY(q, lo, hi, 1)) {
                        e = mget(1, k, 0, key, 1);
                        e->state = MNONE;
                    }
                    continue;
                }
                e = mget(1, k, 0, key, 1);
                if (G.lazy && qY(q, lo, hi, 1))
                    e->state = MLAZY;
                else
                    e->state = memoHint(e, G.lazy) ? MHINT : MNONE;
                st = e->state;
            }
            if (st != MNONE) {
                if (!probe) statAdd(S_resy, 1);
                *maskOut = mask;
                *eOut = e;
                return 1;
            }
        }
    }
    return 0;
}

/* ---------------------------------------------------------------------------------------------------------------
   The proposals and floors (Planner) */
static void pickCc(const Cell *bl, int j, u32 m, u32 *mr, i64 *lm, i64 *lo, i64 *hi) {
    *lm = DEN;
    *lo = 0;
    *hi = 0;
    for (int i = 0; i < j; i++) {
        *lm = min64(*lm, bl[i].lo);
        *lo += (m & 1) * bl[i].lo;
        *hi += (m & 1) * bl[i].hi;
        m >>= 1;
    }
    *mr = m;
}
static i64 floorP(int i, i64 f) {
    for (int k = 0; k < i; k++) f = 3 * f / 4;
    return f;
}
/* `cfgJF` with the hint `sel` (< 16): the floor and the configuration */
static FC cfgJF(i64 Kb, i64 cl, i64 chh, const Cell *beta, int nb, i64 lomb, const Cell *bl, int n, int sel) {
    u32 m;
    i64 lm, lo, hi;
    pickCc(bl, (int)tsub(n, nb), (u32)1 << (sel / 2), &m, &lm, &lo, &hi);
    u32 cofb = (m >> nb) & 1;
    i64 lmv = max64(1, tsub(min64(lm, lomb), Kb));
    i64 lov = max64(1, tsub(lo + mSum(0, beta, nb, m) + cofb * cl, Kb));
    i64 hiv = hi + mSum(1, beta, nb, m) + cofb * chh + Kb;
    u32 pw = (u32)1 << (n + 1);
    u32 s1 = (u32)tsub(pw / 2, 1);
    FC r;
    r.ok = 1;
    if (sel % 2 == 0) {
        r.f = (i64)minI(lmv, tsubI(vOfF(hiv), uOfF(lov) + 1));
        Cfg c = {1, 0, (u32)1 << (sel / 2), s1, 1};
        r.cfg = c;
    } else {
        r.f = floorP(sel / 2, (i64)minI(lmv, fmax3));
        Cfg c = {2, 0, 0, s1, 1};
        r.cfg = c;
    }
    return r;
}

static FC tryJ2(const Cell *bl, int n, i64 lmin, i64 ls, i64 hs, Cell c, u32 bit) {
    FC none = {0, 0, {0, 0, 0, 0, 0}};
    if (!restOK(c.lo, c.hi)) return none;
    i128 u = uOfF(c.lo), v = vOfF(c.hi);
    i128 f = minI(lmin, tsubI(v, u + 1));
    if (!(0 < f && hs + tsubI(u, tsub(ls, c.lo)) <= t5J())) return none;
    SM z = {0, 0};
    SM b = bestSub(v, bit, bl, n, 1, 0, 0, 0, tsub(ls, c.lo), z);
    SP sp = leavesOfJ2(bl, n, hs, tsubI(u, b.slo));
    if (!sp.ok) return none;
    FC r = {1, (i64)f, {1, b.mask, bit, sp.m, sp.e}};
    return r;
}
static FC guideJ(const Cell *bl, int n, i64 lmin, int sel) {
    FC none = {0, 0, {0, 0, 0, 0, 0}};
    i64 ls = loSum(bl, n), hs = hiSum(bl, n);
    if (t5J() < hs) return none;
    int j = sel / 2;
    if (sel % 2 == 0) {
        Cell z = {0, 0};
        return tryJ2(bl, n, lmin, ls, hs, j < n ? bl[j] : z, (u32)1 << j);
    }
    i64 f = (i64)minI(lmin, fmax3);
    for (int i = 0; i < j; i++) f = 3 * f / 4;
    return tryJ3(bl, n, ls, hs, f);
}
static FC guideX(const Cell *bl, int n, int sel);
static FC guide(const Cell *bl, int n, int sel) {
    if (!FZ.on) return guideJ(bl, n, lomin(bl, n), sel);
    Cell vb[MAXB + 1], wv[MAXB + 1], wb[MAXB];
    int nv = vboxF(FZ.ctx, FZ.beta, FZ.nb, bl, n, vb);
    widen(FZ.Kb, vb, nv, wv);
    widen(FZ.Kb, bl, n, wb);
    FC r = guideJ(wv, nv, lomin(wb, n), sel);
    if (G.exh && (!r.ok || !okJm(bl, n, r.f, &r.cfg))) return guideX(bl, n, sel);
    return r;
}

/* `sumsF`: loR, hiR and hiRc for every set of bits over ch ++ β ++ [cofactor] (a cache of the last boxes) */
#define SUMSC 64
static struct {
    int valid, n, nb;
    i64 e1, e2;
    Cell bl[MAXB];
    i64 lo[1024], hi[1024], hic[1024];
} SUMS[SUMSC];
static int sumsF(const Cell *bl, int n, i64 **lo, i64 **hi, i64 **hic) {
    i64 e1 = FZ.e1, e2 = FZ.e2;
    int nb = FZ.nb;
    u64 h = 7;
    for (int i = 0; i < n; i++) h = (h * 1000003) ^ (u64)bl[i].lo ^ ((u64)bl[i].hi << 1);
    h = (h ^ (u64)e1 ^ ((u64)e2 << 3) ^ (u64)nb) * 0x9E3779B97F4A7C15ULL;
    int slot = (int)(h >> 58);
    typeof(&SUMS[0]) Sx = &SUMS[slot];
    int N = 1 << n;
    if (!(Sx->valid && Sx->n == n && Sx->nb == nb && Sx->e1 == e1 && Sx->e2 == e2 &&
          !memcmp(Sx->bl, bl, sizeof(Cell) * n))) {
        int nch = n - nb;
        i64 lsb = loSum(bl + nch, nb), hsb = hiSum(bl + nch, nb), hsc = hiSum(bl, nch);
        static i64 cl[512], chh[512], blo[512], bh[512];
        cl[0] = chh[0] = blo[0] = bh[0] = 0;
        for (int m = 1; m < N; m++) {
            int j = __builtin_ctz(m);
            int r = m & (m - 1);
            Cell c = bl[j];
            if (j < nch) {
                cl[m] = cl[r] + c.lo;
                chh[m] = chh[r] + c.hi;
                blo[m] = blo[r];
                bh[m] = bh[r];
            } else {
                cl[m] = cl[r];
                chh[m] = chh[r];
                blo[m] = blo[r] + c.lo;
                bh[m] = bh[r] + c.hi;
            }
        }
        for (int m = 0; m < N; m++) {
            Sx->lo[m] = blo[m] + cl[m];
            Sx->lo[N + m] = tsub(e1, hsb - bh[m]) + cl[m];
            Sx->hi[m] = bh[m] + chh[m];
            Sx->hi[N + m] = tsub(e2, lsb - blo[m]) + chh[m];
            Sx->hic[m] = tsub(e2, blo[m]) + (hsc - chh[m]);
            Sx->hic[N + m] = (hsb - bh[m]) + (hsc - chh[m]);
        }
        Sx->valid = 1;
        Sx->n = n;
        Sx->nb = nb;
        Sx->e1 = e1;
        Sx->e2 = e2;
        memcpy(Sx->bl, bl, sizeof(Cell) * n);
    }
    *lo = Sx->lo;
    *hi = Sx->hi;
    *hic = Sx->hic;
    return 2 * N;
}

static FC guideX(const Cell *bl, int n, int sel) {
    FC none = {0, 0, {0, 0, 0, 0, 0}};
    i64 e1 = FZ.e1, e2 = FZ.e2, Kb = FZ.Kb;
    int nb = FZ.nb;
    const Cell *beta = FZ.beta;
    FC c0 = cfgJF(Kb, max64(1, tsub(e1, hiSum(beta, nb))), tsub(e2, loSum(beta, nb)), beta, nb, lomin(beta, nb), bl, n,
                  sel);
    i64 f = c0.f;
    int kind = c0.cfg.kind;
    u32 sr = c0.cfg.sr;
    if (!(0 < f && cellsIn(f, bl, n)) || n > 9) return none;
    i64 *lo, *hi, *hic;
    int N2 = sumsF(bl, n, &lo, &hi, &hic);
    i128 r1, r2, add;
    if (kind == 1) {
        if ((i64)sr >= N2 || !(0 < lo[sr])) return none;
        r1 = tsub(lo[sr], Kb);
        r2 = hi[sr] + Kb;
        add = 0;
    } else {
        r1 = fillLo;
        r2 = fillLo + f + 1;
        add = r2;
    }
    i128 u = uOf(r1), v = vOf(r2);
    if (!(zone(r1, r2, u, v) && u + f < v)) return none;
    i128 bestv = -1;
    u32 s0 = 0;
    for (int m = 0; m < N2; m++)
        if ((m & sr) == 0 && hi[m] + Kb < v && tsub(lo[m], Kb) > bestv) {
            bestv = tsub(lo[m], Kb);
            s0 = m;
        }
    if (bestv < 0) return none;
    i128 t = tsubI(u, bestv) + add;
    for (int s1 = 0; s1 < N2; s1++) {
        i128 h1 = hi[s1] + Kb, h2 = hic[s1] + Kb;
        /* on both sides D1 + D2 = h1 + h2 + t, and both tests need it below DEN (`leaves`: 2·Ln·(D1 + D2) + Ld·DEN <
           2·Ln·DEN; `leavesE`: D1 + D2 < DEN), so a set whose sum reaches DEN passes on neither */
        if (h1 + h2 + t >= DEN) continue;
        for (int ei = 0; ei < 2; ei++) {
            int e = ei == 0;
            i128 D1 = h1 + (e ? t : 0), D2 = h2 + (e ? 0 : t);
            if (leavesT(D1, D2) || (G.energy && leavesE(D1, D2))) {
                Cfg cfg = {kind, s0, sr, (u32)s1, e};
                if (okJm(bl, n, f, &cfg)) {
                    FC r = {1, f, cfg};
                    return r;
                }
                statAdd(S_jmiss, 1);
                return none;
            }
        }
    }
    return none;
}

/* `floorX`: (sel, floor) or sel = -1 */
static int floorX(const Cell *bl, int n, i64 lo0, i64 *fout) {
    i64 e1 = FZ.e1, e2 = FZ.e2, Kb = FZ.Kb;
    int nb = FZ.nb;
    const Cell *beta = FZ.beta;
    i64 cl = max64(1, tsub(e1, hiSum(beta, nb))), chh = tsub(e2, loSum(beta, nb));
    i64 lomb = lomin(beta, nb);
    i64 fs[16];
    int ord[16];
    for (int sel = 0; sel < 16; sel++) {
        fs[sel] = cfgJF(Kb, cl, chh, beta, nb, lomb, bl, n, sel).f;
        ord[sel] = sel;
    }
    /* sorted by (f, −sel), greatest first */
    for (int i = 1; i < 16; i++) {
        int x = ord[i], j = i - 1;
        while (j >= 0 && (fs[ord[j]] < fs[x] || (fs[ord[j]] == fs[x] && ord[j] > x))) {
            ord[j + 1] = ord[j];
            j--;
        }
        ord[j + 1] = x;
    }
    for (int i = 0; i < 16; i++) {
        int sel = ord[i];
        i64 f = fs[sel];
        if (0 < f && f <= lo0) {
            FC r = guide(bl, n, sel);
            if (r.ok && r.f == f && okJm(bl, n, r.f, &r.cfg)) {
                statAdd(S_jexh, 1);
                *fout = f;
                return sel;
            }
        }
    }
    return -1;
}

/* `propIF`: the configuration of an evaluation over a frozen part, if any */
static int propIF(const Cell *bl, int n, Cfg *out) {
    Cell vb[MAXB + 1];
    int nv = vboxF(FZ.ctx, FZ.beta, FZ.nb, bl, n, vb);
    Cfg cfg;
    if (propI2(vb, nv, loSum(vb, nv), &cfg))
        if (okIF(bl, n, &cfg)) {
            if (out) *out = cfg;
            return 1;
        }
    if (!G.exh) return 0;
    i64 e1 = FZ.e1, e2 = FZ.e2;
    int nb = FZ.nb, nch = n - nb;
    const Cell *beta = FZ.beta, *ch = bl;
    i64 lsb = loSum(bl, n), lsc = loSum(ch, nch), hsb_ = hiSum(beta, nb), lsb_ = loSum(beta, nb);
    int rim = n + 1 < 8 ? n + 1 : 8;
    for (int ri = 0; ri < rim; ri++) {
        u32 sr = (u32)1 << ri;
        i64 r1 = loR(e1, beta, nb, ch, nch, sr), r2 = hiR(e2, beta, nb, ch, nch, sr);
        if (r1 <= 0 || !restOK(r1, r2)) continue;
        i128 Uu_ = uminOf(r1), Vv = vOfF(r2);
        if (Vv < Uu_) continue;
        i64 cands[1 + 4096];
        int nc = 0;
        if (ri < n) {
            cands[nc++] = findSub2(Uu_, Vv, sr, bl, n, 1, 0, 0, 0, tsub(lsb, bl[ri].lo));
            for (u32 mb = 0; mb < ((u32)1 << nb); mb++) {
                if (ri >= nch && (mb >> (ri - nch) & 1)) continue;
                CHECK(nc < 4097, "propIF: too many candidates");
                cands[nc++] = findSub2(Uu_, Vv, ri < nch ? sr : 0, ch, nch, 1,
                                       tsub(e1, tsub(hsb_, mSum(1, beta, nb, mb))),
                                       tsub(e2, tsub(lsb_, mSum(0, beta, nb, mb))), (mb << nch) | ((u32)1 << n),
                                       ri < nch ? tsub(lsc, ch[ri].lo) : lsc);
            }
        } else
            cands[nc++] = findSub2(Uu_, Vv, 0, bl, n, 1, 0, 0, 0, lsb);
        for (int i = 0; i < nc; i++) {
            i64 m = cands[i];
            if (m > 0) {
                Cfg c = {1, (u32)m, sr, 0, 0};
                if (okIF(bl, n, &c)) {
                    statAdd(S_exh, 1);
                    if (out) *out = c;
                    return 1;
                }
                statAdd(S_exhmiss, 1);
            }
        }
    }
    return 0;
}

static int anyI(const Cell *bl, int n) {
    if (FZ.on) return propIF(bl, n, NULL);
    Cfg cfg;
    if (propI2(bl, n, loSum(bl, n), &cfg))
        if (okI_T(bl, n, &cfg)) return 1;
    return 0;
}

static int firstJ(const Cell *bl, int n, i64 lo0, const FC *ps, int np, FC *out) {
    for (int i = 0; i < np; i++) {
        i64 f = ps[i].f;
        if (0 < f && f <= lo0 && okJm(bl, n, f, &ps[i].cfg)) {
            *out = ps[i];
            return 1;
        }
    }
    return 0;
}
static int propJ(const Cell *bl, int n, FC *out) {
    if (!FZ.on) return propJF(bl, n, lomin(bl, n), out);
    Cell vb[MAXB + 1], wv[MAXB + 1], wb[MAXB];
    int nv = vboxF(FZ.ctx, FZ.beta, FZ.nb, bl, n, vb);
    widen(FZ.Kb, vb, nv, wv);
    widen(FZ.Kb, bl, n, wb);
    return propJF(wv, nv, lomin(wb, n), out);
}
static i64 guideLomin(const Cell *bl, int n) {
    if (!FZ.on) return lomin(bl, n);
    Cell wb[MAXB];
    widen(FZ.Kb, bl, n, wb);
    return lomin(wb, n);
}
static inline int cfgEq(const Cfg *a, const Cfg *b) {
    return a->kind == b->kind && a->s0 == b->s0 && a->sr == b->sr && a->s1 == b->s1 && a->e == b->e;
}
/* `floorOf`: sel (and the floor), or -1 */
static int floorOf(const Cell *bl, int n, i64 lo0, i64 *fout) {
    if (G.exh >= 2 && FZ.on) return floorX(bl, n, lo0, fout);
    FC ps[2], fj;
    int np = propJ(bl, n, ps);
    if (!firstJ(bl, n, lo0, ps, np, &fj)) return (G.exh && FZ.on) ? floorX(bl, n, lo0, fout) : -1;
    i64 f = fj.f;
    int sel = -1;
    if (fj.cfg.kind == 1) {
        u32 b = fj.cfg.sr;
        int bl_ = 32 - __builtin_clz(b);
        sel = 2 * (bl_ - 1);
    } else {
        i64 g = (i64)minI(guideLomin(bl, n), fmax3);
        for (int i = 0; i < 8; i++) {
            if (g == f) {
                sel = 2 * i + 1;
                break;
            }
            g = 3 * g / 4;
        }
    }
    int bad = sel < 0 || sel > 15;
    if (!bad) {
        FC r = guide(bl, n, sel);
        bad = !(r.ok && r.f == f && cfgEq(&r.cfg, &fj.cfg));
    }
    if (bad) {
        statAdd(S_noguide, 1);
        return (G.exh && FZ.on) ? floorX(bl, n, lo0, fout) : -1;
    }
    *fout = f;
    return sel;
}

/* ---------------------------------------------------------------------------------------------------------------
   The strategies and the operations of the two trees */
typedef struct { int frozen; Cell ctx; int na; } Ops;
typedef struct { int frozen; int depth; Cell ctx; int nb; } Strat;

typedef struct { int n, cap; i64 *v; } Vec;
static void vpush(Vec *a, i64 x) {
    if (a->n == a->cap) {
        a->cap = a->cap ? 2 * a->cap : 64;
        a->v = realloc(a->v, sizeof(i64) * a->cap);
        CHECK(a->v, "out of memory");
    }
    a->v[a->n++] = x;
}
static void geoCuts(i64 kappa, i64 st, i64 reg, int nn, i64 c, Vec *out) {
    while (nn > 0 && c < reg) {
        c = c + max64(1, min64(st, c / kappa));
        vpush(out, min64(c, reg));
        nn--;
    }
}
static inline i64 stepOf(int d) { return d <= 4 ? G.hI : G.hI * (1 + tsub(d, 3) / 2); }
static void cutsOfG(const Cell *bl, int n, i64 f, Vec *out) {
    out->n = 0;
    if (n == 0) return;
    i64 reg = min64(bl[0].hi, tsub(DEN, loSum(bl, n)) / 2 + 2);
    i64 last = tsub(DEN - 1, hiSum(bl, n));
    if (f < reg) geoCuts(G.kappa, stepOf(n + 1), reg, 4096, f, out);
    vpush(out, last);
    /* the flip's cut (`insCut`) */
    i64 c = tsub(bl[n - 1].lo, 1);
    if (f < c) {
        int i = 0;
        while (i < out->n && !(c < out->v[i]) && c != out->v[i]) i++;
        if (i < out->n && c == out->v[i]) return;
        vpush(out, 0);
        memmove(out->v + i + 1, out->v + i, sizeof(i64) * (out->n - 1 - i));
        out->v[i] = c;
    }
}
static void cutsKh(i64 hR, Cell ctx, const Cell *ch, int nch, i64 top, i64 f, Vec *out) {
    out->n = 0;
    i64 reg = min64(top, tsub(ctx.hi + 1, loSum(ch, nch)) / 2 + 2);
    i64 last = tsub(tsub(ctx.lo, 1), hiSum(ch, nch));
    if (f < reg) geoCuts(G.kappa, nch < 2 ? hR : 2 * hR, reg, 4096, f, out);
    vpush(out, last);
}
static void Scuts(const Strat *S, const Cell *bl, int n, i64 f, Vec *out) {
    if (!S->frozen) {
        cutsOfG(bl, n, f, out);
        return;
    }
    int nch = (int)tsub(n, S->nb);
    cutsKh(G.hF, S->ctx, bl, nch, nch ? bl[0].hi : flipT(S->ctx), f, out);
}
static inline int Ogrd(const Ops *O, int n) { return !O->frozen || (O->na < n && n <= 12); }
static inline int Ovan(const Ops *O, const Cell *bl, int n) {
    return O->frozen ? vanishK(O->ctx, bl, (int)tsub(n, O->na)) : vanishOK(bl, n);
}
static inline i128 Odrp(const Ops *O, const Cell *bl, int n, int par) {
    return O->frozen ? dropK(O->ctx, bl, (int)tsub(n, O->na), par) : dropC(bl, n, par);
}

/* ---------------------------------------------------------------------------------------------------------------
   The cells of a prime that remember what lost at the cells before them (`sib`, `want`, `note`, `again`) */
typedef struct {
    struct { int in, s0, s1, s2, s3; } st[4];      /* 'd', 'p', 'b', 'f'; s2: −1 None, 0 False, 1 True */
    int ltIn, lt, dollar, bang;
} Group;
enum { KEYD, KEYP, KEYB, KEYF };

static int want(Group *sib, int key) {
    if (!sib || sib->bang || key == KEYF) return 1;
    if (!sib->st[key].in || sib->st[key].s1 == 0) return 1;
    if (sib->dollar) {
        sib->st[key].s1 = 0;
        return 1;
    }
    sib->st[key].s1 -= 1;
    sib->st[key].s3 += 1;
    return 0;
}
static void note(Group *sib, int key, int won, i128 used) {
    if (!sib || sib->bang) return;
    typeof(&sib->st[0]) st = &sib->st[key];
    if (!st->in) {
        st->in = 1;
        st->s0 = st->s1 = st->s3 = 0;
        st->s2 = -1;
    }
    if (st->s3 && st->s2 != -1 && won != st->s2 && G.redo) {
        int cur = sib->ltIn ? sib->lt : 0;
        sib->lt = cur > st->s3 ? cur : st->s3;
        sib->ltIn = 1;
    }
    st->s2 = won;
    st->s3 = 0;
    if (won)
        st->s0 = st->s1 = 0;
    else if (used >= G.skipmin) {
        st->s0 = st->s0 + 1 < G.skip + 1 ? st->s0 + 1 : G.skip + 1;
        st->s1 = (1 << (st->s0 - 1)) - 1;
    }
}

/* ---------------------------------------------------------------------------------------------------------------
   The search as a plan */
static i128 pSolve(const Ops *O, const Strat *S, int n, const Cell *bl, int nbl, int par, i128 lim, Group *sib,
                   Node **out);

typedef struct { i64 s, c; Node *n; i128 cost; } KCell;

static inline int mkBox(i64 a, i64 b, const Cell *bl, int n, Cell *out) {
    CHECK(n + 1 <= MAXB, "a box of too many primes");
    out[0].lo = a;
    out[0].hi = b;
    memcpy(out + 1, bl, sizeof(Cell) * n);
    return n + 1;
}

static i128 again(const Ops *O, const Strat *S, int n, const Cell *bl, int nbl, int par, KCell *cells, int nc,
                  i128 tot, i128 lim, Group *grp) {
    int m = grp->lt, j = nc - 2;
    grp->ltIn = 0;
    grp->bang = 1;
    while (m > 0 && j >= 0) {
        KCell *x = &cells[j];
        i128 l1 = lim - (tot - x->cost);
        Cell b[MAXB];
        int nb = mkBox(x->s, x->c, bl, nbl, b);
        Node *n1 = NULL;
        i128 c1 = pSolve(O, S, n, b, nb, par, l1, grp, &n1);
        if (!n1 || l1 <= c1 || (c1 == x->cost && n1->k == x->n->k)) {
            nfree(n1);
            break;
        }
        nfree(x->n);
        x->n = n1;
        tot += c1 - x->cost;
        x->cost = c1;
        statAdd(S_again, 1);
        m--;
        j--;
    }
    grp->bang = 0;
    return tot;
}

/* `pKids`: the cells of the new prime (the cuts `cs` from `a` to `top`); the cost, and on success the kids and the
   bits */
static i128 pKids(const Ops *O, const Strat *S, int n, i64 top, const Cell *bl, int nbl, int par, const Vec *cs,
                  i64 a, i128 lim, Node ***kidsOut, int *nkOut, uint8_t **bitsOut, int *nbitsOut) {
    CHECK(G.blk == 1 && G.blkF == 1, "blocks of cells (blk > 1) are not supported");
    Group mine;
    memset(&mine, 0, sizeof mine);
    Group *grp = G.skip ? &mine : NULL;
    Group *rsib = grp;
    KCell *cells = malloc(sizeof(KCell) * (cs->n + 2));
    CHECK(cells, "out of memory");
    int nc = 0;
    i128 tot = 0;
    i64 s = a;
    Cell b[MAXB];
    *kidsOut = NULL;
#define FAIL_CELLS()                                                                                              \
    do {                                                                                                          \
        for (int _i = 0; _i < nc; _i++) nfree(cells[_i].n);                                                       \
        free(cells);                                                                                              \
    } while (0)
    for (int i = 0; i < cs->n; i++) {
        i64 c = cs->v[i];
        if (s < c && c < top) {
            int nb = mkBox(s, c, bl, nbl, b);
            Node *n1 = NULL;
            i128 c1 = pSolve(O, S, n, b, nb, par, lim - tot, rsib, &n1);
            tot += c1;
            if (lim <= tot) {
                nfree(n1);
                FAIL_CELLS();
                return tot;
            }
            CHECK(n1, "a cell below the limit without a plan");
            cells[nc].s = s;
            cells[nc].c = c;
            cells[nc].n = n1;
            cells[nc].cost = c1;
            nc++;
            s = c;
            if (grp && grp->ltIn) tot = again(O, S, n, bl, nbl, par, cells, nc, tot, lim, grp);
        }
    }
    if (grp) grp->dollar = 1;
    {
        int nb = mkBox(s, top, bl, nbl, b);
        Node *n1 = NULL;
        i128 c1 = pSolve(O, S, n, b, nb, par, lim - tot, rsib, &n1);
        tot += c1;
        if (lim <= tot) {
            nfree(n1);
            FAIL_CELLS();
            return tot;
        }
        CHECK(n1, "a cell below the limit without a plan");
        cells[nc].s = s;
        cells[nc].c = top;
        cells[nc].n = n1;
        cells[nc].cost = c1;
        nc++;
        if (grp && grp->ltIn) tot = again(O, S, n, bl, nbl, par, cells, nc, tot, lim, grp);
    }
    /* consecutive evaluated cells that one test covers are one cell; so are consecutive dropped cells whose one
       bound is within `dmerge` of the sum of theirs, and with `res_merge` consecutive cells of the window */
    int fz = FZ.on;
    Node **kids = malloc(sizeof(Node *) * nc);
    i64 *keep = malloc(sizeof(i64) * (nc + 1));
    CHECK(kids && keep, "out of memory");
    int nk = 0, nkeep = 0, i = 0;
    while (i < nc) {
        int j = i;
        int kind = cells[i].n->k;
        Node *merged = NULL;
        if (G.merge && kind == KE) {
            while (j + 1 < nc && cells[j + 1].n->k == KE) {
                int nb = mkBox(cells[i].s, cells[j + 1].c, bl, nbl, b);
                if (!anyI(b, nb)) break;
                j++;
            }
        } else if (G.rmerge && kind == KR) {
            while (j + 1 < nc && cells[j + 1].n->k == KR) {
                int nb = mkBox(cells[i].s, cells[j + 1].c, bl, nbl, b);
                u32 mask;
                Memo *e;
                if (!resHint(b, nb, 0, &mask, &e)) break;
                nfree(merged);
                merged = mkR(fz, mask, e);
                j++;
            }
        } else if (kind == KD) {
            i128 tsum = cells[i].cost;
            while (j + 1 < nc && cells[j + 1].n->k == KD) {
                int nb = mkBox(cells[i].s, cells[j + 1].c, bl, nbl, b);
                i128 u = Odrp(O, b, nb, par);
                if (u < 0) break;
                i128 tt = tsum + cells[j + 1].cost;
                if (G.dm1 * u > G.dm0 * tt && cmp_i128_double(u - tt, G.lamK * secOf(KD, fz)) > 0) break;
                j++;
                tsum += cells[j].cost;
            }
            if (j > i) {
                int nb = mkBox(cells[i].s, cells[j].c, bl, nbl, b);
                i128 u = Odrp(O, b, nb, par);
                tot += u - tsum;
            }
        }
        if (merged) {
            for (int q = i; q <= j; q++) nfree(cells[q].n);
            kids[nk++] = merged;
        } else {
            kids[nk++] = cells[i].n;
            for (int q = i + 1; q <= j; q++) nfree(cells[q].n);
        }
        if (j + 1 < nc) keep[nkeep++] = cells[j].c;
        i = j + 1;
    }
    free(cells);
    if (lim <= tot) {
        for (int q = 0; q < nk; q++) nfree(kids[q]);
        free(kids);
        free(keep);
        return tot;
    }
    /* the bits of the cuts, as the kernel reads them */
    uint8_t *bits = malloc(cs->n + 1);
    CHECK(bits, "out of memory");
    int nbits = 0, kp = 0;
    s = a;
    for (int q = 0; q < cs->n; q++) {
        i64 c = cs->v[q];
        if (s < c && c < top) {
            int in = 0;
            for (int z = 0; z < nkeep; z++)
                if (keep[z] == c) in = 1;
            (void)kp;
            if (in) {
                bits[nbits++] = 1;
                s = c;
            } else
                bits[nbits++] = 0;
        }
    }
    free(keep);
    *kidsOut = kids;
    *nkOut = nk;
    *bitsOut = bits;
    *nbitsOut = nbits;
    return tot;
#undef FAIL_CELLS
}

static i128 pBuch(const Ops *O, const Strat *S, int n, Cell x, const Cell *bl, int nbl, int par, i128 lim,
                  Node **out) {
    *out = NULL;
    if (nbl < S->depth) {
        i64 f;
        int sel = floorOf(bl, nbl, x.lo, &f);
        if (sel >= 0) {
            Vec cs = {0, 0, NULL};
            Scuts(S, bl, nbl, f, &cs);
            Node **kids;
            int nk, nbits;
            uint8_t *bits;
            i128 c = pKids(O, S, n, x.hi, bl, nbl, !par, &cs, f, lim, &kids, &nk, &bits, &nbits);
            free(cs.v);
            if (kids) *out = mkBFP(KB, FZ.on, sel, kids, nk, bits, nbits);
            return c;
        }
    }
    return lim + BIG;
}

static i128 pSplit(const Ops *O, const Strat *S, int n, Cell x, const Cell *bl, int nbl, int par, i128 lim,
                   Group *sib, Node **out) {
    *out = NULL;
    i64 mid = (x.lo + x.hi) / 2;
    if (G.wmin < tsub(x.hi, x.lo) && x.lo < mid && mid < x.hi) {
        Cell b[MAXB];
        int nb = mkBox(x.lo, mid, bl + 1, nbl - 1, b);
        Node *n1 = NULL, *n2 = NULL;
        i128 c1 = pSolve(O, S, n, b, nb, par, lim, sib, &n1);
        if (lim <= c1) {
            nfree(n1);
            return c1;
        }
        nb = mkBox(mid, x.hi, bl + 1, nbl - 1, b);
        i128 c2 = pSolve(O, S, n, b, nb, par, lim - c1, sib, &n2);
        if (lim <= c1 + c2) {
            nfree(n1);
            nfree(n2);
            return c1 + c2;
        }
        *out = mkS(FZ.on, n1, n2);
        return c1 + c2;
    }
    return lim + BIG;
}

/* `pFlip`: the box reversed through its largest prime, with the plan of its tree */
static i128 pFlip(const Cell *bl, int n, i128 lim, int pos, Node **out) {
    *out = NULL;
    CHECK(n >= 2 && n <= MAXB - 1, "pFlip: a box of fewer than two primes");
    Cell ctx = bl[n - 1];
    const Cell *beta = bl;
    int nb = n - 1;
    Cell tmp[MAXB];
    memcpy(tmp, beta, sizeof(Cell) * nb);
    tmp[nb].lo = tsub(ctx.hi, 1);
    tmp[nb].hi = ctx.hi + 1;
    i128 d1 = dropCost(tmp, nb + 1);
    tmp[nb].lo = tsub(ctx.lo, 1);
    tmp[nb].hi = ctx.lo + 1;
    i128 d2 = dropCost(tmp, nb + 1);
    U E = Uadd(Umul(Ui(ctx.hi + 1), Ui(d1)), Umul(Ui(ctx.lo + 1), Ui(d2)));
    U A = Umul(Ui(ctx.hi), Ui(dropCost(bl, n)));
    if (!pos) A = Uadd(A, E);
    i64 t = flipT(ctx);
    U B = Umul(Ui(bdK(ctx, t)), E);
    if (Uz(A)) return lim;
    U X = Ust(Umul(Ui(tsubI(lim, 1)), Ui((i128)DEN * KC)), B);
    U q = Ufdiv(X, A);
    i128 cl;
    if (Ule(Ui(CAPK), Uadd(q, Uu(1))))
        cl = CAPK;
    else
        cl = UtoI(q) + 1;
    Cell c = beta[0];
    FZ.on = 1;
    FZ.e1 = tsub(DEN, ctx.hi) + pos;
    FZ.e2 = tsub(DEN, ctx.lo) + 1 - pos;
    FZ.Kb = 12 + DEN / beta[0].lo;
    memcpy(FZ.beta, beta, sizeof(Cell) * nb);
    FZ.nb = nb;
    FZ.ctx = ctx;
    i128 w0 = Wcalls;
    Strat S = {1, G.depthF + nb, ctx, nb};
    i64 f;
    int sel = floorOf(beta, nb, min64(c.lo, t), &f);
    if (sel < 0) {
        statAdd(pos ? S_posroot : S_fliproot, 1);
        FZ.on = 0;
        Wfcalls += Wcalls - w0;
        return lim;
    }
    Ops O = {1, ctx, nb};
    Vec cs = {0, 0, NULL};
    Scuts(&S, beta, nb, f, &cs);
    Node **kids;
    int nk, nbits;
    uint8_t *bits;
    i128 cc = pKids(&O, &S, G.fuel, t, beta, nb, !pos, &cs, f, cl, &kids, &nk, &bits, &nbits);
    free(cs.v);
    FZ.on = 0;
    Wfcalls += Wcalls - w0;
    if (cl <= cc) {
        statAdd(pos ? S_poscap : S_flipcap, 1);
        CHECK(!kids, "a tree at its cap with a plan");
        return lim;
    }
    CHECK(kids != NULL, "a tree below its cap without a plan");
    U num = Uadd(Umul(Ui(cc), A), B);
    i128 cost = UtoI(Ushr(Uadd(num, Usub(Ushl(Uu(1), 100), Uu(1))), 100));     /* DEN·K = 2^100 */
    *out = mkBFP(pos ? KP : KF, 0, sel, kids, nk, bits, nbits);
    return cost;
}

/* `nearRes`: the top 1/2^j of the box's first cell passes the window's filter for some rest */
static int nearRes(const Cell *bl, int n) {
    Cell x = bl[0];
    i64 lo = x.lo, w = tsub(x.hi, x.lo);
    for (int k = 0; k < G.split; k++) {
        if (!(G.wmin < w && lo < (lo + x.hi) / 2 && (lo + x.hi) / 2 < x.hi)) return 0;
        lo = (lo + x.hi) / 2;
        w = tsub(x.hi, lo);
        Cell b[MAXB];
        int nb = mkBox(lo, x.hi, bl + 1, n - 1, b);
        u32 mask;
        Memo *e;
        if (resHint(b, nb, 1, &mask, &e)) return 1;
    }
    return 0;
}

static i128 pSolve1(const Ops *O, const Strat *S, int n, const Cell *bl, int nbl, int par, i128 lim, Group *sib,
                    Node **out);

static i128 pSolve(const Ops *O, const Strat *S, int n, const Cell *bl, int nbl, int par, i128 lim, Group *sib,
                   Node **out) {
    Node *node = NULL;
    i128 c = pSolve1(O, S, n, bl, nbl, par, lim, sib, &node);
    *out = node;
    if (!(G.split || G.split2) || !node || c == 0 || n <= 1 || nbl == 0 || node->k == KE || node->k == KR ||
        node->k == KV || node->k == KS)
        return c;
    Cell x = bl[0];
    /* `split2`: a box of two primes of the main tree is also tried cut in two, down to cells of 1/2^j of the grid's
       step; with a price on the kernel's time the cut is kept where it costs less with the time of the two halves
       counted (the sums as Python's: the costs as floats) */
    int two = G.split2 && !FZ.on && nbl == 2 && G.wmin < tsub(x.hi, x.lo) &&
              G.hI < tsub(x.hi, x.lo) * ((i64)1 << G.split2);
    if (!two && !nearRes(bl, nbl)) return c;
    statAdd(S_splittry, 1);
    Node *ns = NULL;
    i128 cs = pSplit(O, S, n - 1, x, bl, nbl, par, c, sib, &ns);
    if (ns && cs < c &&
        (!(two && G.lamK != 0.0) || (double)cs + G.lamK * ns->secs < (double)c + G.lamK * node->secs)) {
        statAdd(S_splitwin, 1);
        nfree(node);
        *out = ns;
        return cs;
    }
    nfree(ns);
    return c;
}

static i128 pSolve1(const Ops *O, const Strat *S, int n, const Cell *bl, int nbl, int par, i128 lim, Group *sib,
                    Node **out) {
    *out = NULL;
    if (n == 0 || nbl == 0 || !Ogrd(O, nbl)) return lim;
    Wcalls += 1;
    if (MAXCALLS && Wcalls >= MAXCALLS) exit(0);
    if (DBG && (Wcalls & ((1 << 20) - 1)) == 0)
        fprintf(stderr, "  %ld M boxes: %ld nodes live (peak %ld), %ld memo entries, %ld cached filters\n",
                (long)(Wcalls >> 20), NLIVE, NPEAK, MN, QN);
    int fz = FZ.on;
    if (Ovan(O, bl, nbl)) {
        *out = mkLeaf(KV, fz);
        return 0;
    }
    if (anyI(bl, nbl)) {
        *out = mkLeaf(KE, fz);
        return 0;
    }
    {
        u32 mask;
        Memo *e;
        if (resHint(bl, nbl, 0, &mask, &e)) {
            *out = mkR(fz, mask, e);
            return 0;
        }
    }
    Cell x = bl[0];
    double lam = G.lamK;
    int skip = G.skip;
    int OR = !O->frozen;
    i128 dc = Odrp(O, bl, nbl, par);
    if (dc >= 0) {
        i128 r;
        Node *how;
        if (skip && dc <= lim && !want(sib, KEYD)) {
            r = dc;
            how = mkLeaf(KD, fz);
        } else {
            i128 w0 = Wcalls;
            Node *nb = NULL;
            i128 bc = pBuch(O, S, n - 1, x, bl, nbl, par, dc <= lim ? dc : lim, &nb);
            if (dc <= bc) {
                r = dc;
                how = mkLeaf(KD, fz);
                nfree(nb);
            } else if (lam != 0 && nb && dc < lim &&
                       cmp_i128_double(dc - bc, lam * (nb->secs - secOf(KD, fz))) < 0) {
                r = dc;
                how = mkLeaf(KD, fz);
                nfree(nb);
            } else {
                r = bc;
                how = nb;
            }
            if (skip && dc <= lim) note(sib, KEYD, how != NULL && how->k != KD, Wcalls - w0);
        }
        if (G.pos && OR && par && 0 < r && how && flipOK(G.maxlen, bl, nbl) && (!skip || want(sib, KEYP))) {
            statAdd(S_postry, 1);
            i128 w0 = Wcalls;
            Node *nf = NULL;
            i128 c = pFlip(bl, nbl, r <= lim ? r : lim, 1, &nf);
            int won = nf && c < r && (lam == 0 || addIF(c, lam * nf->secs) < addIF(r, lam * how->secs));
            if (skip) note(sib, KEYP, won, Wcalls - w0);
            if (won) {
                statAdd(S_poswin, 1);
                nfree(how);
                *out = nf;
                return c;
            }
            nfree(nf);
        }
        *out = how;
        return r;
    }
    int rev = OR && !par && flipOK(G.maxlen, bl, nbl);
    if (skip && rev && !want(sib, KEYB)) {
        statAdd(S_fliptry, 1);
        i128 w0 = Wcalls;
        Node *nf = NULL;
        i128 c = pFlip(bl, nbl, lim, 0, &nf);
        if (nf) {
            statAdd(S_flipwin, 1);
            *out = nf;
            return c;
        }
        note(sib, KEYF, 0, Wcalls - w0);
        note(sib, KEYB, 1, 0);
        rev = 0;
    }
    i128 w0 = Wcalls;
    Node *nb = NULL;
    i128 bc = pBuch(O, S, n - 1, x, bl, nbl, par, lim, &nb);
    i128 w1 = Wcalls;
    i128 l2 = bc <= lim ? bc : lim;
    if (OR && !par) {
        i128 r = l2;
        Node *how = NULL;
        if (rev && (!skip || !nb || want(sib, KEYF))) {
            statAdd(S_fliptry, 1);
            if (lam != 0 && nb) {
                Node *nf = NULL;
                i128 c = pFlip(bl, nbl, lim, 0, &nf);
                int won = nf && addIF(c, lam * nf->secs) < addIF(bc, lam * nb->secs);
                if (skip) {
                    note(sib, KEYF, won, Wcalls - w1);
                    note(sib, KEYB, !won, w1 - w0);
                }
                if (won) {
                    statAdd(S_flipwin, 1);
                    nfree(nb);
                    *out = nf;
                    return c;
                }
                nfree(nf);
            } else {
                Node *nf = NULL;
                i128 c = pFlip(bl, nbl, r, 0, &nf);
                if (skip && nb) {
                    note(sib, KEYF, c < r, Wcalls - w1);
                    note(sib, KEYB, !(c < r), w1 - w0);
                }
                if (c < r) {
                    statAdd(S_flipwin, 1);
                    r = c;
                    how = nf;
                } else
                    nfree(nf);
            }
        }
        if (r < l2) {
            nfree(nb);
            *out = how;
            return r;
        }
        nfree(how);
    }
    if (bc < BIG) {
        *out = nb;
        return bc;
    }
    nfree(nb);
    return pSplit(O, S, n - 1, x, bl, nbl, par, lim, sib, out);
}

/* ---------------------------------------------------------------------------------------------------------------
   The hints of the plan's lazy leaves (`resolve`) */
typedef struct { Memo **v; int n, cap; } MVec;
static void resolve(Node *x, MVec *bad) {
    if (x->k == KR) {
        Memo *e = x->u.r.m;
        if (e->state == MLAZY) e->state = memoHint(e, 1) ? MHINT : MNONE;
        if (e->state == MNONE) {
            for (int i = 0; i < bad->n; i++)
                if (bad->v[i] == e) return;
            if (bad->n == bad->cap) {
                bad->cap = bad->cap ? 2 * bad->cap : 16;
                bad->v = realloc(bad->v, sizeof(Memo *) * bad->cap);
            }
            bad->v[bad->n++] = e;
        }
    } else if (x->k == KB || x->k == KF || x->k == KP) {
        for (int i = 0; i < x->u.b.nk; i++) resolve(x->u.b.kids[i], bad);
    } else if (x->k == KS) {
        resolve(x->u.s.a, bad);
        resolve(x->u.s.b, bad);
    }
}

/* ---------------------------------------------------------------------------------------------------------------
   Output: the plan's nodes in prefix order. `V`, `E`, `D`; `R mask k h` (the window's test, `h` in hex) or `Y mask s`
   (the test at the two corners, `s` packed as `res_test.packY`); `B sel nk bits kid…`, `F …`, `P …` (`bits` a string
   of 0 and 1, `-` if none); `S kid kid`. */
typedef struct { u64 w[64]; int nbits; } Bits;
static void bput(Bits *b, u64 v, int nb) {
    for (int i = 0; i < nb; i++, b->nbits++) {
        CHECK(b->nbits < 64 * 64, "a hint too long");
        if (v >> i & 1) b->w[b->nbits / 64] |= (u64)1 << (b->nbits % 64);
    }
}
static void bhex(FILE *f, const Bits *b) {
    int nd = (b->nbits + 3) / 4;
    while (nd > 1) {
        int i = nd - 1;
        if ((b->w[i * 4 / 64] >> (i * 4 % 64) & 15) != 0) break;
        nd--;
    }
    if (nd == 0) nd = 1;
    for (int i = nd - 1; i >= 0; i--) fputc("0123456789abcdef"[b->w[i * 4 / 64] >> (i * 4 % 64) & 15], f);
}
static void emit(FILE *f, const Node *x) {
    switch (x->k) {
    case KV: case KE: case KD:
        fputc(KCH[x->k], f);
        fputc(' ', f);
        break;
    case KR: {
        Memo *e = x->u.r.m;
        CHECK(e->state == MHINT, "a leaf of the window without its hint");
        Bits b;
        memset(&b, 0, sizeof b);
        if (!e->y) {
            const HintX *h = (const HintX *)e->hint;
            int k = h->k;
            if (h->lvf) bput(&b, (u64)k, 4);
            for (int i = 0; i < k; i++) bput(&b, h->rec[i], RC.EB);
            fprintf(f, "R %u %d ", x->u.r.mask, h->lvf ? 0 : k);
        } else {
            const HintY *h = (const HintY *)e->hint;
            int w = RC.EB + 2 + 3 * h->n;
            bput(&b, (u64)h->n, 4);
            bput(&b, (u64)h->kH, 4);
            bput(&b, (u64)h->kL, 4);
            for (int i = 0; i < h->kH; i++) bput(&b, h->recH[i], w);
            for (int i = 0; i < h->kL; i++) bput(&b, h->recL[i], w);
            fprintf(f, "Y %u ", x->u.r.mask);
        }
        bhex(f, &b);
        fputc(' ', f);
        break;
    }
    case KB: case KF: case KP:
        fprintf(f, "%c %d %d ", KCH[x->k], x->u.b.sel, x->u.b.nk);
        if (x->u.b.nbits == 0) fputc('-', f);
        for (int i = 0; i < x->u.b.nbits; i++) fputc('0' + x->u.b.bits[i], f);
        fputc(' ', f);
        for (int i = 0; i < x->u.b.nk; i++) emit(f, x->u.b.kids[i]);
        break;
    case KS:
        fputs("S ", f);
        emit(f, x->u.s.a);
        emit(f, x->u.s.b);
        break;
    }
}
static void putI(FILE *f, i128 x) {
    char buf[64];
    int i = 63, neg = x < 0;
    u128 m = neg ? (u128)0 - (u128)x : (u128)x;
    buf[i] = 0;
    do {
        buf[--i] = '0' + (int)(m % 10);
        m /= 10;
    } while (m);
    if (neg) buf[--i] = '-';
    fputs(buf + i, f);
}

/* the generator (`--cgen`) */
static i128 parseI(const char *s);
#include "gen.h"

/* `row_job`'s plan of one cell of the first prime; with `cut`, a heavy cell's parts and pieces (`cut`) in place of
   its plan, and the counts of its plan's steps */
static int CUTMODE;
static void planCell(i64 a, i64 b, FILE *f) {
    mclear();
    Wcalls = Wfcalls = 0;
    i64 replan = 0;
    Node *node = NULL;
    i128 c;
    for (;;) {
        statReset();
        if (replan) statAdd(S_replan, replan);
        memset(&FZ, 0, sizeof FZ);
        Ops O = {0, {0, 0}, 0};
        Strat S = {0, G.depth, {0, 0}, 0};
        Cell box[1] = {{a, b}};
        c = pSolve(&O, &S, G.fuel, box, 1, 0, KC, NULL, &node);
        CHECK(node && c < KC, "the cell's plan is not below K");
        if (!G.lazy) break;
        MVec bad = {NULL, 0, 0};
        resolve(node, &bad);
        if (bad.n == 0) break;
        replan = bad.n;
        free(bad.v);
        nfree(node);
        node = NULL;
    }
    fprintf(f, "CELL %lld %lld\nCOST ", (long long)a, (long long)b);
    putI(f, c);
    fputs("\nCALLS ", f);
    putI(f, Wcalls);
    fputc(' ', f);
    putI(f, Wfcalls);
    fputs("\nSTAT", f);
    for (int i = 0; i < STn; i++) fprintf(f, " %s %lld", SNAME[STord[i]], (long long)ST[STord[i]]);
    if (CUTMODE && !(node->secs <= CAP) && node->k == KB) {
        Part cp;
        memset(&cp, 0, sizeof cp);
        countg(node, 0, &cp);
        fputs("\nCOUNT", f);
        for (int i = 0; i < cp.nord; i++) {
            int k = cp.ord[i] / 2, z = cp.ord[i] % 2;
            fprintf(f, " %c %d %ld", KCH[k], z, cp.cnt[k][z]);
        }
        fputc('\n', f);
        cutAndWrite(f, node, a, b);
        fputs("END\n", f);
    } else {
        fputs("\nTREE ", f);
        emit(f, node);
        fputs("\nEND\n", f);
    }
    fflush(f);
    if (getenv("CPLAN_DEBUG")) fprintf(stderr, "cell %lld %lld: %ld memo entries\n", (long long)a, (long long)b, MN);
    nfree(node);
}

/* ---------------------------------------------------------------------------------------------------------------
   The parameters */
static char *tokbuf;
static char *nextTok(void) {
    char *t = strtok(tokbuf, " \t\r\n");
    tokbuf = NULL;
    CHECK(t, "the parameters end early");
    return t;
}
static i128 parseI(const char *s) {
    int neg = 0;
    if (*s == '-') neg = 1, s++;
    u128 x = 0;
    for (; *s; s++) {
        CHECK(*s >= '0' && *s <= '9', "a malformed integer in the parameters");
        x = x * 10 + (u128)(*s - '0');
    }
    return neg ? -(i128)x : (i128)x;
}
static U parseU(const char *s) {
    U x = U0();
    for (; *s; s++) {
        CHECK(*s >= '0' && *s <= '9', "a malformed integer in the parameters");
        x = Uadd(Umul(x, Uu(10)), Uu((u128)(*s - '0')));
    }
    return x;
}
static i128 rdI(const char *name) {
    char *t = nextTok();
    CHECK(!strcmp(t, name), name);
    return parseI(nextTok());
}
static double rdF(const char *name) {
    char *t = nextTok();
    CHECK(!strcmp(t, name), name);
    return strtod(nextTok(), NULL);       /* hex floats: exact */
}
static U rdU(const char *name) {
    char *t = nextTok();
    CHECK(!strcmp(t, name), name);
    return parseU(nextTok());
}

static void readParams(const char *path) {
    FILE *f = fopen(path, "r");
    CHECK(f, "cannot open the parameters");
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *buf = malloc(sz + 1);
    CHECK(buf && fread(buf, 1, sz, f) == (size_t)sz, "cannot read the parameters");
    buf[sz] = 0;
    fclose(f);
    tokbuf = buf;
    CHECK(rdI("version") == 1, "the parameters' version");
    DEN = (i64)rdI("DEN");
    KC = rdI("K");
    BIG = rdI("BIG");
    CAPK = rdI("CAPK");
    G.Ln = (i64)rdI("Ln");
    G.Ld = (i64)rdI("Ld");
    G.hI = (i64)rdI("hI");
    G.hF = (i64)rdI("hF");
    G.hR = (i64)rdI("hR");
    G.hQ = (i64)rdI("hQ");
    G.wmin = (i64)rdI("wmin");
    G.kappa = (i64)rdI("kappa");
    G.depth = (int)rdI("depth");
    G.depthR = (int)rdI("depthR");
    G.depthF = (int)rdI("depthF");
    G.maxlen = (int)rdI("maxlen");
    G.fuel = (int)rdI("fuel");
    G.pos = (int)rdI("pos");
    G.skip = (int)rdI("skip");
    G.skipmin = (int)rdI("skipmin");
    G.energy = (int)rdI("energy");
    G.res = (int)rdI("res");
    G.resF = (int)rdI("resF");
    G.cof = (int)rdI("cof");
    G.lv = (int)rdI("lv");
    G.lazy = (int)rdI("lazy");
    G.rmerge = (int)rdI("rmerge");
    G.split = (int)rdI("split");
    G.ycorner = (int)rdI("ycorner");
    G.exh = (int)rdI("exh");
    G.split2 = (int)rdI("split2");
    G.blk = (int)rdI("blk");
    G.blkF = (int)rdI("blkF");
    G.redo = (int)rdI("redo");
    G.merge = (int)rdI("merge");
    G.lamK = rdF("lamK");
    G.dm0 = (i64)rdI("dm0");
    G.dm1 = (i64)rdI("dm1");
    for (int k = 0; k < NKIND; k++)
        for (int z = 0; z < 2; z++) {
            char name[16];
            snprintf(name, sizeof name, "SEC%c%d", KCH[k], z);
            char *t = nextTok();
            CHECK(!strcmp(t, name), name);
            char *v = nextTok();
            if (!strcmp(v, "none"))
                G.SECp[k][z] = 0;
            else {
                G.SECp[k][z] = 1;
                G.SEC[k][z] = strtod(v, NULL);
            }
        }
    G.nlx = (int)rdI("nleaf");
    CHECK(G.nlx <= 32, "too many leaf checks");
    for (int i = 0; i < G.nlx; i++)
        for (int j = 0; j < 12; j++) G.LX[i][j] = (i64)parseI(nextTok());
    G.TOPK = rdI("TOPK");
    G.W1K = rdI("W1K");
    G.LD = rdI("LD");
    for (int i = 0; i < 17; i++) G.LNT[i] = parseI(nextTok());
    /* res_test */
    RC.Ln = G.Ln;
    RC.Ld = G.Ld;
    RC.DEN = (i64)rdI("rDEN");
    RC.NP = (int)rdI("NP");
    RC.PK = (int)rdI("PK");
    RC.GB = (int)rdI("GB");
    RC.EB = (int)rdI("EB");
    RC.SH = (int)rdI("SH");
    RC.LVKS = (int)rdI("LVKS");
    RC.S = rdU("S");
    RC.S2 = Umul(RC.S, RC.S);
    RC.HALF = Ushr(RC.S, 1);
    CHECK(rdI("nFT") == RC.NP + 1, "FT");
    for (int i = 0; i <= RC.NP; i++) RC.FT[i] = parseU(nextTok());
    for (int i = 0; i <= RC.NP; i++) RC.FTM[i] = parseU(nextTok());
    for (int i = 0; i <= RC.NP; i++) RC.IA[i] = parseU(nextTok());
    for (int i = 0; i <= RC.NP; i++) RC.DH[i] = parseU(nextTok());
    RC.WC = rdU("WC");
    RC.MG = rdU("MG");
    RC.K1U = rdU("K1U");
    RC.K1D = rdU("K1D");
    RC.M1U = rdU("M1U");
    RC.M1D = rdU("M1D");
    RC.HP = rdU("HP");
    RC.LVE = rdU("LVE");
    RC.OFF = rdU("OFF");
    RC.E23 = rdU("E23");
    RC.C310 = rdU("C310");
    RC.C15U = rdU("C15U");
    RC.C15D = rdU("C15D");
    RC.C65D = rdU("C65D");
    RC.C43 = rdU("C43");
    RC.W2 = rdU("W2");
    RC.nck = (int)rdI("nCK");
    for (int i = 0; i < RC.nck; i++) RC.CK[i] = parseU(nextTok());
    CHECK(rdI("nHF") == RC.NP, "HF");
    for (int i = 0; i < RC.NP; i++) {
        RC.HFlo[i] = strtod(nextTok(), NULL);
        RC.HFhi[i] = strtod(nextTok(), NULL);
        RC.HFA[i] = strtod(nextTok(), NULL);
        RC.TF[i] = strtod(nextTok(), NULL);
    }
    RC.CHI = rdF("CHI");
    RC.LVEQ = rdF("LVEQ");
    /* the search's constants */
    restLo = rdI("restLo");
    restHi = rdI("restHi");
    uC0 = rdI("uC0");
    uA = rdI("uA");
    uB = rdI("uB");
    uC = rdI("uC");
    vA = rdI("vA");
    vB = rdI("vB");
    vC = rdI("vC");
    umC0 = rdI("umC0");
    umA = rdI("umA");
    D1max = rdI("D1max");
    T5 = rdI("T5");
    T6 = rdI("T6");
    T5E = rdI("T5E");
    u3 = rdI("u3");
    fmax3 = rdI("fmax3");
    fillLo = rdI("fillLo");
    /* the generator's */
    G.hl = (int)rdI("hl");
    CAP = rdF("cap");
    LEVELS = (int)rdI("levels");
    CHECK(!strcmp(nextTok(), "end"), "the parameters' end");
    free(buf);
    for (int z = 0; z < 2; z++) {
        int ks[3] = {KV, KE, KD};
        for (int i = 0; i < 3; i++) {
            Node *x = &NSTATIC[i][z];
            x->k = ks[i];
            x->fz = z;
            x->stat_ = 1;
            x->secs = G.SECp[ks[i]][z] ? G.SEC[ks[i]][z] : 0;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: hint_plan PARAMS [cut] < CELLS, or hint_plan PARAMS gen < COMMANDS\n");
        return 2;
    }
    readParams(argv[1]);
    DBG = getenv("CPLAN_DEBUG") != NULL;
    leavesInit();
    if (getenv("CPLAN_MAXCALLS")) MAXCALLS = atol(getenv("CPLAN_MAXCALLS"));
    qclear();
    if (argc > 2 && !strcmp(argv[2], "gen")) {
        genMain(stdin, stdout);
        return 0;
    }
    CUTMODE = argc > 2 && !strcmp(argv[2], "cut");
    long long a, b;
    while (scanf("%lld %lld", &a, &b) == 2) planCell(a, b, stdout);
    return 0;
}
