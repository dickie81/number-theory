// Exact arithmetic of the certificate: coordinates, linear forms, boxes, the omega* table, the cell bounds.
// Everything here is integer arithmetic (int64 / int128); this is what the kernel would evaluate.
#pragma once
#include <cstdint>
#include <cstdlib>
#include <cstdio>
#include <algorithm>
#include <vector>
#include "omtable.h"

typedef long long i64;
typedef __int128 i128;

// coordinates: alpha = x / DEN, DEN = 100 * 2^30. theta = 1/2 + 1/G for the root grid's G (compile with -DGRID=50 for
// Li's 13/25, the default 40 for 21/40); then gamma(theta) = 4 theta - 2 = 4/G (Lemma 4.1's), and all of Li's constants
// below are exact, and dyadic splits stay exact
#ifndef GRID
#define GRID 40
#endif
static const i64 DEN = 100LL << 30;
static const i64 G = GRID;
static const i64 DG = DEN / G;            // the root grid's step 1/G
static const i64 NU0 = 2 * DG;            // nu0 = 2 theta - 1 = 2/G
static const i64 GAMD = 4 * DG;           // gamma = 4/G
static const i64 THD = DEN / 2 + DG;      // theta
static const i64 OMTD = DEN / 2 - DG;     // 1 - theta
// Li's Type I regions (Lemma 3.2; ShortSieveTypeI.TypeIReg): (3 theta - 1)/2 (less than (1 + theta)/5 for G > 26),
// (3 theta - 1)/4, (1 + theta)/2, (1 - theta)/2, (3 theta - 1)/8
static const i64 TI_N1 = DEN / 4 + 3 * DG / 2;
static const i64 TI_H2 = DEN / 8 + 3 * DG / 4;
static const i64 TI_S3 = 3 * DEN / 4 + DG / 2;
static const i64 TI_N3 = DEN / 4 - DG / 2;
static const i64 TI_H3 = DEN / 16 + 3 * DG / 8;
static_assert(GRID > 26 && DEN % (8 * GRID) == 0, "the grid keeps Li's constants exact");
// the Lean checker's slack E (|H| <= E, E = 1 in run) and a margin for it and the rounding of its domain-aware
// extremes: the generator's thresholds are Li's tightened by MRG, its witness faces likewise, and its domain is relaxed
// by E (the checker's 2 x_k <= S_k carries the slack)
static const i64 ESL = 1;
static const i64 MRG = 8;
static const i64 TIIM = 4096;            // margin of the Type II sums (units 1/SCF)
// the root cells (k/G, (k + 1)/G] x [j/G, (j + 1)/G): region C's, alpha1 in [nu0, 1/2), alpha2 in [nu0, 1/4), on the
// side branch = (alpha1 >= 2/5) and in the interval I_h = [theta - (2h + 1)/G, theta - (2h - 1)/G) of nu, and region
// A's, alpha1 in [1/4, 2/5), alpha2 in (1/5, 1/3)
static const int CK0 = 2, CK1 = (int)(G / 2), CJ0 = 2, CJ1 = (int)((G + 3) / 4);
static const int AK0 = (int)(G / 4), AK1 = (int)((2 * G + 4) / 5), AJ0 = (int)(G / 5), AJ1 = (int)((G + 2) / 3);
// and the Lean's cells outside region C, alpha1 in (1/4, 1/2], alpha2 in [1/5, 1/3)
static const int OK0 = (int)(G / 4), OK1 = (int)(G / 2), OJ0 = (int)(G / 5), OJ1 = (int)((G + 2) / 3);
static inline int rootBranch(int k) { return 5 * k >= 2 * G ? 1 : 0; }
// h = 0 on the first cell k = 2, where the level is held at 2 theta - 1 = nu0, the domain's lower end (the Lean's
// ShortSieveRoot.nuH: Li's level exceeds alpha just above nu0 when G/4 is an integer)
static inline int rootH(int k) { return k == 2 ? 0 : (int)((G / 2 + 1 - k) / 2); }
static const int MAXD = 8;
static const i64 SC = 1LL << 50;         // fixed point of the cell bounds (units 1/SC)
static const i64 SCF = 1LL << 40;        // fixed point of the Hoelder sums
static const i64 SCW = 1LL << 40;        // fixed point of the omega* table
extern i64 KQ;                           // kappa * DEN

struct Box {
    int n;
    i64 lo[MAXD], hi[MAXD];
};

// a linear form: value (c0 + sum c[j] x[j]) / DEN
struct LF {
    i64 c0 = 0;
    int c[MAXD] = {0, 0, 0, 0, 0, 0, 0, 0};
};
inline LF lfT(int j) { LF L; L.c[j] = 1; return L; }
inline LF lfK(i64 v) { LF L; L.c0 = v; return L; }
inline LF operator+(LF a, const LF& b) { a.c0 += b.c0; for (int j = 0; j < MAXD; ++j) a.c[j] += b.c[j]; return a; }
inline LF operator-(LF a, const LF& b) { a.c0 -= b.c0; for (int j = 0; j < MAXD; ++j) a.c[j] -= b.c[j]; return a; }
inline LF operator*(int k, LF a) { a.c0 *= k; for (int j = 0; j < MAXD; ++j) a.c[j] *= k; return a; }
inline LF lfS(int k) { LF L = lfK(DEN); for (int j = 0; j < k; ++j) L.c[j] = -1; return L; }   // 1 - x0 - ... - x_{k-1}

extern thread_local long long WK_LF;   // kernel work counter: linear form evaluations
inline i64 lfmin(const LF& L, const Box& B) {
    ++WK_LF;
    i64 v = L.c0;
    for (int j = 0; j < B.n; ++j) v += L.c[j] > 0 ? L.c[j] * B.lo[j] : L.c[j] * B.hi[j];
    return v;
}
inline i64 lfmax(const LF& L, const Box& B) {
    ++WK_LF;
    i64 v = L.c0;
    for (int j = 0; j < B.n; ++j) v += L.c[j] > 0 ? L.c[j] * B.hi[j] : L.c[j] * B.lo[j];
    return v;
}
// ---- domain-aware extremes: min of L over box ∩ {g_i < 0} for the straddling (active) diagonal constraints g_i of
// the node's domain, bounded below by min over the box of L + sum mu_i g_i / 6 (mu_i >= 0 integers, Lagrange
// duality: on the domain each g_i <= 0). The multipliers are chosen deterministically (one pass of coordinate ascent
// over the constraints, candidates at the breakpoints where a coefficient changes sign), so the kernel recomputes them.
struct Act { int n = 0; LF g[16]; };
extern thread_local const Act* CUR_ACT;
extern thread_local long long WK_LFA, WK_LFS;
inline i64 lfminScaled(const i64* c, i64 c0, const Box& B) {
    ++WK_LFS;
    i64 v = c0;
    for (int j = 0; j < B.n; ++j) v += c[j] > 0 ? c[j] * B.lo[j] : c[j] * B.hi[j];
    return v;
}
inline i64 fdiv6(i64 a) { return a >= 0 ? a / 6 : -((-a + 5) / 6); }
inline i64 lfminA(const LF& L, const Box& B) {
    const Act* A = CUR_ACT;
    if (!A || A->n == 0) return lfmin(L, B);
    ++WK_LFA;
    i64 c[MAXD], c0 = 6 * L.c0;
    for (int j = 0; j < B.n; ++j) c[j] = 6 * (i64)L.c[j];
    i64 best = lfminScaled(c, c0, B);
    for (int i = 0; i < A->n; ++i) {
        const LF& g = A->g[i];
        i64 bmu = 0;
        for (int j = 0; j < B.n; ++j) {
            if (!g.c[j]) continue;
            i64 q = -c[j] / g.c[j];                      // the multiplier that cancels coefficient j (and its neighbours)
            for (i64 mu = std::max<i64>(0, q - 1); mu <= q + 1; ++mu) {
                if (mu <= 0) continue;
                i64 cc[MAXD];
                for (int k = 0; k < B.n; ++k) cc[k] = c[k] + mu * g.c[k];
                i64 v = lfminScaled(cc, c0 + mu * g.c0, B);
                if (v > best) { best = v; bmu = mu; }
            }
        }
        if (bmu) { for (int k = 0; k < B.n; ++k) c[k] += bmu * g.c[k]; c0 += bmu * g.c0; }
    }
    return fdiv6(best);
}
inline i64 lfmaxA(const LF& L, const Box& B) {
    LF M; M.c0 = -L.c0;
    for (int j = 0; j < MAXD; ++j) M.c[j] = -L.c[j];
    return -lfminA(M, B);
}
inline double lfval(const LF& L, const double* x) {
    double v = L.c0;
    for (int j = 0; j < MAXD; ++j) v += L.c[j] * x[j];
    return v / DEN;
}

// a >= 0, b > 0; saturates at 2^62 (a saturated value exceeds every budget, so saturation keeps the bounds sound;
// the verifier also rejects a dropped box whose bound reaches 2^62)
extern thread_local bool SAT_FLAG;      // set by any saturation; dropCost then returns the cap 2^62 (rejected)
inline i64 cdiv128(i128 a, i128 b) {
    i128 q = (a + b - 1) / b;
    if (q >= ((i128)1 << 62)) { SAT_FLAG = true; return (i64)1 << 62; }
    return (i64)q;
}

// ---- omega* on a box: u = N / x_k, N a linear form; the table OMT (omtable.py) -------------------------------------
// min and max of u over the box as rationals P/Q (Q > 0)
inline void uRange(const LF& N, int k, const Box& B, i128& Plo, i128& Qlo, i128& Phi, i128& Qhi) {
    LF Np = N; int ck = Np.c[k]; Np.c[k] = 0;          // u = N'/x_k + c_k
    i64 nmin = lfmin(Np, B), nmax = lfmax(Np, B);
    i64 qlo = nmin >= 0 ? B.hi[k] : B.lo[k];
    i64 qhi = nmax >= 0 ? B.lo[k] : B.hi[k];
    Plo = (i128)nmin + (i128)ck * qlo; Qlo = qlo;
    Phi = (i128)nmax + (i128)ck * qhi; Qhi = qhi;
}
// table index of u = P/Q >= 1: floor(512 (u - 1)), clamped to 1024 (= above 3)
inline int uIndex(i128 P, i128 Q) {
    if (P < Q) return -1;
    i128 i = (512 * (P - Q)) / Q;
    return i > 1024 ? 1024 : (int)i;
}
extern thread_local long long WK_OM;
// upper bound for omega* on the range of u over the box, units 2^-40
inline i64 omegaBox(const LF& N, int k, const Box& B) {
    ++WK_OM;
    i128 Plo, Qlo, Phi, Qhi;
    uRange(N, k, B, Plo, Qlo, Phi, Qhi);
    if (Phi < Qhi) return 0;                             // u < 1 on the whole box: omega = 0
    int ia = uIndex(Plo, Qlo), ib = uIndex(Phi, Qhi);
    if (ia < 0) ia = 0;
    if (ia >= 1024) return OMT_TOP;                      // u >= 3
    i64 m = 0;
    int top = ib >= 1024 ? 1023 : ib;
    for (int i = ia; i <= top; ++i) m = std::max(m, (i64)OMT[i]);
    if (ib >= 1024) m = std::max(m, OMT_TOP);
    return m;
}

// ---- the weights' integrals over [x, x + w] (x, w in units 1/DEN), units 1/SC, rounded up -------------------------
inline i64 trapF(i64 x, i64 w) { return cdiv128((i128)SC * w * (2 * x + w), (i128)2 * x * (x + w)); }  // int dt/t
inline i64 lastF(i64 x, i64 w) { return cdiv128((i128)SC * DEN * w, (i128)x * (x + w)); }              // int dt/t^2
inline i64 linF(i64 w) { return cdiv128((i128)SC * w, (i128)DEN); }                                  // int dt
inline i64 mulSC(i64 a, i64 b) { return cdiv128((i128)a * b, (i128)SC); }
