#include "wit.h"
#include <functional>
#include <climits>

TIIOpt TIIO;
bool USE_G2 = true, USE_TII = true;
thread_local Work WK;
thread_local long long WK_LF = 0, WK_OM = 0, WK_LFA = 0, WK_LFS = 0;
thread_local bool SAT_FLAG = false;
thread_local const Act* CUR_ACT = nullptr;
i64 KQ = DEN >> 20;                      // kappa = 2^-20

Con regionConOf(const RootCtx& rc) {
    LF L = rc.branch % 2 == 0 ? 3 * lfT(1) + lfT(0) - lfK(DEN) : 2 * lfT(1) - lfT(0);
    return {L, rc.branch < 2};
}

bool regionOutside(const Box& B, const RootCtx& rc) {
    Con c = regionConOf(rc);             // region C: alpha2 < (1 - alpha1)/3 below 2/5, alpha2 < alpha1/2 above
    if (c.lt ? lfmin(c.L, B) >= 0 : lfmax(c.L, B) < 0) return true;
    // below nu(alpha1) = min(2 (theta - alpha1)/(2h - 1), gamma) on I_h: alpha2 < nu everywhere
    if (rc.h > 0 && B.hi[1] < GAMD && lfmax((2 * rc.h - 1) * lfT(1) + 2 * lfT(0), B) < 2 * THD) return true;
    return false;
}

bool outside(NT t, const Box& B, const RootCtx& rc) {
    ++WK.out;
    for (auto& c : ND[t].dom) {
        if (c.lt ? lfmin(c.L, B) >= 0 : lfmax(c.L, B) < 0) return true;
    }
    if (t != NA2 && regionOutside(B, rc)) return true;
    return false;
}

static LF sumItems(const std::vector<Item>& it, int mask) {
    LF s;
    for (int j = 0; j < (int)it.size(); ++j) if (mask >> j & 1) s = s + it[j].a;
    return s;
}

bool checkG2(const std::vector<Item>& it, const Box& B, int M, int R) {
    ++WK.g2;
    int all = (1 << it.size()) - 1;
    if (!M || !R || (M & R) || ((M | R) == all) || ((M | R) & ~all)) return false;
    LF lr = sumItems(it, R), l2 = 2 * sumItems(it, M) + lr;
    return lfmaxA(lr, B) < GAMD - MRG && lfmaxA(l2, B) < 2 * THD - MRG && lfminA(l2, B) > 2 * OMTD + MRG;
}

// generator-only filter: points of the region; a linear form's value at such a point bounds its extremes over the
// region (min <= value <= max), so a search can skip candidates that already fail at a point
thread_local Box FILT_P[4];
thread_local int FILT_N = 0;
static inline i64 fpMax(const LF& L) { i64 m = LLONG_MIN; for (int q = 0; q < FILT_N; ++q) m = std::max(m, lfmin(L, FILT_P[q])); return m; }
static inline i64 fpMin(const LF& L) { i64 m = LLONG_MAX; for (int q = 0; q < FILT_N; ++q) m = std::min(m, lfmin(L, FILT_P[q])); return m; }
bool searchG2(const std::vector<Item>& it, const Box& B, int& Mo, int& Ro) {
    int k = it.size(), all = (1 << k) - 1;
    for (int R = 1; R < all; ++R) {
        LF lr = sumItems(it, R);
        if (FILT_N && fpMax(lr) >= GAMD - MRG) continue;
        if (lfmaxA(lr, B) >= GAMD - MRG) continue;
        int comp = all & ~R, low = comp & -comp;
        for (int M = comp; M; M = (M - 1) & comp) {
            if (!(M & low) || M == comp) continue;
            LF l2 = 2 * sumItems(it, M) + lr;
            if (FILT_N && (fpMax(l2) >= 2 * THD - MRG || fpMin(l2) <= 2 * OMTD + MRG)) continue;
            if (lfmaxA(l2, B) < 2 * THD - MRG && lfminA(l2, B) > 2 * OMTD + MRG) { Mo = M; Ro = R; return true; }
        }
    }
    return false;
}

// floor(SCF * f) with f = 1/delta_req(D), D = (1 - theta + kappa)/(a - kappa), a = A/DEN
i64 fexact(i64 A) {
    if (A <= KQ) return 0;
    i64 P = OMTD + KQ, Q = A - KQ;
    if (P <= Q) return SCF / 2;                         // D <= 1: delta = 2
    i64 m = (P - 1) / Q;                                // D in (m, m + 1]
    if ((i128)2 * P <= (i128)(2 * m + 1) * Q)           // D <= m + 1/2: delta = 4D - 2m (Huxley)
        return (i64)(((i128)SCF * Q) / ((i128)4 * P - (i128)2 * m * Q));
    return SCF / (2 * m + 2);                           // delta = 2m + 2 (mean value theorem)
}

bool groupAllowed(const std::vector<Item>& it, const Box& B, int S) {
    if (__builtin_popcount(S) > TIIO.maxGroup) return false;
    if (!TIIO.group && (S & (S - 1))) return false;
    if (!TIIO.roughFactor)
        for (int j = 0; j < (int)it.size(); ++j)
            if ((S >> j & 1) && it[j].rough && lfmax(it[j].a - 2 * lfT(it[j].sift), B) >= 0) return false;
    return true;
}

bool checkTII(const std::vector<Item>& it, const Box& B, uint64_t part) {
    ++WK.tii;
    int k = it.size();
    int mask[16] = {0};
    int ng = 0;
    for (int j = 0; j < k; ++j) {
        int g = (part >> (4 * j)) & 15;
        mask[g] |= 1 << j;
        ng = std::max(ng, g + 1);
    }
    i64 tot = 0;
    for (int g = 0; g < ng; ++g) {
        if (!mask[g]) return false;
        if (!groupAllowed(it, B, mask[g])) return false;
        ++WK.tiiGroups;
        tot += fexact(lfminA(sumItems(it, mask[g]), B) - MRG);
    }
    return tot > SCF + TIIM;
}

bool checkTIIlin(const std::vector<Item>& it, const Box& B, uint64_t part);
bool searchTIIlin(const std::vector<Item>& it, const Box& B, uint64_t& part);
static inline int fpiece(i64 A, i64& m);
static inline i64 fslope(i64 A, i64 m);
static i128 tanMin(const i128* coef, i128 k0, const Box& B);
bool searchTII(const std::vector<Item>& it, const Box& B, uint64_t& part) {
    int k = it.size(), all = (1 << k) - 1;
    static thread_local i64 F[512], best[512];
    static thread_local int arg[512];
    static thread_local LF L[512];
    L[0] = LF();
    if (FILT_N) {
        // at one point of the region, the best partition's value bounds every partition's plain or linearised value
        // on the region from above (the tangents lie below f): a point where it fails rules the region out
        for (int S = 1; S <= all; ++S) { int b = __builtin_ctz(S); L[S] = L[S & (S - 1)] + it[b].a; }
        for (int q = 0; q < FILT_N; ++q) {
            for (int S = 1; S <= all; ++S) F[S] = groupAllowed(it, B, S) ? fexact(lfmin(L[S], FILT_P[q])) : -(1LL << 60);
            best[0] = 0;
            for (int S = 1; S <= all; ++S) {
                int low = S & -S;
                i64 bv = -(1LL << 62);
                for (int T = S; T; T = (T - 1) & S) {
                    if (!(T & low)) continue;
                    i64 v = F[T] + best[S & ~T];
                    if (v > bv) bv = v;
                }
                best[S] = bv;
            }
            if (best[all] + 64 <= SCF) return false;
        }
    }
    for (int S = 1; S <= all; ++S) {
        int b = __builtin_ctz(S);
        L[S] = L[S & (S - 1)] + it[b].a;
        F[S] = groupAllowed(it, B, S) ? (lfminA(L[S], B) - MRG > KQ ? fexact(lfminA(L[S], B) - MRG) : -(1LL << 60)) : -(1LL << 60);
    }
    best[0] = 0;
    for (int S = 1; S <= all; ++S) {
        int low = S & -S;
        i64 bv = -(1LL << 62); int ba = 0;
        for (int T = S; T; T = (T - 1) & S) {
            if (!(T & low)) continue;
            i64 v = F[T] + best[S & ~T];
            if (v > bv) { bv = v; ba = T; }
        }
        best[S] = bv; arg[S] = ba;
    }
    part = 0;
    int S = all, g = 0;
    while (S) {
        int T = arg[S];
        for (int j = 0; j < k; ++j) if (T >> j & 1) part |= (uint64_t)g << (4 * j);
        S &= ~T; ++g;
    }
    if (best[all] > SCF + TIIM) return true;
    if (best[all] < SCF - SCF / 6) return false;          // too far for the tangents to help
    bool point = true;
    for (int j = 0; j < B.n; ++j) if (B.lo[j] != B.hi[j]) { point = false; break; }
    if (point) return false;                              // on a point the tangents add nothing
    return searchTIIlin(it, B, part);
}

// all partitions with the linearised check: per subset its least and largest exponents, f at the least, the tangent
// slope (in one ramp) and its coefficient vector; a partition passes a cheap filter (the tangents' largest possible
// gain) before the exact least value of its combined tangent form on the box
long long TIILIN_TRIED = 0;
bool searchTIIlin(const std::vector<Item>& it, const Box& B, uint64_t& part) {
    int k = it.size(), all = (1 << k) - 1;
    static thread_local i64 Flo[512], gain[512];
    static thread_local i128 cf[512][MAXD + 1];
    static thread_local bool ok[512];
    LF L;
    for (int S = 1; S <= all; ++S) {
        L = sumItems(it, S);
        ok[S] = groupAllowed(it, B, S);
        if (!ok[S]) continue;
        i64 lo = lfminA(L, B) - MRG, hi = lfmaxA(L, B) + MRG;
        if (lo <= KQ) { ok[S] = false; continue; }
        Flo[S] = fexact(lo);
        i64 m1, m2;
        int p1 = fpiece(lo, m1), p2 = fpiece(hi, m2);
        i64 s = (p1 == 1 && p2 == 1 && m1 == m2) ? fslope(lo, m1) : 0;
        gain[S] = (i64)(((i128)s * (hi - lo)) / DEN) + 1;
        for (int j = 0; j < MAXD; ++j) cf[S][j] = (i128)s * L.c[j];
        cf[S][MAXD] = (i128)s * (L.c0 - lo);
    }
    // restricted growth strings
    int lab[16], gm[16];
    int ng = 0;
    std::function<bool(int)> rec = [&](int j) -> bool {
        if (j == k) {
            i64 tot = 0, up = 0;
            for (int g = 0; g < ng; ++g) { if (!ok[gm[g]]) return false; tot += Flo[gm[g]]; up += gain[gm[g]]; }
            if (tot + up <= SCF) return false;
            ++TIILIN_TRIED;
            i128 c[MAXD + 1] = {0, 0, 0, 0, 0, 0, 0, 0, 0};
            for (int g = 0; g < ng; ++g) for (int q = 0; q <= MAXD; ++q) c[q] += cf[gm[g]][q];
            i128 v = tanMin(c, c[MAXD], B);
            if (v < 0) v = 0;
            return tot + (i64)(v / DEN) > SCF + TIIM;
        }
        for (int g = 0; g <= ng && g < 15; ++g) {
            lab[j] = g;
            if (g == ng) { gm[ng++] = 1 << j; if (rec(j + 1)) return true; --ng; }
            else { gm[g] |= 1 << j; if (rec(j + 1)) return true; gm[g] &= ~(1 << j); }
        }
        return false;
    };
    if (!rec(0)) return false;
    part = 0;
    for (int j = 0; j < k; ++j) part |= (uint64_t)lab[j] << (4 * j);
    return checkTIIlin(it, B, part);
}

// ---- Type I ----
static bool kindOK(int kind, const LF& m, const LF& n, const LF& h, const Box& B) {
    switch (kind) {
        case 1: return 2 * lfmaxA(m, B) <= DEN - 2 * MRG && lfmaxA(n, B) < TI_N1 - MRG;
        case 2: return 2 * lfmaxA(m, B) <= DEN - 2 * MRG && lfmaxA(h, B) < TI_H2 - MRG && lfmaxA(2 * n + h, B) < THD - MRG &&
                       lfmaxA(2 * n + 3 * h, B) < TI_S3 - MRG;
        case 3: return 2 * lfmaxA(m, B) <= DEN - 2 * MRG && lfmaxA(n, B) < TI_N3 - MRG && lfmaxA(h, B) < TI_H3 - MRG;
    }
    return false;
}
bool checkTypeI(const TypeIReq& r, const Box& B, uint32_t code) {
    ++WK.tyI;
    int kind = code & 3;
    if (!(r.kinds >> kind & 1)) return false;
    LF g[3];
    for (int i = 0; i < (int)r.v.size(); ++i) {
        int role = (code >> (2 + 2 * i)) & 3;
        if (role > 2 || (kind == 1 && role == 2)) return false;
        g[role] = g[role] + r.v[i];
    }
    if (kind == 0) return 2 * lfmaxA(g[0] + g[1] + g[2], B) <= DEN - 2 * MRG;
    return kindOK(kind, g[0], g[1], g[2], B);
}

// pruned enumeration of the roles (pruning is exact when every variable is >= 0 on the box)
static bool dfsI(const TypeIReq& r, const Box& B, int kind, int i, LF* g, uint32_t roles, uint32_t& out, bool prune) {
    int k = r.v.size();
    if (prune || i == k) {
        bool ok;
        switch (kind) {
            case 1: ok = 2 * lfmaxA(g[0], B) <= DEN - 2 * MRG && lfmaxA(g[1], B) < TI_N1 - MRG; break;
            case 2: ok = 2 * lfmaxA(g[0], B) <= DEN - 2 * MRG && lfmaxA(g[2], B) < TI_H2 - MRG &&
                         lfmaxA(2 * g[1] + g[2], B) < THD - MRG && lfmaxA(2 * g[1] + 3 * g[2], B) < TI_S3 - MRG;
                    break;
            default: ok = 2 * lfmaxA(g[0], B) <= DEN - 2 * MRG && lfmaxA(g[1], B) < TI_N3 - MRG && lfmaxA(g[2], B) < TI_H3 - MRG;
        }
        if (!ok) return false;
        if (i == k) { out = (uint32_t)kind | roles << 2; return true; }
    }
    int nr = kind == 1 ? 2 : 3;
    for (int role = 0; role < nr; ++role) {
        g[role] = g[role] + r.v[i];
        bool f = dfsI(r, B, kind, i + 1, g, roles | (uint32_t)role << (2 * i), out, prune);
        g[role] = g[role] - r.v[i];
        if (f) return true;
    }
    return false;
}
bool searchTypeI(const TypeIReq& r, const Box& B, uint32_t& code) {
    LF tot;
    bool prune = true;
    for (auto& v : r.v) { tot = tot + v; if (lfmin(v, B) < 0) prune = false; }
    if (FILT_N) {
        // a code that holds on the region holds at each of its points: a point where none holds rules the region out
        const Act* save = CUR_ACT; CUR_ACT = nullptr;
        int saveN = FILT_N; FILT_N = 0;
        bool okp = true;
        for (int q = 0; q < saveN && okp; ++q) { uint32_t c2; Box P = FILT_P[q]; okp = searchTypeI(r, P, c2); }
        FILT_N = saveN; CUR_ACT = save;
        if (!okp) return false;
    }
    if ((r.kinds & 1) && 2 * lfmaxA(tot, B) <= DEN - 2 * MRG) { code = 0; return true; }
    for (int kind = 1; kind <= 3; ++kind) {
        if (!(r.kinds >> kind & 1)) continue;
        LF g[3];
        if (dfsI(r, B, kind, 0, g, 0, code, prune)) return true;
    }
    return false;
}

// the ordering links of a node type: domain constraints x_b < x_a (consecutive primes of one chain)
static int LINKA[NT_COUNT][8], LINKB[NT_COUNT][8], NLINK[NT_COUNT];
struct ChainInfo { int n; int c[MAXD]; };
static ChainInfo CHAINS[NT_COUNT][MAXD];
static int NCH[NT_COUNT];
static bool linksInit = false;
static void initLinks() {
    for (int t = 0; t < NT_COUNT; ++t) {
        NLINK[t] = 0;
        for (auto& c : ND[t].dom) {
            if (!c.lt || c.L.c0 != 0) continue;
            int a = -1, b = -1, nz = 0;
            for (int j = 0; j < MAXD; ++j) {
                if (!c.L.c[j]) continue;
                ++nz;
                if (c.L.c[j] == 1) b = j; else if (c.L.c[j] == -1) a = j;
            }
            if (nz == 2 && a >= 0 && b >= 0 && NLINK[t] < 8) { LINKA[t][NLINK[t]] = a; LINKB[t][NLINK[t]] = b; ++NLINK[t]; }
        }
        // the links must form paths (each coordinate at most once above and once below), so that a run of r linked
        // coordinates with one range is totally ordered and fills exactly 1/r! of its cube
        int up[MAXD] = {0}, down[MAXD] = {0};
        for (int l = 0; l < NLINK[t]; ++l) { ++down[LINKA[t][l]]; ++up[LINKB[t][l]]; }
        for (int j = 0; j < MAXD; ++j)
            if (up[j] > 1 || down[j] > 1) { fprintf(stderr, "links of %s are not paths\n", ND[t].name.c_str()); exit(1); }
        // the chains: maximal paths of links, from the largest coordinate down (singletons included)
        int nxt[MAXD];
        for (int j = 0; j < MAXD; ++j) nxt[j] = -1;
        for (int l = 0; l < NLINK[t]; ++l) nxt[LINKA[t][l]] = LINKB[t][l];
        NCH[t] = 0;
        for (int j = 0; j < ND[t].dim; ++j) {
            if (up[j]) continue;
            ChainInfo& c = CHAINS[t][NCH[t]++];
            c.n = 0;
            for (int q = j; q >= 0; q = nxt[q]) c.c[c.n++] = q;
        }
        int cov = 0;
        for (int i = 0; i < NCH[t]; ++i) cov += CHAINS[t][i].n;
        if (cov != ND[t].dim) { fprintf(stderr, "chains of %s do not cover the coordinates\n", ND[t].name.c_str()); exit(1); }
    }
    linksInit = true;
}
bool ORDERBOUND = true;
int CHAINBOUND = 1;          // 1: the chain bound (ordered runs with virtual splits at every range end); 0: the old one
int CHAINREF = 1;            // each elementary interval of a chain is cut into this many equal parts (virtual splits)
long long WK_ORD = 0;
thread_local long long WK_CHAINOPS = 0;
// F_j over [x, x + w): the integral of the coordinate's weight (0: dt, 1: dt/t, 2: dt/t^2), units 1/SC, rounded up
static inline i64 Fw(int wt, i64 x, i64 w) { return wt == 0 ? linF(w) : wt == 1 ? trapF(x, w) : lastF(x, w); }
static const i64 FACT[9] = {1, 1, 2, 6, 24, 120, 720, 5040, 40320};
// the bound of an ordered run: chain coordinates cs[0] > cs[1] > ... > cs[r-1] (strictly decreasing primes) all in
// [e, e + w). For r >= 2 and no weight-0 coordinate: every weight is converted to 1/p (1/(p log p) <= (DEN/e) / (p
// log x)), then sum over decreasing r-tuples of prod 1/p <= (sum 1/p)^r / r!; the plain product is also a bound.
static i64 runBound(const NodeDef& d, const int* cs, int r, i64 e, i64 w) {
    i64 prod = SC;
    bool any0 = false;
    int n2 = 0;
    for (int q = 0; q < r; ++q) {
        int wt = d.wt[cs[q]];
        prod = mulSC(prod, Fw(wt, e, w));
        if (wt == 0) any0 = true;
        if (wt == 2) ++n2;
    }
    if (r == 1 || any0) return prod;
    i64 T = trapF(e, w);
    // the ordered bound, computed in i128; a value beyond 2^62 is treated as infinite (the product bound is kept)
    const i128 BIG = (i128)1 << 62;
    i128 ord = SC;
    bool inf = false;
    for (int q = 0; q < r && !inf; ++q) { ord = ((i128)ord * T + SC - 1) / SC; if (ord > BIG) inf = true; }
    for (int q = 0; q < n2 && !inf; ++q) { ord = (ord * DEN + e - 1) / e; if (ord > BIG) inf = true; }
    if (inf) return prod;
    ord = (ord + FACT[r] - 1) / FACT[r];
    return ord < (i128)prod ? (i64)ord : prod;
}
// the bound of a chain c_0 > c_1 > ... > c_{m-1} of linked coordinates over the box: the breakpoints are every range
// end (and CHAINREF - 1 equal cuts of each elementary interval); every point of box ∩ {chain order} assigns each
// coordinate to one elementary interval, with nonincreasing intervals along the chain, and the coordinates sharing an
// interval form a run (a contiguous part of the chain). The sum over the assignments of the products of the runs'
// bounds is computed by a DP along the chain.
static i64 chainBound(const NodeDef& d, const ChainInfo& ch, const Box& B) {
    int m = ch.n;
    if (m == 1) { int j = ch.c[0]; return Fw(d.wt[j], B.lo[j], B.hi[j] - B.lo[j]); }
    i64 bp0[2 * MAXD];
    int K0 = 0;
    for (int i = 0; i < m; ++i) { bp0[K0++] = B.lo[ch.c[i]]; bp0[K0++] = B.hi[ch.c[i]]; }
    std::sort(bp0, bp0 + K0);
    K0 = std::unique(bp0, bp0 + K0) - bp0;
    static thread_local std::vector<i64> bp;
    bp.clear();
    for (int k = 0; k + 1 < K0; ++k) {
        i64 a = bp0[k], b = bp0[k + 1];
        int ref = CHAINREF;
        for (int q = 0; q < ref; ++q) {
            i64 x = a + (b - a) * q / ref;
            if (bp.empty() || x > bp.back()) bp.push_back(x);
        }
    }
    bp.push_back(bp0[K0 - 1]);
    int K = (int)bp.size() - 1;                  // elementary intervals [bp[k], bp[k + 1])
    // allowed[i][k]: interval k lies in coordinate c_i's range
    static thread_local std::vector<uint8_t> al;
    static thread_local std::vector<i128> A, P;
    al.assign((size_t)m * K, 0);
    for (int i = 0; i < m; ++i) {
        int j = ch.c[i];
        for (int k = 0; k < K; ++k) al[(size_t)i * K + k] = B.lo[j] <= bp[k] && bp[k + 1] <= B.hi[j];
    }
    // P[i][k] = sum_{k' < k} A[i][k'] for i < m; the tail beyond the chain counts 1 (SC)
    P.assign((size_t)(m + 1) * (K + 1), 0);
    A.assign((size_t)m * K, 0);
    for (int k = 0; k <= K; ++k) P[(size_t)m * (K + 1) + k] = SC;
    const i128 CAP = (i128)1 << 62;    // a capped value fails the budget (> 4096), so capping keeps soundness
    for (int i = m - 1; i >= 0; --i) {
        for (int k = 0; k < K; ++k) {
            i128 s = 0;
            for (int r = 1; i + r <= m; ++r) {
                if (!al[(size_t)(i + r - 1) * K + k]) break;
                ++WK_CHAINOPS;
                i128 tail = i + r == m ? (i128)SC : P[(size_t)(i + r) * (K + 1) + k];
                if (tail == 0) continue;
                i64 R = runBound(d, ch.c + i, r, bp[k], bp[k + 1] - bp[k]);
                s += (R * tail + SC - 1) / SC;
                if (s > CAP) { s = CAP; SAT_FLAG = true; }
            }
            A[(size_t)i * K + k] = s;
        }
        i128 acc = 0;
        for (int k = 0; k < K; ++k) { P[(size_t)i * (K + 1) + k] = acc; acc += A[(size_t)i * K + k]; if (acc > CAP) { acc = CAP; SAT_FLAG = true; } }
        P[(size_t)i * (K + 1) + K] = acc;
    }
    i128 tot = P[(size_t)0 * (K + 1) + K];
    if (tot >= ((i128)1 << 62)) { SAT_FLAG = true; return (i64)1 << 62; }
    return (i64)tot;
}
static i64 dropCostOld(NT t, const Box& B);
static i64 dropCostImpl(NT t, const Box& B);
i64 dropCost(NT t, const Box& B) {
    bool save = SAT_FLAG;
    SAT_FLAG = false;
    i64 v = CHAINBOUND ? dropCostImpl(t, B) : dropCostOld(t, B);
    if (SAT_FLAG) v = (i64)1 << 62;                    // any saturation: the cap (fails every budget; rejected)
    SAT_FLAG = save || SAT_FLAG;
    return v;
}
static i64 dropCostImpl(NT t, const Box& B) {
    ++WK.bound;
    if (!linksInit) initLinks();
    const NodeDef& d = ND[t];
    i64 acc;
    if (d.om.size() == 1) acc = omegaBox(d.om[0].N, d.om[0].k, B) << 10;
    else {
        i64 a = omegaBox(d.om[0].N, d.om[0].k, B);
        if (!a) return 0;
        i64 b = omegaBox(d.om[1].N, d.om[1].k, B);
        acc = cdiv128((i128)a * b, (i128)1 << 30);
    }
    if (!acc) return 0;
    for (int c = 0; c < NCH[t]; ++c) {
        i64 f = chainBound(d, CHAINS[t][c], B);
        if (!f) return 0;
        acc = mulSC(acc, f);
    }
    return acc;
}
// the bound of a dropped box: omega* times the weights' integrals; for a run of r chained coordinates with identical
// ranges (the domain orders them), the weights' maxima times the ordered simplex's volume w^r / r! when smaller
static i64 dropCostOld(NT t, const Box& B) {
    ++WK.bound;
    if (!linksInit) initLinks();
    const NodeDef& d = ND[t];
    i64 acc;
    if (d.om.size() == 1) acc = omegaBox(d.om[0].N, d.om[0].k, B) << 10;
    else {
        i64 a = omegaBox(d.om[0].N, d.om[0].k, B);
        if (!a) return 0;
        i64 b = omegaBox(d.om[1].N, d.om[1].k, B);
        acc = cdiv128((i128)a * b, (i128)1 << 30);
    }
    if (!acc) return 0;
    // runs: components of the links between coordinates with identical ranges
    int comp[MAXD];
    for (int j = 0; j < d.dim; ++j) comp[j] = j;
    if (ORDERBOUND)
        for (int l = 0; l < NLINK[t]; ++l) {
            int a = LINKA[t][l], b = LINKB[t][l];
            if (a >= d.dim || b >= d.dim) continue;
            if (B.lo[a] == B.lo[b] && B.hi[a] == B.hi[b]) {
                int ca = comp[a], cb = comp[b];
                for (int j = 0; j < d.dim; ++j) if (comp[j] == cb) comp[j] = ca;
            }
        }
    for (int c = 0; c < d.dim; ++c) {
        int r = 0;
        for (int j = 0; j < d.dim; ++j) if (comp[j] == c) ++r;
        if (!r) continue;
        i64 fp = SC, fm = SC;        // the product of the integrals, the product of maxima x width
        for (int j = 0; j < d.dim; ++j) {
            if (comp[j] != c) continue;
            i64 w = B.hi[j] - B.lo[j], x = B.lo[j];
            i64 F = d.wt[j] == 0 ? linF(w) : d.wt[j] == 1 ? trapF(x, w) : lastF(x, w);
            fp = mulSC(fp, F);
            if (r > 1) {
                i64 G = d.wt[j] == 0 ? linF(w) : d.wt[j] == 1 ? cdiv128((i128)SC * w, (i128)x)
                                                             : cdiv128((i128)SC * DEN * w, (i128)x * x);
                fm = mulSC(fm, G);
            }
        }
        if (r > 1) {
            i64 fact = 1;
            for (int q = 2; q <= r; ++q) fact *= q;
            fm = (fm + fact - 1) / fact;
            if (fm < fp) { fp = fm; ++WK_ORD; }
        }
        acc = mulSC(acc, fp);
    }
    return acc;
}

i64 childUpper(NT child, const Box& B) {
    int j = ND[child].dim - 1;
    i64 U = DEN;
    for (auto& c : ND[child].dom) {
        if (!c.lt || c.L.c[j] <= 0) continue;
        bool deeper = false;
        for (int q = j + 1; q < MAXD; ++q) if (c.L.c[q]) deeper = true;
        if (deeper) continue;
        LF rest = c.L; int cj = rest.c[j]; rest.c[j] = 0;
        i64 num = -lfmin(rest, B);                      // x_j < num / cj
        if (num <= 0) return 0;
        U = std::min(U, (num + cj - 1) / cj);
    }
    return U;
}

static inline i64 fdiv(i64 a, i64 b) { i64 q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) --q; return q; }  // b > 0
static inline i64 cdivs(i64 a, i64 b) { return -fdiv(-a, b); }

static bool tightenOne(const LF& L, bool lt, Box& B) {
    // L < 0 (lt) or L >= 0 on the domain; restrict each coordinate
    for (int j = 0; j < B.n; ++j) {
        int cj = L.c[j];
        if (!cj) continue;
        i64 rmin = L.c0, rmax = L.c0;
        for (int i = 0; i < B.n; ++i) {
            if (i == j || !L.c[i]) continue;
            i64 a = L.c[i] * B.lo[i], b = L.c[i] * B.hi[i];
            rmin += std::min(a, b); rmax += std::max(a, b);
        }
        if (lt) {
            if (cj > 0) B.hi[j] = std::min(B.hi[j], cdivs(-rmin, cj));        // x_j < -rest/cj <= -rmin/cj
            else B.lo[j] = std::max(B.lo[j], fdiv(rmin, -cj));                // x_j > rest/|cj| >= rmin/|cj|
        } else {
            if (cj > 0) B.lo[j] = std::max(B.lo[j], fdiv(-rmax, cj));        // x_j >= -rest/cj >= -rmax/cj
            else B.hi[j] = std::min(B.hi[j], fdiv(rmax, -cj) + 1);            // x_j <= rest/|cj| <= rmax/|cj|
        }
        if (B.lo[j] >= B.hi[j]) return false;
    }
    return true;
}
bool tighten(NT t, Box& B, const RootCtx& rc) {
    for (int it = 0; it < 2; ++it) {
        for (auto& c : ND[t].dom) if (!tightenOne(c.L, c.lt, B)) return false;
        if (t != NA2) {
            Con c = regionConOf(rc);
            if (!tightenOne(c.L, c.lt, B)) return false;
        }
    }
    return true;
}

// ---- the linearised Hoelder check ----
// f is increasing, constant on its plateaus (D in (m + 1/2, m + 1], and D <= 1) and convex on its ramps (D in
// (m, m + 1/2]). For a group whose least and largest exponents on the box lie in one ramp, the tangent at the least one
// is a lower bound for f on the box: f(a) >= f(lo) + f'(lo)(a - lo); on one plateau the slope 0 is exact; otherwise 0.
// Summing these lower bounds gives a linear form in x whose least value on the box (at a vertex) keeps the
// cancellations between groups (a prime and the rough factor that contains it with the opposite sign).
static inline int fpiece(i64 A, i64& m) {     // 0: D <= 1; 1: ramp m; 2: plateau m (D in (m + 1/2, m + 1])
    if (A <= KQ) { m = -1; return -1; }
    i64 P = OMTD + KQ, Q = A - KQ;
    if (P <= Q) { m = 0; return 0; }
    m = (P - 1) / Q;
    return (i128)2 * P <= (i128)(2 * m + 1) * Q ? 1 : 2;
}
// slope of SCF * f per unit of A / DEN... returned as floor(SCF * DEN * f'(a)) / DEN per unit of A: we return
// floor(SCF * 4 P DEN / (4P - 2mQ)^2), the derivative of SCF*f with respect to a = A/DEN
static inline i64 fslope(i64 A, i64 m) {
    i64 P = OMTD + KQ, Q = A - KQ;
    i128 den = (i128)4 * P - (i128)2 * m * Q;
    // SCF * 4 P * DEN / den^2, computed as (SCF * 4P / den) * DEN / den, rounded down at each step
    i128 a = ((i128)SCF * 4 * P) / den;
    return (i64)((a * DEN) / den);
}
// the least value of the combined tangent (i128 coefficients) on the box, or with TANDOM on the box and the active
// constraints: lfminA's multipliers, with the Lean's Euclidean division for the candidates (its LF.minD)
bool TANDOM = false;
static inline i128 ediv128(i128 a, i128 b) { i128 q = a / b, r = a % b; if (r < 0) q += b > 0 ? -1 : 1; return q; }
static inline i128 minScaled128(const i128* c, i128 c0, const Box& B) {
    i128 v = c0;
    for (int j = 0; j < B.n; ++j) v += c[j] > 0 ? c[j] * B.lo[j] : c[j] * B.hi[j];
    return v;
}
static i128 tanMin(const i128* coef, i128 k0, const Box& B) {
    i128 c[MAXD], c0 = 6 * k0;
    for (int j = 0; j < B.n; ++j) c[j] = 6 * coef[j];
    i128 best = minScaled128(c, c0, B);
    const Act* A = TANDOM ? CUR_ACT : nullptr;
    if (A) for (int i = 0; i < A->n; ++i) {
        const LF& g = A->g[i];
        i128 bmu = 0;
        for (int j = 0; j < B.n; ++j) {
            if (!g.c[j]) continue;
            i128 q = ediv128(-c[j], g.c[j]);
            for (i128 mu = q - 1; mu <= q + 1; ++mu) {
                if (mu <= 0) continue;
                i128 cc[MAXD];
                for (int k = 0; k < B.n; ++k) cc[k] = c[k] + mu * g.c[k];
                i128 v = minScaled128(cc, c0 + mu * g.c0, B);
                if (v > best) { best = v; bmu = mu; }
            }
        }
        if (bmu) { for (int k = 0; k < B.n; ++k) c[k] += bmu * g.c[k]; c0 += bmu * g.c0; }
    }
    return best >= 0 ? best / 6 : -((-best + 5) / 6);
}
long long WK_TIILIN = 0;
bool checkTIIlin(const std::vector<Item>& it, const Box& B, uint64_t part) {
    ++WK.tii;
    int k = it.size();
    int mask[16] = {0};
    int ng = 0;
    for (int j = 0; j < k; ++j) {
        int g = (part >> (4 * j)) & 15;
        mask[g] |= 1 << j;
        ng = std::max(ng, g + 1);
    }
    i64 tot = 0;
    i128 coef[MAXD] = {0, 0, 0, 0, 0, 0, 0, 0};
    i128 c0 = 0;
    for (int g = 0; g < ng; ++g) {
        if (!mask[g]) return false;
        if (!groupAllowed(it, B, mask[g])) return false;
        ++WK.tiiGroups;
        LF L = sumItems(it, mask[g]);
        i64 lo = lfminA(L, B) - MRG, hi = lfmaxA(L, B) + MRG;
        tot += fexact(lo);
        i64 m1, m2;
        int p1 = fpiece(lo, m1), p2 = fpiece(hi, m2);
        if (p1 == 1 && p2 == 1 && m1 == m2) {
            i64 s = fslope(lo, m1);              // the tangent at lo, in SCF per unit of alpha
            // s * (L(x) - lo) / DEN, L(x) = (c0 + sum c_j x_j)
            for (int j = 0; j < B.n; ++j) coef[j] += (i128)s * L.c[j];
            c0 += (i128)s * (L.c0 - lo);
        }
    }
    if (tot > SCF + TIIM) return true;
    i128 v = tanMin(coef, c0, B);
    if (v < 0) v = 0;                            // each tangent term is >= 0 on the box
    ++WK_TIILIN;
    return tot + (i64)(v / DEN) > SCF + TIIM;
}

// the active diagonal constraints of the node's domain on the box: neither true nor false on the whole box
void actives(NT t, const Box& B, const RootCtx& rc, Act& A) {
    A.n = 0;
    auto add = [&](const LF& g) {
        int nz = 0;
        for (int j = 0; j < B.n; ++j) if (g.c[j]) ++nz;
        if (nz < 2 || A.n >= 16) return;
        if (lfmax(g, B) < 0 || lfmin(g, B) >= 0) return;
        A.g[A.n++] = g;
    };
    for (auto& c : ND[t].dom) if (c.lt) add(c.L);
    if (t != NA2) {
        Con c = regionConOf(rc);                        // lt: L < 0 inside; ge: -L <= 0 inside
        LF g = c.L;
        if (!c.lt) { g.c0 = -g.c0; for (int j = 0; j < MAXD; ++j) g.c[j] = -g.c[j]; }
        add(g);
    }
}

// the linearised Hoelder value of a partition on the box (SCF units; the check passes when it exceeds SCF)
i64 tiiLinValue(const std::vector<Item>& it, const Box& B, uint64_t part) {
    int k = it.size();
    int mask[16] = {0};
    int ng = 0;
    for (int j = 0; j < k; ++j) { int g = (part >> (4 * j)) & 15; mask[g] |= 1 << j; ng = std::max(ng, g + 1); }
    i64 tot = 0;
    i128 coef[MAXD] = {0, 0, 0, 0, 0, 0, 0, 0};
    i128 c0 = 0;
    for (int g = 0; g < ng; ++g) {
        if (!mask[g] || !groupAllowed(it, B, mask[g])) return -(1LL << 60);
        LF L = sumItems(it, mask[g]);
        i64 lo = lfminA(L, B) - MRG, hi = lfmaxA(L, B) + MRG;
        tot += fexact(lo);
        i64 m1, m2;
        int p1 = fpiece(lo, m1), p2 = fpiece(hi, m2);
        if (p1 == 1 && p2 == 1 && m1 == m2) {
            i64 s = fslope(lo, m1);
            for (int j = 0; j < B.n; ++j) coef[j] += (i128)s * L.c[j];
            c0 += (i128)s * (L.c0 - lo);
        }
    }
    i128 v = tanMin(coef, c0, B);
    if (v < 0) v = 0;
    return tot + (i64)(v / DEN);
}

// ---- regions with cuts: box ∩ domain ∩ {cut half-spaces} (diagonal splits of the tree) ----
bool tightenC(NT t, Box& B, const RootCtx& rc, const Cuts& K) {
    for (int it = 0; it < 2; ++it) {
        for (auto& c : ND[t].dom) if (!tightenOne(c.L, c.lt, B)) return false;
        if (t != NA2) {
            Con c = regionConOf(rc);
            if (!tightenOne(c.L, c.lt, B)) return false;
        }
        for (int i = 0; i < K.n; ++i) if (!tightenOne(K.c[i].L, K.c[i].lt, B)) return false;
    }
    return true;
}
bool outsideC(NT t, const Box& B, const RootCtx& rc, const Cuts& K) {
    if (outside(t, B, rc)) return true;
    for (int i = 0; i < K.n; ++i) {
        const Con& c = K.c[i];
        if (c.lt ? lfmin(c.L, B) >= 0 : lfmax(c.L, B) < 0) return true;
    }
    return false;
}
void activesC(NT t, const Box& B, const RootCtx& rc, const Cuts& K, Act& A) {
    actives(t, B, rc, A);
    for (int i = 0; i < K.n && A.n < 16; ++i) {
        const Con& c = K.c[i];
        LF g = c.L;                                     // lt: g < 0 inside; ge: -L <= 0 inside
        if (!c.lt) { g.c0 = -g.c0; for (int j = 0; j < MAXD; ++j) g.c[j] = -g.c[j]; }
        int nz = 0;
        for (int j = 0; j < B.n; ++j) if (g.c[j]) ++nz;
        if (nz < 2) continue;
        if (lfmax(g, B) < 0 || lfmin(g, B) > 0) continue;
        A.g[A.n++] = g;
    }
}
// the bound of a dropped region by virtual splits: the box is cut into k1 equal parts along q1 (and each into k2 along
// q2); every part is tightened against the domain and the cuts (dropped when empty) and bounded by dropCost. The parts
// cover the box, each tightened part contains its part of the region, so the sum bounds the region.
thread_local long long WK_VSPARTS = 0;
i64 dropCostVS(NT t, const Box& B, const RootCtx& rc, const Cuts& K, int q1, int k1, int q2, int k2) {
    if (k1 <= 1 && k2 <= 1) return dropCost(t, B);
    if (k1 < 1) k1 = 1;
    if (k2 < 1) k2 = 1;
    i128 tot = 0;
    for (int i = 0; i < k1; ++i) {
        Box S = B;
        if (k1 > 1) {
            i64 w = B.hi[q1] - B.lo[q1];
            S.lo[q1] = B.lo[q1] + (i64)((i128)w * i / k1);
            S.hi[q1] = B.lo[q1] + (i64)((i128)w * (i + 1) / k1);
            if (S.lo[q1] >= S.hi[q1]) continue;
        }
        for (int j = 0; j < k2; ++j) {
            Box S2 = S;
            if (k2 > 1) {
                i64 w = S.hi[q2] - S.lo[q2];
                S2.lo[q2] = S.lo[q2] + (i64)((i128)w * j / k2);
                S2.hi[q2] = S.lo[q2] + (i64)((i128)w * (j + 1) / k2);
                if (S2.lo[q2] >= S2.hi[q2]) continue;
            }
            ++WK_VSPARTS;
            if (!tightenC(t, S2, rc, K)) continue;
            i64 c = dropCost(t, S2);
            if (c >= ((i64)1 << 62)) return (i64)1 << 62;
            tot += c;
        }
    }
    return tot >= ((i128)1 << 62) ? ((i64)1 << 62) : (i64)tot;
}

// ---- generator-only: fast searches at a point (scalar arithmetic on the items' values; same witnesses and codes) ----
bool searchG2Pt(const std::vector<Item>& it, const Box& P, int& Mo, int& Ro) {
    int k = it.size(), all = (1 << k) - 1;
    i64 v[16], sum[512];
    for (int j = 0; j < k; ++j) v[j] = lfmin(it[j].a, P);
    sum[0] = 0;
    for (int S = 1; S <= all; ++S) sum[S] = sum[S & (S - 1)] + v[__builtin_ctz(S)];
    for (int R = 1; R < all; ++R) {
        if (sum[R] >= GAMD - MRG) continue;
        int comp = all & ~R, low = comp & -comp;
        for (int M = comp; M; M = (M - 1) & comp) {
            if (!(M & low) || M == comp) continue;
            i64 l2 = 2 * sum[M] + sum[R];
            if (l2 < 2 * THD - MRG && l2 > 2 * OMTD + MRG) { Mo = M; Ro = R; return true; }
        }
    }
    return false;
}
bool searchTIIPt(const std::vector<Item>& it, const Box& P, uint64_t& part) {
    int k = it.size(), all = (1 << k) - 1;
    static thread_local i64 F[512], best[512], sum[512];
    static thread_local int arg[512];
    i64 v[16];
    for (int j = 0; j < k; ++j) v[j] = lfmin(it[j].a, P);
    sum[0] = 0;
    for (int S = 1; S <= all; ++S) {
        sum[S] = sum[S & (S - 1)] + v[__builtin_ctz(S)];
        F[S] = groupAllowed(it, P, S) ? fexact(sum[S]) : -(1LL << 60);
    }
    best[0] = 0;
    for (int S = 1; S <= all; ++S) {
        int low = S & -S;
        i64 bv = -(1LL << 62); int ba = 0;
        for (int T = S; T; T = (T - 1) & S) {
            if (!(T & low)) continue;
            i64 val = F[T] + best[S & ~T];
            if (val > bv) { bv = val; ba = T; }
        }
        best[S] = bv; arg[S] = ba;
    }
    if (best[all] <= SCF) return false;
    part = 0;
    int S = all, g = 0;
    while (S) {
        int T = arg[S];
        for (int j = 0; j < k; ++j) if (T >> j & 1) part |= (uint64_t)g << (4 * j);
        S &= ~T; ++g;
    }
    return true;
}
static bool kindOKs(int kind, i64 m, i64 n, i64 h) {
    switch (kind) {
        case 1: return 2 * m <= DEN - 2 * MRG && n < TI_N1 - MRG;
        case 2: return 2 * m <= DEN - 2 * MRG && h < TI_H2 - MRG && 2 * n + h < THD - MRG && 2 * n + 3 * h < TI_S3 - MRG;
        case 3: return 2 * m <= DEN - 2 * MRG && n < TI_N3 - MRG && h < TI_H3 - MRG;
    }
    return false;
}
static bool dfsIs(const i64* v, int k, int kind, int i, i64* g, uint32_t roles, uint32_t& out) {
    // every variable is >= 0 at an admissible point, so a failing partial assignment can be pruned
    if (!kindOKs(kind, g[0], g[1], g[2])) {
        bool nonneg = true;
        for (int q = i; q < k; ++q) if (v[q] < 0) nonneg = false;
        if (nonneg) return false;
    }
    if (i == k) { if (!kindOKs(kind, g[0], g[1], g[2])) return false; out = (uint32_t)kind | roles << 2; return true; }
    int nr = kind == 1 ? 2 : 3;
    for (int role = 0; role < nr; ++role) {
        g[role] += v[i];
        bool f = dfsIs(v, k, kind, i + 1, g, roles | (uint32_t)role << (2 * i), out);
        g[role] -= v[i];
        if (f) return true;
    }
    return false;
}
bool searchTypeIPt(const TypeIReq& r, const Box& P, uint32_t& code) {
    int k = r.v.size();
    i64 v[16], tot = 0;
    for (int i = 0; i < k; ++i) { v[i] = lfmin(r.v[i], P); tot += v[i]; }
    if ((r.kinds & 1) && 2 * tot <= DEN - 2 * MRG) { code = 0; return true; }
    for (int kind = 1; kind <= 3; ++kind) {
        if (!(r.kinds >> kind & 1)) continue;
        i64 g[3] = {0, 0, 0};
        if (dfsIs(v, k, kind, 0, g, 0, code)) return true;
    }
    return false;
}
// the cuts that still constrain the (tightened) box: a cut that holds on the whole box is implied there and below
Cuts pruneCuts(const Cuts& K, const Box& B) {
    Cuts R;
    for (int i = 0; i < K.n; ++i) {
        const Con& c = K.c[i];
        bool implied = c.lt ? lfmax(c.L, B) < 0 : lfmin(c.L, B) >= 0;
        if (!implied) R.c[R.n++] = c;
    }
    return R;
}
