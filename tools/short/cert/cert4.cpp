// The certificate prototype at theta = 13/25, version 3 (cert052b): regions box ∩ domain ∩ cut half-spaces (diagonal
// splits along the faces of the linear witnesses: Li's Type I sets and Lemma 4.1), drops bounded by virtual splits
// (each part tightened against the domain and the cuts, then the chain bound), alternatives compared at the decisions.
// The generator builds the tree; the verifier replays it with the exact checks only and sums the dropped bounds.
//   ./cert3 [key=value ...]
#include "wit.h"
#include <random>
#include <array>
#include <cstring>
#include <chrono>
#include <thread>
#include <atomic>
#include <cmath>
#include <mutex>
#include <map>

static const i64 INF = (i64)1 << 62;
static const uint8_t D_LSPLIT = 8;   // a diagonal split: children region ∩ {L < 0} and region ∩ {L >= 0}

struct TNode {
    uint8_t type, dec, sc, k1;   // node type, decision; axis split: coordinate; drop: virtual split q1, k1
    uint8_t q2, k2, pad0, pad1;  // drop: second virtual split
    i64 sp;                      // axis split position
    uint64_t w;                  // witness; diagonal split: index of the form in the tree's form table
};
struct Tree { std::vector<TNode> T; std::vector<LF> F; };

// ---------------- parameters ----------------
static int MAXLVL = 80;
static i64 MINW = DEN >> 24;
static int NSAMP = 4;
static double EPS_SLACK = 2e-8;
static double PEELMIN = 0.02, PEELMIN2 = 0.002;
static double PBF = 10;
static double LAMBDA = 5e-9;
static double ASYMFRAC = 0.3;
static int DIAG = 1;             // diagonal cuts along witness faces
static int DIAGTII = 1;          // ... including Type II group-threshold cuts
static int DIAGNZP = 2;          // + nodes: a diagonal cut may involve at most this many coordinates of positive width
static int DIAGNZM = 8;          // - nodes: likewise
static int MININ = 8;
static int COVSEL = 1;
static int PRUNE = 1;
static int ORTHANT = 1;
static int CORNERCUT = 0;        // sample the box corners also for regions with cuts          // Type II witnesses: orthant cuts (all groups' thresholds jointly)            // drop the cuts implied on a node's tightened box (generator and verifier alike)           // diagonal cuts: score witnesses by their coverage of the region's samples            // samples: draw until this many lie in the region (at most 6x the plain number)
static int MAXDIAG = 10;         // at most this many cuts on a path
static double DIAGPREF = 1.0;    // a diagonal cut's share is multiplied by this before comparing with axis peels
static int VSMAX = 16;           // virtual splits of a drop: at most this many parts per coordinate
static double VSW = 0.3;         // kernel cost of a virtual part, in nodes
static int ALTMINUS = 1;         // - nodes: compare decomposing now with cutting first
static double ALTMIN = 2e-6;     // ... when the child's drop bound exceeds this
static int TRACE = 0;
static double TRACEMIN = 1e-4;
static const char* TRACET = nullptr;
static long long TRACEMAX = 300;
static int USEFILT = 1;          // generator-only point filters in the box searches

// ---------------- witnesses at sample points ----------------
struct Wit { int kind; uint64_t w; int si = -1; };   // 0 OUT, 1 G2, 2 TII, 3 DEC0, 4 DEC1; si: a sample where it holds
struct Samp { std::array<i64, 8> x; int cls; Wit wit; double f; };   // cls 0 OUT, 1 ASYM, 2 DEC0, 3 DEC1, 4 none

static bool pointOutsideC(NT t, const Box& P, const RootCtx& rc, const Cuts& K) {
    for (auto& c : ND[t].dom) {
        i64 v = lfmin(c.L, P);
        if (c.lt ? v >= 0 : v < 0) return true;
    }
    if (t != NA2 && regionOutside(P, rc)) return true;
    for (int i = 0; i < K.n; ++i) {
        i64 v = lfmin(K.c[i].L, P);
        if (K.c[i].lt ? v >= 0 : v < 0) return true;
    }
    return false;
}
static bool checkDec(NT t, int c, const Box& B, uint64_t w) {
    const Child& ch = ND[t].ch[c];
    for (int r = 0; r < (int)ch.req.size(); ++r)
        if (!checkTypeI(ch.req[r], B, (uint32_t)(w >> (32 * r)))) return false;
    return true;
}
static bool searchDec(NT t, int c, const Box& B, uint64_t& w) {
    const Child& ch = ND[t].ch[c];
    w = 0;
    for (int r = 0; r < (int)ch.req.size(); ++r) {
        uint32_t code;
        if (!searchTypeI(ch.req[r], B, code)) return false;
        w |= (uint64_t)code << (32 * r);
    }
    return true;
}
static bool checkWitC(NT t, const Box& B, const Wit& w, const RootCtx& rc, const Cuts& K) {
    const NodeDef& d = ND[t];
    switch (w.kind) {
        case 0: { Box s = B; return !tightenC(t, s, rc, K) || outsideC(t, s, rc, K); }
        case 1: return checkG2(d.items, B, w.w & 0xffff, (w.w >> 16) & 0xffff);
        case 2: return checkTIIlin(d.items, B, w.w);
        case 3: return checkDec(t, 0, B, w.w);
        case 4: return checkDec(t, 1, B, w.w);
    }
    return false;
}
static double integrandPt(NT t, const double* x) {   // x in DEN units
    const NodeDef& d = ND[t];
    double v = 1;
    for (auto& o : d.om) {
        double u = lfval(o.N, x) * DEN / x[o.k];
        v *= u < 1 ? 0 : u >= 3 ? (double)OMT_TOP / SCW : (double)OMT[std::min(1023, (int)(512 * (u - 1)))] / SCW;
    }
    for (int j = 0; j < d.dim; ++j) {
        double tj = x[j] / DEN;
        v *= d.wt[j] == 0 ? 1 : d.wt[j] == 1 ? 1 / tj : 1 / (tj * tj);
    }
    return v;
}
static Samp classify(NT t, const std::array<i64, 8>& x, const RootCtx& rc, const Cuts& K) {
    const NodeDef& d = ND[t];
    Box P; P.n = d.dim;
    for (int j = 0; j < d.dim; ++j) P.lo[j] = P.hi[j] = x[j];
    Samp s{x, 4, {0, 0}, 0};
    if (pointOutsideC(t, P, rc, K)) { s.cls = 0; return s; }
    const Act* save = CUR_ACT;
    CUR_ACT = nullptr;
    int saveF = FILT_N;
    FILT_N = 0;
    struct R { const Act* s; int f; ~R() { CUR_ACT = s; FILT_N = f; } } rs{save, saveF};
    int M, Rm; uint64_t part;
    if (USE_G2 && searchG2Pt(d.items, P, M, Rm)) { s.cls = 1; s.wit = {1, (uint64_t)M | (uint64_t)Rm << 16}; return s; }
    if (USE_TII && searchTIIPt(d.items, P, part)) { s.cls = 1; s.wit = {2, part}; return s; }
    for (int c = 0; c < (int)d.ch.size(); ++c) {
        uint64_t w = 0;
        bool ok = true;
        const Child& ch = d.ch[c];
        for (int r = 0; r < (int)ch.req.size() && ok; ++r) {
            uint32_t code;
            ok = searchTypeIPt(ch.req[r], P, code);
            if (ok) w |= (uint64_t)code << (32 * r);
        }
        if (ok) { s.cls = 2 + c; s.wit = {3 + c, w}; return s; }
    }
    if (d.plus) {
        double xd[8] = {0, 0, 0, 0, 0, 0, 0, 0};
        for (int j = 0; j < d.dim; ++j) xd[j] = (double)x[j];
        s.f = integrandPt(t, xd);
    }
    return s;
}

// the linear constraints of a linear witness (Lemma 4.1 or a Type I code): max over the region of form < lim
// (strict) or <= lim
struct LinCon { LF form; i64 lim; bool strict; };
static LF sumItemsM(const std::vector<Item>& it, int mask) {
    LF s;
    for (int j = 0; j < (int)it.size(); ++j) if (mask >> j & 1) s = s + it[j].a;
    return s;
}
static void witnessCons(NT t, const Wit& w, std::vector<LinCon>& out) {
    const NodeDef& d = ND[t];
    out.clear();
    if (w.kind == 1) {
        int M = w.w & 0xffff, R = (w.w >> 16) & 0xffff;
        LF lr = sumItemsM(d.items, R), l2 = 2 * sumItemsM(d.items, M) + lr;
        LF nl2; nl2.c0 = -l2.c0; for (int j = 0; j < MAXD; ++j) nl2.c[j] = -l2.c[j];
        out.push_back({lr, GAMD - MRG, true});
        out.push_back({l2, 2 * THD - MRG, true});
        out.push_back({nl2, -2 * OMTD - MRG, true});
        return;
    }
    if (w.kind == 3 || w.kind == 4) {
        const Child& ch = d.ch[w.kind - 3];
        for (int r = 0; r < (int)ch.req.size(); ++r) {
            uint32_t code = (uint32_t)(w.w >> (32 * r));
            const TypeIReq& q = ch.req[r];
            int kind = code & 3;
            LF g[3];
            for (int i = 0; i < (int)q.v.size(); ++i) g[(code >> (2 + 2 * i)) & 3] = g[(code >> (2 + 2 * i)) & 3] + q.v[i];
            if (kind == 0) { out.push_back({g[0] + g[1] + g[2], DEN / 2 - MRG, false}); continue; }
            out.push_back({g[0], DEN / 2 - MRG, false});
            if (kind == 1) out.push_back({g[1], TI_N1 - MRG, true});
            if (kind == 2) {
                out.push_back({g[2], TI_H2 - MRG, true});
                out.push_back({2 * g[1] + g[2], THD - MRG, true});
                out.push_back({2 * g[1] + 3 * g[2], TI_S3 - MRG, true});
            }
            if (kind == 3) { out.push_back({g[1], TI_N3 - MRG, true}); out.push_back({g[2], TI_H3 - MRG, true}); }
        }
    }
}


// ---------------- witness palettes (generator only): per root and node type, a few polytopes on which a witness
// holds, found by Monte Carlo along Li's path and a greedy set cover; the generator cuts along their faces ----------
struct PolyW { Wit w; std::vector<LinCon> faces; bool dec; double cov; };
struct Palette { std::vector<PolyW> P[NT_COUNT]; };
static int PAL = 1, PALN = 6000, PALMAX = 40;
static double PALMIN = 0.03;
static double omstarD(double u) { if (u < 1) return 0; if (u < 2) return 1 / u; if (u <= 3) return (1 + std::log(u - 1)) / u; return 0.565073; }
static bool inPoly(const PolyW& pw, const Box& P) {
    for (auto& f : pw.faces) { i64 v = lfmin(f.form, P); if (f.strict ? v >= f.lim : v > f.lim) return false; }
    return true;
}
static void tiiGroups(const NodeDef& d, uint64_t part, LF* Lg, int& ng) {
    int k = d.items.size(), mask[16] = {0};
    ng = 0;
    for (int j = 0; j < k; ++j) { int g = (part >> (4 * j)) & 15; mask[g] |= 1 << j; ng = std::max(ng, g + 1); }
    for (int g = 0; g < ng; ++g) Lg[g] = sumItemsM(d.items, mask[g]);
}
struct PalPt { Box P; double w; int cls; std::vector<int> cands; };
static void buildPalette(int ri, const Box& root, const RootCtx& rc, Palette& pal, uint64_t seed) {
    std::mt19937_64 rng(seed);
    std::uniform_real_distribution<double> U(0, 1);
    std::vector<PalPt> pts[NT_COUNT];
    std::vector<PolyW> cand[NT_COUNT];
    std::map<uint64_t, int> key2c[NT_COUNT];
    double lo0 = (double)root.lo[0] / DEN, hi0 = (double)root.hi[0] / DEN, lo1 = (double)root.lo[1] / DEN, hi1 = (double)root.hi[1] / DEN;
    auto addCand = [&](NT t, uint64_t key, const PolyW& pw) -> int {
        auto it = key2c[t].find(key);
        if (it != key2c[t].end()) return it->second;
        int id = cand[t].size(); cand[t].push_back(pw); key2c[t][key] = id; return id;
    };
    std::vector<LinCon> cons;
    for (int s = 0; s < PALN; ++s) {
        double x0 = lo0 * std::exp(std::log(hi0 / lo0) * U(rng)), x1 = lo1 * std::exp(std::log(hi1 / lo1) * U(rng));
        double W = x0 * std::log(hi0 / lo0) * x1 * std::log(hi1 / lo1);
        NT t = N2;
        Box P; P.n = 2;
        P.lo[0] = P.hi[0] = (i64)llround(x0 * DEN); P.lo[1] = P.hi[1] = (i64)llround(x1 * DEN);
        for (int depth = 0; depth < 8; ++depth) {
            std::array<i64, 8> xa{};
            for (int j = 0; j < P.n; ++j) xa[j] = P.lo[j];
            Samp sm = classify(t, xa, rc, Cuts());
            const NodeDef& d = ND[t];
            if (sm.cls == 0) break;
            double f = W;
            if (d.plus && t != N2) {
                double xd[8], xD[8];
                for (int q = 0; q < 8; ++q) { xd[q] = q < P.n ? (double)P.lo[q] / DEN : 0; xD[q] = q < P.n ? (double)P.lo[q] : 0; }
                for (auto& o : d.om) f *= omstarD(lfval(o.N, xD) / xd[o.k]);
                for (int q = 0; q < d.dim; ++q) f *= d.wt[q] == 0 ? 1 : d.wt[q] == 1 ? 1 / xd[q] : 1 / (xd[q] * xd[q]);
            }
            PalPt pp; pp.P = P; pp.w = f; pp.cls = sm.cls;
            int k = d.items.size(), all = (1 << k) - 1;
            if (sm.cls == 1) {
                i64 v[16], sum[512];
                for (int q = 0; q < k; ++q) v[q] = lfmin(d.items[q].a, P);
                sum[0] = 0;
                for (int S2 = 1; S2 <= all; ++S2) sum[S2] = sum[S2 & (S2 - 1)] + v[__builtin_ctz(S2)];
                // Lemma 4.1: every (M, R)
                for (int R = 1; R < all; ++R) {
                    if (sum[R] >= GAMD - MRG) continue;
                    int comp = all & ~R, low = comp & -comp;
                    for (int M = comp; M; M = (M - 1) & comp) {
                        if (!(M & low) || M == comp) continue;
                        i64 l2 = 2 * sum[M] + sum[R];
                        if (!(l2 < 2 * THD - MRG && l2 > 2 * OMTD + MRG)) continue;
                        Wit w{1, (uint64_t)M | (uint64_t)R << 16, -1};
                        PolyW pw; pw.w = w; pw.dec = false; pw.cov = 0;
                        witnessCons(t, w, cons);
                        for (auto c : cons) { c.lim -= 2; pw.faces.push_back(c); }
                        pp.cands.push_back(addCand(t, 1ULL << 62 | w.w, pw));
                    }
                }
                // Type II: the best partition at the point, as an orthant anchored at the point (thresholds lowered
                // toward the point's values times 0.97 while the plain sum stays > 1)
                uint64_t part;
                if (searchTIIPt(d.items, P, part)) {
                    LF Lg[16]; int ng;
                    tiiGroups(d, part, Lg, ng);
                    i64 a[16];
                    for (int g = 0; g < ng; ++g) a[g] = lfmin(Lg[g], P);
                    // lower vectors b: a uniform shift, a proportional one, and the start of each group's plateau
                    for (int variant = 0; variant < 3; ++variant) {
                        i64 b[16];
                        for (int g = 0; g < ng; ++g) {
                            if (variant == 0) b[g] = a[g] - (i64)(0.03 * DEN);
                            else if (variant == 1) b[g] = (i64)(0.9 * (double)a[g]);
                            else {
                                i64 Fa = fexact(a[g]), l = a[g] - (i64)(0.2 * DEN), h = a[g];   // least a' with F(a') = F(a)
                                if (fexact(l) == Fa) b[g] = l;
                                else { while (h - l > 1) { i64 m = l + (h - l) / 2; if (fexact(m) == Fa) h = m; else l = m; } b[g] = h; }
                            }
                            if (b[g] < 0) b[g] = 0;
                        }
                        auto th = [&](int g, double l) { return b[g] + (i64)(l * (double)(a[g] - b[g])); };
                        auto sumF = [&](double l) { i64 tt = 0; for (int g = 0; g < ng; ++g) tt += fexact(th(g, l)); return tt; };
                        if (sumF(1.0) <= SCF + 64) continue;
                        double lo_ = 0, hi_ = 1;
                        if (sumF(0.0) > SCF + TIIM + 64) hi_ = 0;
                        else for (int it = 0; it < 30; ++it) { double m = 0.5 * (lo_ + hi_); if (sumF(m) > SCF + TIIM + 64) hi_ = m; else lo_ = m; }
                        PolyW pw; pw.w = Wit{2, part, -1}; pw.dec = false; pw.cov = 0;
                        uint64_t key = 1ULL << 61 | part;
                        bool okp = true;
                        for (int g = 0; g < ng; ++g) {
                            i64 tg = th(g, hi_);
                            if (tg + 2 >= a[g] && b[g] < a[g]) { okp = false; break; }   // the anchor must lie inside
                            LF nl; nl.c0 = -Lg[g].c0; for (int j = 0; j < MAXD; ++j) nl.c[j] = -Lg[g].c[j];
                            pw.faces.push_back({nl, -tg - 2, true});            // a_g > tg + 2
                            key = key * 1000003ULL + (uint64_t)(tg >> 22);
                        }
                        if (okp) pp.cands.push_back(addCand(t, key, pw));
                    }
                }
            } else if (sm.cls == 2 || sm.cls == 3) {
                int c = sm.cls - 2;
                const Child& ch = d.ch[c];
                if (!ch.req.empty()) {
                    // every code of each requirement; at most 2 requirements (all pairs, capped)
                    std::vector<std::vector<uint32_t>> codes(ch.req.size());
                    for (size_t r = 0; r < ch.req.size(); ++r) {
                        const TypeIReq& rq = ch.req[r];
                        int kv = rq.v.size();
                        for (int kind = 0; kind <= 3; ++kind) {
                            if (!(rq.kinds >> kind & 1)) continue;
                            int nr = kind == 0 ? 1 : kind == 1 ? 2 : 3;
                            int tot = 1; for (int z = 0; z < kv; ++z) tot *= nr;
                            for (int aa = 0; aa < tot; ++aa) {
                                uint32_t roles = 0; int x = aa;
                                for (int z = 0; z < kv; ++z) { roles |= (uint32_t)(x % nr) << (2 * z); x /= nr; }
                                uint32_t code = (uint32_t)kind | roles << 2;
                                const Act* save = CUR_ACT; CUR_ACT = nullptr;
                                bool ok = checkTypeI(rq, P, code);
                                CUR_ACT = save;
                                if (ok) codes[r].push_back(code);
                            }
                        }
                    }
                    std::vector<uint64_t> ws;
                    if (ch.req.size() == 1) for (uint32_t a0 : codes[0]) ws.push_back(a0);
                    else for (uint32_t a0 : codes[0]) for (uint32_t b0 : codes[1]) { ws.push_back((uint64_t)a0 | (uint64_t)b0 << 32); if (ws.size() > 64) break; }
                    for (uint64_t ww : ws) {
                        Wit w{3 + c, ww, -1};
                        PolyW pw; pw.w = w; pw.dec = true; pw.cov = 0;
                        witnessCons(t, w, cons);
                        for (auto cc : cons) { cc.lim -= 2; pw.faces.push_back(cc); }
                        pp.cands.push_back(addCand(t, (uint64_t)(3 + c) << 60 ^ ww * 0x9E3779B97F4A7C15ULL, pw));
                    }
                }
            }
            pts[t].push_back(pp);
            if (sm.cls == 1 || sm.cls == 4) break;
            // descend into the child
            NT chT = d.ch[sm.cls - 2].type;
            i64 Uc = childUpper(chT, P);
            if (Uc <= NU0) break;
            double aa = (double)NU0 / DEN, bb = (double)Uc / DEN;
            double xn = aa * std::exp(std::log(bb / aa) * U(rng));
            i64 xi = std::min(std::max((i64)llround(xn * DEN), NU0), Uc - 1);
            W *= xn * std::log(bb / aa);
            P.lo[P.n] = P.hi[P.n] = xi; P.n++;
            t = chT;
        }
    }
    // greedy weighted set cover per type: asymptotic polytopes on asymptotic points, decomposition ones on decomposable
    for (int t = 0; t < NT_COUNT; ++t) {
        auto& C = cand[t];
        auto& Pt = pts[t];
        if (C.empty()) continue;
        // point membership by the faces (a polytope covers the points inside it of its own class family)
        std::vector<std::vector<int>> inside(Pt.size());
        for (size_t p = 0; p < Pt.size(); ++p) {
            if (Pt[p].cls == 0 || Pt[p].cls == 4) continue;
            bool wantDec = Pt[p].cls >= 2;
            for (size_t c = 0; c < C.size(); ++c) if (C[c].dec == wantDec && inPoly(C[c], Pt[p].P)) inside[p].push_back(c);
        }
        double tot = 0;
        for (size_t p = 0; p < Pt.size(); ++p) if (Pt[p].cls == 1 || Pt[p].cls == 2 || Pt[p].cls == 3) tot += Pt[p].w;
        std::vector<char> cov(Pt.size(), 0);
        double done = 0;
        while ((int)pal.P[t].size() < PALMAX) {
            std::vector<double> gain(C.size(), 0);
            for (size_t p = 0; p < Pt.size(); ++p) if (!cov[p]) for (int c : inside[p]) gain[c] += Pt[p].w;
            int best = -1; double bg = 0;
            for (size_t c = 0; c < C.size(); ++c) if (gain[c] > bg) { bg = gain[c]; best = c; }
            if (best < 0 || bg < 1e-4 * tot) break;
            for (size_t p = 0; p < Pt.size(); ++p) if (!cov[p]) for (int c : inside[p]) if (c == best) { cov[p] = 1; break; }
            done += bg;
            C[best].cov = bg / tot;
            pal.P[t].push_back(C[best]);
        }
        if (getenv("PALVERB")) printf("palette root %d %s: %zu points, %zu candidates, %zu chosen, covering %.4f\n", ri,
                                      ND[t].name.c_str(), Pt.size(), C.size(), pal.P[t].size(), tot > 0 ? done / tot : 0);
    }
}

// ---------------- the generator ----------------
static std::atomic<long long> CUTS[NT_COUNT][6];   // peel, midpoint, slack, minus-peel, diagonal, alt-minus
struct VS { int q1 = 0, k1 = 1, q2 = 0, k2 = 1; };
static std::atomic<long long> ROOTDROPS(0);   // the root's last-resort drops
static int N2DROP = 0;                         // n2drop=1: the root may drop like any + node, by cost

struct Gen {
    Tree tr;
    std::vector<TNode>& T = tr.T;
    std::mt19937_64 rng;
    const RootCtx* rcp = nullptr;
    const Palette* pal = nullptr;
    uint64_t curExcl = 0;
    Gen(uint64_t seed) : rng(seed) {}

    void samples(NT t, const Box& B, const RootCtx& rc, const Cuts& K, std::vector<Samp>& S, int extra = 0) {
        int n = B.n;
        std::array<i64, 8> x{};
        int nc = n <= 4 ? (1 << n) : 12;
        if (K.n && CORNERCUT == 0) nc = 0;              // a region with cuts: its box corners are mostly outside it
        for (int c = 0; c < nc; ++c) {
            uint32_t bits = n <= 4 ? c : (uint32_t)rng();
            for (int j = 0; j < n; ++j) x[j] = (bits >> j & 1) ? B.hi[j] - 1 : B.lo[j];
            S.push_back(classify(t, x, rc, K));
        }
        for (int j = 0; j < n; ++j) x[j] = B.lo[j] + (B.hi[j] - B.lo[j]) / 2;
        S.push_back(classify(t, x, rc, K));
        int nin = 0;
        for (auto& s : S) if (s.cls != 0) ++nin;
        int want = NSAMP + extra, got = 0;
        for (int r = 0; r < 6 * (NSAMP + extra + MININ) && (got < want || nin < MININ); ++r) {
            for (int j = 0; j < n; ++j) x[j] = B.lo[j] + (i64)(rng() % (uint64_t)std::max<i64>(1, B.hi[j] - B.lo[j]));
            Box P; P.n = n;
            for (int j = 0; j < n; ++j) P.lo[j] = P.hi[j] = x[j];
            bool outp = pointOutsideC(t, P, rc, K);
            if (outp && got >= want) continue;          // beyond the plain number, keep only points of the region
            S.push_back(classify(t, x, rc, K));
            ++got;
            if (!outp) ++nin;
        }
    }
    static void candidates(const std::vector<Samp>& S, bool out, bool asym, bool dec, std::vector<Wit>& cand) {
        int nOut = 0;
        for (auto& s : S) if (s.cls == 0) ++nOut;
        if (out && nOut) cand.push_back({0, 0, -1});
        for (int i = 0; i < (int)S.size(); ++i) {
            const Samp& s = S[i];
            if (!((asym && s.cls == 1) || (dec && (s.cls == 2 || s.cls == 3)))) continue;
            bool dup = false;
            for (auto& w : cand) if (w.kind == s.wit.kind && w.w == s.wit.w) dup = true;
            if (!dup && cand.size() < 10) { Wit w = s.wit; w.si = i; cand.push_back(w); }
        }
    }
    int chooseSplit(const Box& B, const std::vector<Samp>& S) {
        int best = -1; double bscore = 1e18;
        for (int j = 0; j < B.n; ++j) {
            if (B.hi[j] - B.lo[j] < 2 * MINW) continue;
            i64 mid = B.lo[j] + (B.hi[j] - B.lo[j]) / 2;
            int cnt[2][5] = {{0}};
            for (auto& s : S) cnt[s.x[j] >= mid][s.cls]++;
            int imp = 0;
            for (int h = 0; h < 2; ++h) {
                int tot = 0, mx = 0;
                for (int c = 0; c < 5; ++c) { tot += cnt[h][c]; mx = std::max(mx, cnt[h][c]); }
                imp += tot - mx;
            }
            double rel = (double)(B.hi[j] - B.lo[j]) / B.hi[j];
            double score = imp - 0.5 * rel;
            if (score < bscore) { bscore = score; best = j; }
        }
        return best;
    }
    int chooseSplitW(NT t, const Box& B, const RootCtx& rc, const Cuts& K, const std::vector<Samp>& S) {
        std::vector<Wit> cand;
        candidates(S, true, true, true, cand);
        if (cand.empty()) return chooseSplit(B, S);
        int best = -1; double bscore = -1e30;
        for (int j = 0; j < B.n; ++j) {
            if (B.hi[j] - B.lo[j] < 2 * MINW) continue;
            i64 mid = B.lo[j] + (B.hi[j] - B.lo[j]) / 2;
            Box H[2] = {B, B};
            H[0].hi[j] = mid; H[1].lo[j] = mid;
            double score = 0, worst = 1e30;
            for (int h = 0; h < 2; ++h) {
                bool okh = false; double bm = -1e30;
                for (auto& w : cand) {
                    if (w.kind == 2) {
                        i64 v = tiiLinValue(ND[t].items, H[h], w.w);
                        bm = std::max(bm, (double)(v - SCF) / SCF);
                        if (v > SCF + TIIM) okh = true;
                    } else if (checkWitC(t, H[h], w, rc, K)) okh = true;
                }
                if (okh) score += 10;
                worst = std::min(worst, bm);
            }
            score += worst > -1e29 ? worst : 0;
            score += 1e-3 * (double)(B.hi[j] - B.lo[j]) / B.hi[j];
            if (score > bscore) { bscore = score; best = j; }
        }
        return best;
    }
    double share(NT t, const Box& B, const Box& sub, i64 bfull) {
        if (ND[t].plus && bfull > 0) return (double)dropCost(t, sub) / bfull;
        double r = 1;
        for (int j = 0; j < B.n; ++j) r *= (double)(sub.hi[j] - sub.lo[j]) / (B.hi[j] - B.lo[j]);
        return r;
    }
    bool findPeel(NT t, const Box& B, const RootCtx& rc, const Cuts& K, const std::vector<Wit>& cand, i64 bfull,
                  int& jo, i64& spo, double& so) {
        so = 0; jo = -1;
        for (auto& w : cand) {
            for (int j = 0; j < B.n; ++j) {
                i64 w0 = B.hi[j] - B.lo[j];
                if (w0 < 2 * MINW) continue;
                for (int side = 0; side < 2; ++side) {
                    Box sub = B;
                    if (side == 0) sub.hi[j] = B.lo[j] + MINW; else sub.lo[j] = B.hi[j] - MINW;
                    if (!checkWitC(t, sub, w, rc, K)) continue;
                    i64 good = side == 0 ? sub.hi[j] : sub.lo[j];
                    i64 bad = side == 0 ? B.hi[j] : B.lo[j];
                    while ((side == 0 ? bad - good : good - bad) > 1 && std::llabs(bad - good) > MINW / 64) {
                        i64 mid = good + (bad - good) / 2;
                        Box s2 = B;
                        if (side == 0) s2.hi[j] = mid; else s2.lo[j] = mid;
                        if (checkWitC(t, s2, w, rc, K)) good = mid; else bad = mid;
                    }
                    if (side == 0) good = std::min(good, B.hi[j] - MINW); else good = std::max(good, B.lo[j] + MINW);
                    Box s3 = B;
                    if (side == 0) s3.hi[j] = good; else s3.lo[j] = good;
                    if (good <= B.lo[j] || good >= B.hi[j]) continue;
                    double sc = share(t, B, s3, bfull);
                    if (w.kind >= 3) sc *= 0.7;
                    if (sc > so) { so = sc; jo = j; spo = good; }
                }
            }
        }
        return jo >= 0;
    }
    // MC estimate of the share of the region on the side L < 0 (weighted by the integrand for + nodes)
    double diagShare(NT t, const Box& B, const RootCtx& rc, const Cuts& K, const LF& L) {
        const NodeDef& d = ND[t];
        double in = 0, all = 0;
        std::array<i64, 8> x{};
        for (int r = 0; r < 96; ++r) {
            for (int j = 0; j < B.n; ++j) x[j] = B.lo[j] + (i64)(rng() % (uint64_t)std::max<i64>(1, B.hi[j] - B.lo[j]));
            Box P; P.n = B.n;
            for (int j = 0; j < B.n; ++j) P.lo[j] = P.hi[j] = x[j];
            if (pointOutsideC(t, P, rc, K)) continue;
            double wgt = 1;
            if (d.plus) {
                double xd[8] = {0, 0, 0, 0, 0, 0, 0, 0};
                for (int j = 0; j < B.n; ++j) xd[j] = (double)x[j];
                wgt = integrandPt(t, xd) + 1e-30;
            }
            all += wgt;
            if (lfmin(L, P) < 0) in += wgt;
        }
        return all > 0 ? in / all : 0;
    }
    // the best diagonal cut along a failing face of a linear witness of the samples: the witness side's share, and
    // whether the witness then holds on that side
    // the weighted share of the region's samples at which a witness holds (point checks)
    double coverage(NT t, const RootCtx& rc, const std::vector<Samp>& S, const Wit& w) {
        const Act* save = CUR_ACT; CUR_ACT = nullptr;
        double in = 0, all = 0;
        Cuts none;
        for (auto& s : S) {
            if (s.cls == 0) continue;
            double wt = ND[t].plus ? (s.cls == 4 ? s.f : 1e-30 + sampW(t, s)) : 1;
            all += wt;
            Box P; P.n = ND[t].dim;
            for (int j = 0; j < P.n; ++j) P.lo[j] = P.hi[j] = s.x[j];
            bool ok = w.kind == 2 ? checkTII(ND[t].items, P, w.w) : checkWitC(t, P, w, rc, none);
            if (ok) in += wt;
        }
        CUR_ACT = save;
        return all > 0 ? in / all : 0;
    }
    static double sampW(NT t, const Samp& s) {
        double xd[8] = {0, 0, 0, 0, 0, 0, 0, 0};
        for (int j = 0; j < ND[t].dim; ++j) xd[j] = (double)s.x[j];
        return integrandPt(t, xd);
    }
    bool findDiag(NT t, const Box& B, const RootCtx& rc, const Cuts& K, const std::vector<Wit>& cand, LF& Lo, double& so,
                  bool& resolves, const std::vector<Samp>* SP = nullptr) {
        so = 0; resolves = false;
        if (!DIAG || K.n >= std::min(MAXDIAG, MAXCUT)) return false;
        const int nzMax = ND[t].plus ? DIAGNZP : DIAGNZM;
        std::vector<LinCon> cons;
        bool found = false;
        for (auto& w : cand) {
            double covw = (COVSEL && SP) ? coverage(t, rc, *SP, w) : -1;
            if (w.kind == 2 && DIAGTII) {
                // a Type II witness: cut along one group's exponent a_g = t, t the least value with
                // F(t) > SCF - (sum of the other groups' F at their minima on the region): the plain check then holds
                // on {a_g > t} (the other minima can only rise there)
                const NodeDef& d = ND[t];
                int k = d.items.size(), mask[16] = {0}, ng = 0;
                for (int j = 0; j < k; ++j) { int g = (w.w >> (4 * j)) & 15; mask[g] |= 1 << j; ng = std::max(ng, g + 1); }
                i64 Fg[16], tot = 0;
                LF Lg[16];
                bool okw = true;
                for (int g = 0; g < ng; ++g) {
                    if (!mask[g]) { okw = false; break; }
                    Lg[g] = sumItemsM(d.items, mask[g]);
                    Fg[g] = fexact(lfminA(Lg[g], B));
                    tot += Fg[g];
                }
                if (!okw) continue;
                if (ORTHANT && SP && w.si >= 0) {
                    // thresholds t_g = lo_g + lam (a_g(x_s) - lo_g), the least lam with sum F(t_g) > SCF (x_s: a sample
                    // where the witness holds): the plain check holds on {a_g >= t_g for all g}; cut the group whose
                    // threshold is the most violated
                    Box Ps; Ps.n = B.n;
                    for (int j = 0; j < B.n; ++j) Ps.lo[j] = Ps.hi[j] = (*SP)[w.si].x[j];
                    i64 lo[16], as[16];
                    for (int g = 0; g < ng; ++g) { lo[g] = lfminA(Lg[g], B); as[g] = lfmin(Lg[g], Ps); }
                    auto sumF = [&](double lam) { i64 tt = 0; for (int g = 0; g < ng; ++g) tt += fexact(lo[g] + (i64)(lam * (double)std::max<i64>(0, as[g] - lo[g]))); return tt; };
                    if (sumF(1.0) <= SCF + 64) continue;
                    double a = 0, b = 1;
                    for (int it2 = 0; it2 < 30; ++it2) { double m = 0.5 * (a + b); if (sumF(m) > SCF + TIIM + 64) b = m; else a = m; }
                    int gbest = -1; double vbest = 0;
                    for (int g = 0; g < ng; ++g) {
                        i64 tg = lo[g] + (i64)(b * (double)std::max<i64>(0, as[g] - lo[g]));
                        if (tg <= lo[g]) continue;
                        int nz = 0;
                        for (int j = 0; j < B.n; ++j) if (Lg[g].c[j] && B.hi[j] - B.lo[j] > 1) ++nz;
                        if (nz < 1 || nz > nzMax) continue;
                        double viol = (double)(tg - lo[g]) / (double)std::max<i64>(1, lfmaxA(Lg[g], B) - lo[g]);
                        if (viol > vbest) { vbest = viol; gbest = g; }
                    }
                    if (gbest < 0) continue;
                    i64 tg = lo[gbest] + (i64)(b * (double)std::max<i64>(0, as[gbest] - lo[gbest]));
                    LF L;                                      // the witness side: a_g > tg + 2
                    L.c0 = tg + 2 - Lg[gbest].c0;
                    for (int j = 0; j < MAXD; ++j) L.c[j] = -Lg[gbest].c[j];
                    double sh = diagShare(t, B, rc, K, L);
                    if (sh <= 0.02 || sh >= 0.995) continue;
                    double sc = covw >= 0 ? std::max(covw, 0.0) * 0.9 : sh * 0.9;
                    if (sc > so) { so = sc; Lo = L; resolves = false; found = true; }
                    continue;
                }
                for (int g = 0; g < ng; ++g) {
                    int nz = 0;
                    for (int j = 0; j < B.n; ++j) if (Lg[g].c[j] && B.hi[j] - B.lo[j] > 1) ++nz;
                    if (nz < 2 || nz > nzMax) continue;
                    i64 target = SCF - (tot - Fg[g]);          // need F(a_g) > target
                    i64 lo = lfminA(Lg[g], B), hi = lfmaxA(Lg[g], B);
                    if (fexact(hi) <= target) continue;
                    i64 a = lo, b = hi;                        // F(a) <= target < F(b)
                    if (fexact(a) > target) continue;          // already holds (the witness would pass)
                    while (b - a > 1) { i64 m = a + (b - a) / 2; if (fexact(m) > target) b = m; else a = m; }
                    LF L;                                      // the witness side: a_g > b + 2, i.e. b + 2 - a_g < 0
                    L.c0 = b + 2 - Lg[g].c0;
                    for (int j = 0; j < MAXD; ++j) L.c[j] = -Lg[g].c[j];
                    double sh = diagShare(t, B, rc, K, L);
                    if (sh <= 0.02 || sh >= 0.98) continue;
                    double sc = covw >= 0 ? std::min(sh, covw) * 0.9 : sh * 0.9;
                    if (sc > so) { so = sc; Lo = L; resolves = true; found = true; }
                }
                continue;
            }
            if (w.kind != 1 && w.kind != 3 && w.kind != 4) continue;
            witnessCons(t, w, cons);
            int nfail = 0, fi = -1;
            i64 worst = 0;
            for (int i = 0; i < (int)cons.size(); ++i) {
                i64 mx = lfmaxA(cons[i].form, B);
                bool ok = cons[i].strict ? mx < cons[i].lim : mx <= cons[i].lim;
                if (ok) continue;
                ++nfail;
                // must be a genuinely diagonal face: at least two coordinates of positive width
                int nz = 0;
                for (int j = 0; j < B.n; ++j) if (cons[i].form.c[j] && B.hi[j] - B.lo[j] > 1) ++nz;
                if (nz < 2 || nz > nzMax) continue;
                if (fi < 0 || mx - cons[i].lim > worst) { worst = mx - cons[i].lim; fi = i; }
            }
            if (fi < 0) continue;
            LF L = cons[fi].form;
            L.c0 -= cons[fi].lim - 2;            // the witness side: form < lim - 2
            double sh = diagShare(t, B, rc, K, L);
            if (sh <= 0.02 || sh >= 0.98) continue;
            // does the witness hold on that side?
            Cuts K2 = K;
            K2.c[K2.n++] = {L, true};
            Box B2 = B;
            bool res = false;
            if (tightenC(t, B2, rc, K2)) {
                Act a2; activesC(t, B2, rc, K2, a2);
                const Act* save = CUR_ACT; CUR_ACT = &a2;
                res = checkWitC(t, B2, w, rc, K2);
                CUR_ACT = save;
            }
            double sc = covw >= 0 ? (res ? sh : covw * 0.7) * (w.kind >= 3 ? 0.7 : 1.0)
                                  : sh * (res ? 1.0 : 0.5) * (w.kind >= 3 ? 0.7 : 1.0) * (nfail == 1 ? 1.0 : 0.8);
            if (sc > so) { so = sc; Lo = L; resolves = res; found = true; }
        }
        return found;
    }
    // the best virtual split of a drop: coordinates of the active diagonal constraints and of omega's argument
    i64 bestDrop(NT t, const Box& B, const RootCtx& rc, const Cuts& K, const Act& act, VS& vs, i64 LAM) {
        vs = VS();
        i64 base = dropCost(t, B);
        if (base <= 4 * LAM || VSMAX <= 1) return base;
        bool cq[MAXD] = {false};
        for (int i = 0; i < act.n; ++i) for (int j = 0; j < B.n; ++j) if (act.g[i].c[j] && B.hi[j] - B.lo[j] > 8) cq[j] = true;
        for (auto& o : ND[t].om) { if (B.hi[o.k] - B.lo[o.k] > 8) cq[o.k] = true; }
        // chained coordinates whose ranges overlap gain from finer elementary intervals too
        double bestScore = (double)base;
        i64 bestV = base;
        auto score = [&](i64 v, int parts) { return (double)v + VSW * parts * (double)LAM; };
        int bq = -1;
        for (int q = 0; q < B.n; ++q) {
            if (!cq[q]) continue;
            i64 v = dropCostVS(t, B, rc, K, q, 4, 0, 1);
            double s = score(v, 4);
            if (s < bestScore) { bestScore = s; bestV = v; vs = {q, 4, 0, 1}; bq = q; }
        }
        if (bq < 0) return base;
        for (int k : {8, 16}) {
            if (k > VSMAX) break;
            i64 v = dropCostVS(t, B, rc, K, bq, k, 0, 1);
            double s = score(v, k);
            if (s < bestScore) { bestScore = s; bestV = v; vs = {bq, k, 0, 1}; } else break;
        }
        // a second coordinate
        int q1 = vs.q1, k1 = vs.k1, bq2 = -1;
        for (int q = 0; q < B.n; ++q) {
            if (!cq[q] || q == q1) continue;
            i64 v = dropCostVS(t, B, rc, K, q1, k1, q, 2);
            double s = score(v, 2 * k1);
            if (s < bestScore) { bestScore = s; bestV = v; vs = {q1, k1, q, 2}; bq2 = q; }
        }
        if (bq2 >= 0) {
            for (int k : {4, 8}) {
                if (k * k1 > 64) break;
                i64 v = dropCostVS(t, B, rc, K, q1, k1, bq2, k);
                double s = score(v, k * k1);
                if (s < bestScore) { bestScore = s; bestV = v; vs = {q1, k1, bq2, k}; } else break;
            }
        }
        return bestV;
    }
    i64 tryDec(NT t, int c, const Box& B, const RootCtx& rc, const Cuts& K, int lvl, uint64_t excl = 0) {
        const Child& ch = ND[t].ch[c];
        Box C = B; C.n = B.n + 1;
        i64 U = childUpper(ch.type, B);
        C.lo[B.n] = NU0; C.hi[B.n] = std::max(U, NU0 + 1);
        return gen(ch.type, C, rc, K, lvl);
    }
    i64 cut(NT t, const Box& B, const RootCtx& rc, const Cuts& K, int lvl, size_t mark, int j, i64 sp, uint64_t excl = 0) {
        T[mark].dec = D_SPLIT; T[mark].sc = j; T[mark].sp = sp; T[mark].w = 0;
        Box L = B, Rb = B;
        L.hi[j] = sp; Rb.lo[j] = sp;
        i64 v1 = gen(t, L, rc, K, lvl + 1, excl);
        if (v1 >= INF) return INF;
        i64 v2 = gen(t, Rb, rc, K, lvl + 1, excl);
        if (v2 >= INF) return INF;
        return v1 + v2;
    }
    i64 dcut(NT t, const Box& B, const RootCtx& rc, const Cuts& K, int lvl, size_t mark, const LF& L, uint64_t excl = 0, uint64_t exclB = 0) {
        T[mark].dec = D_LSPLIT; T[mark].w = tr.F.size(); T[mark].sc = 0; T[mark].sp = 0;
        tr.F.push_back(L);
        Cuts K1 = K, K2 = K;
        K1.c[K1.n++] = {L, true};
        K2.c[K2.n++] = {L, false};
        i64 v1 = gen(t, B, rc, K1, lvl + 1, excl);
        if (v1 >= INF) return INF;
        i64 v2 = gen(t, B, rc, K2, lvl + 1, excl | exclB);
        if (v2 >= INF) return INF;
        return v1 + v2;
    }
    // the cut of a node by its samples: an axis peel, a diagonal face cut, or a halving
    i64 cutBySamples(NT t, const Box& B, const RootCtx& rc, const Cuts& K, int lvl, size_t mark, const std::vector<Samp>& S,
                     bool asymOnly, double pmin, i64 bfull, bool& done) {
        done = false;
        std::vector<Wit> cand;
        candidates(S, true, true, !asymOnly, cand);
        int j = -1; i64 sp = 0; double sc = 0;
        bool peel = findPeel(t, B, rc, K, cand, bfull, j, sp, sc) && sc >= pmin;
        LF L; double sd = 0; bool res = false;
        bool diag = findDiag(t, B, rc, K, cand, L, sd, res, &S) && sd * DIAGPREF >= pmin;
        if (diag && (!peel || sd * DIAGPREF > sc)) {
            CUTS[t][4]++;
            { char buf[160]; snprintf(buf, sizeof buf, "DSPLIT%s share %.3f peel %.3f", asymOnly ? "(asym)" : "", sd, peel ? sc : 0.0); traceNode(t, B, K, lvl, buf, &S); }
            done = true;
            return dcut(t, B, rc, K, lvl, mark, L, curExcl, 0);
        }
        if (!peel) {
            if (asymOnly) return INF;
            j = chooseSplitW(t, B, rc, K, S);
            if (j < 0) return INF;
            sp = B.lo[j] + (B.hi[j] - B.lo[j]) / 2;
            CUTS[t][1]++;
            { char buf[160]; snprintf(buf, sizeof buf, "HALVE x%d (diag share %.3f)", j, diag ? sd : 0.0); traceNode(t, B, K, lvl, buf, &S); }
        } else { CUTS[t][asymOnly ? 3 : 0]++; char buf[160]; snprintf(buf, sizeof buf, "PEEL%s x%d share %.3f (diag %.3f)", asymOnly ? "(asym)" : "", j, sc, diag ? sd : 0.0); traceNode(t, B, K, lvl, buf, &S); }
        done = true;
        return cut(t, B, rc, K, lvl, mark, j, sp, curExcl);
    }
    // up to 3 points of the region (the tightened box's centre if inside, then random points)
    int filterPoints(NT t, const Box& B, const RootCtx& rc, const Cuts& K, Box* FP) {
        int n = 0;
        Box P; P.n = B.n;
        for (int j = 0; j < B.n; ++j) P.lo[j] = P.hi[j] = B.lo[j] + (B.hi[j] - B.lo[j]) / 2;
        if (!pointOutsideC(t, P, rc, K)) FP[n++] = P;
        for (int tries = 0; tries < 12 && n < 3; ++tries) {
            for (int j = 0; j < B.n; ++j) P.lo[j] = P.hi[j] = B.lo[j] + (i64)(rng() % (uint64_t)std::max<i64>(1, B.hi[j] - B.lo[j]));
            if (!pointOutsideC(t, P, rc, K)) FP[n++] = P;
        }
        return n;
    }
    void restore(size_t mark, NT t) { T.resize(mark + 1); T[mark] = TNode{(uint8_t)t, D_OUT, 0, 1, 0, 1, 0, 0, 0, 0}; }

    long long traceCount = 0;
    void traceNode(NT t, const Box& B, const Cuts& K, int lvl, const char* what, const std::vector<Samp>* S) {
        if (!TRACET || ND[t].name != TRACET || traceCount > TRACEMAX) return;
        ++traceCount;
        int c[5] = {0, 0, 0, 0, 0};
        if (S) for (auto& s : *S) c[s.cls]++;
        printf("TN %s lvl %d cuts %d %s samples o%d a%d d%d/%d l%d box", ND[t].name.c_str(), lvl, K.n, what, c[0], c[1], c[2], c[3], c[4]);
        for (int j = 0; j < B.n; ++j) printf(" [%.4f,%.4f)", (double)B.lo[j] / DEN, (double)B.hi[j] / DEN);
        printf("\n");
    }
    i64 gen(NT t, Box B, const RootCtx& rc, const Cuts& K0, int lvl, uint64_t excl = 0) {
        const NodeDef& d = ND[t];
        size_t mark = T.size();
        size_t fmark = tr.F.size();
        T.push_back(TNode{(uint8_t)t, D_OUT, 0, 1, 0, 1, 0, 0, 0, 0});
        if (!tightenC(t, B, rc, K0) || outsideC(t, B, rc, K0)) return 0;
        const Cuts K = PRUNE ? pruneCuts(K0, B) : K0;
        Act act;
        activesC(t, B, rc, K, act);
        const Act* saveAct = CUR_ACT;
        CUR_ACT = &act;
        struct Restore { const Act* s; ~Restore() { CUR_ACT = s; } } restoreAct{saveAct};
        int M, R; uint64_t part;
        Box FP[4]; int nFP = filterPoints(t, B, rc, K, FP);
        auto filtOn = [&]() { FILT_N = USEFILT ? nFP : 0; for (int q = 0; q < FILT_N; ++q) FILT_P[q] = FP[q]; };
        auto filtOff = [&]() { FILT_N = 0; };
        filtOn();
        if (USE_G2 && searchG2(d.items, B, M, R)) { filtOff(); T[mark].dec = D_ASYM_G2; T[mark].w = (uint64_t)M | (uint64_t)R << 16; traceNode(t, B, K, lvl, "ASYM-G2", nullptr); return 0; }
        if (USE_TII && searchTII(d.items, B, part)) { filtOff(); T[mark].dec = D_ASYM_TII; T[mark].w = part; traceNode(t, B, K, lvl, "ASYM-TII", nullptr); return 0; }
        filtOff();
        const i64 LAM = (i64)(LAMBDA * SC);
        bool canDrop = d.plus && (t != N2 || N2DROP);
        VS vs;
        i64 drop = canDrop ? bestDrop(t, B, rc, K, act, vs, LAM) : INF;
        double dropNodes = 1 + (vs.k1 * vs.k2 > 1 ? VSW * vs.k1 * vs.k2 : 0);
        auto toDrop = [&]() {
            T.resize(mark + 1); tr.F.resize(fmark);
            T[mark] = TNode{(uint8_t)t, D_DROP, 0, (uint8_t)vs.k1, (uint8_t)vs.q2, (uint8_t)vs.k2, 0, 0, 0, 0};
            T[mark].sc = vs.q1;
            return drop;
        };
        auto score = [&](i64 v) { return (double)v + (double)LAM * (double)(T.size() - mark); };
        auto better = [&](i64 v) { return v < INF && (!canDrop || score(v) < (double)drop + LAM * dropNodes); };
        if (canDrop && drop <= 2 * LAM) return toDrop();
        // the root's last resort: where no decision passes (a sliver of the checker's slack), drop it
        auto lastResort = [&]() -> i64 {
            if (!(d.plus && t == N2)) return INF;
            drop = bestDrop(t, B, rc, K, act, vs, LAM);
            if (drop >= INF) return INF;
            ROOTDROPS++;
            return toDrop();
        };
        std::vector<Samp> S;
        bool sampled = false;
        // separate the asymptotic parts first (the - nodes always; + nodes when cheaper)
        auto splitFirst = [&](i64& vout) -> bool {
            if (lvl >= MAXLVL || d.ch.empty()) return false;
            i64 size = drop;
            if (!d.plus) {
                const Child& ch0 = d.ch[0];
                Box C = B; C.n = B.n + 1;
                C.lo[B.n] = NU0; C.hi[B.n] = std::max(childUpper(ch0.type, B), NU0 + 1);
                size = ND[ch0.type].plus ? dropCost(ch0.type, C) : (i64)(PBF * LAM) + 1;
            }
            if (size <= PBF * LAM) return false;
            if (!sampled) { samples(t, B, rc, K, S); sampled = true; }
            int nA = 0, nO = 0;
            for (auto& s : S) { if (s.cls == 1) ++nA; if (s.cls == 0) ++nO; }
            if (!(nA > 0 && nA + nO < (int)S.size())) return false;
            bool done;
            curExcl = excl;
            vout = cutBySamples(t, B, rc, K, lvl, mark, S, true, PEELMIN2, 0, done);
            if (!done) {
                std::vector<Wit> cand;
                int j = chooseSplitW(t, B, rc, K, S);
                if (j < 0) return false;
                CUTS[t][3]++;
                vout = cut(t, B, rc, K, lvl, mark, j, B.lo[j] + (B.hi[j] - B.lo[j]) / 2, excl);
            }
            return vout < INF;
        };
        // palette cut: the polytope of the root's palette holding at the largest share of the region's samples; cut
        // along its face that the most samples violate (the violated side excludes that polytope)
        if (PAL && pal && !pal->P[t].empty() && lvl < MAXLVL && K.n < std::min(MAXDIAG, MAXCUT)) {
            if (!sampled) { samples(t, B, rc, K, S); sampled = true; }
            const auto& PP = pal->P[t];
            int np = std::min<int>(PP.size(), 64);
            std::vector<double> wi(np, 0);
            double totw = 0;
            for (auto& sp : S) {
                if (sp.cls == 0) continue;
                double wgt = d.plus ? (sp.cls == 4 ? sp.f : sampW(t, sp)) + 1e-30 : 1;
                totw += wgt;
                Box P; P.n = B.n;
                for (int j = 0; j < B.n; ++j) P.lo[j] = P.hi[j] = sp.x[j];
                for (int i = 0; i < np; ++i) if (!(excl >> i & 1) && inPoly(PP[i], P)) wi[i] += wgt;
            }
            int bi = -1; double bw = 0;
            for (int i = 0; i < np; ++i) if (wi[i] > bw * 1.0001) { bw = wi[i]; bi = i; }
            if (bi >= 0 && totw > 0 && bw / totw >= PALMIN) {
                // the violated faces on the region; the cut: the face most samples violate
                int fbest = -1; double fw = -1;
                for (int f = 0; f < (int)PP[bi].faces.size(); ++f) {
                    const LinCon& fc = PP[bi].faces[f];
                    i64 mx = lfmaxA(fc.form, B);
                    bool ok = fc.strict ? mx < fc.lim : mx <= fc.lim;
                    if (ok) continue;
                    double vw = 0;
                    for (auto& sp : S) {
                        if (sp.cls == 0) continue;
                        Box P; P.n = B.n;
                        for (int j = 0; j < B.n; ++j) P.lo[j] = P.hi[j] = sp.x[j];
                        i64 v = lfmin(fc.form, P);
                        if (fc.strict ? v >= fc.lim : v > fc.lim) vw += d.plus ? (sp.cls == 4 ? sp.f : sampW(t, sp)) + 1e-30 : 1;
                    }
                    if (vw > fw) { fw = vw; fbest = f; }
                }
                if (fbest >= 0) {
                    const LinCon& fc = PP[bi].faces[fbest];
                    LF L = fc.form; L.c0 -= fc.lim;            // the polytope's side: form < lim
                    CUTS[t][4]++;
                    { char buf[160]; snprintf(buf, sizeof buf, "PALCUT #%d share %.3f face %d", bi, bw / totw, fbest); traceNode(t, B, K, lvl, buf, &S); }
                    i64 v = dcut(t, B, rc, K, lvl, mark, L, excl, 1ULL << bi);
                    if (!d.plus) { if (v < INF) return v; restore(mark, t); tr.F.resize(fmark); }
                    else {
                        if (canDrop && !better(v)) return toDrop();
                        if (v < INF) return v;
                        restore(mark, t); tr.F.resize(fmark);
                    }
                }
            }
        }
        curExcl = excl;
        if (!d.plus) {
            i64 v;
            if (splitFirst(v)) return v;
            restore(mark, t); tr.F.resize(fmark);
        }
        if (d.plus && t != N2 && !d.ch.empty() && ASYMFRAC <= 1) {
            if (!sampled) { samples(t, B, rc, K, S); sampled = true; }
            int nA = 0, nN = 0;
            for (auto& s : S) { if (s.cls != 0) ++nN; if (s.cls == 1) ++nA; }
            if (nN > 0 && nA >= ASYMFRAC * nN) {
                i64 v;
                if (splitFirst(v) && better(v)) return v;
                restore(mark, t); tr.F.resize(fmark);
            }
        }
        // whole-region decompositions (Li's order); for - nodes the alternative of cutting first is compared when the
        // preferred decomposition fails on the region but holds at some samples
        for (int c = 0; c < (int)d.ch.size(); ++c) {
            uint64_t w;
            filtOn();
            bool okDec = searchDec(t, c, B, w);
            filtOff();
            if (!okDec) continue;
            if (!d.plus && c > 0 && ALTMINUS) {
                // the earlier decompositions hold somewhere in the region? then compare
                if (!sampled) { samples(t, B, rc, K, S, 8); sampled = true; }
                int nEarlier = 0;
                for (auto& s : S) if (s.cls >= 2 && s.cls < 2 + c) ++nEarlier;
                Box C = B; C.n = B.n + 1;
                C.lo[B.n] = NU0; C.hi[B.n] = std::max(childUpper(d.ch[0].type, B), NU0 + 1);
                i64 sz = ND[d.ch[0].type].plus ? dropCost(d.ch[0].type, C) : 0;
                if (nEarlier > 0 && (double)sz / SC > ALTMIN && lvl < MAXLVL) {
                    T[mark].dec = c == 0 ? D_DEC0 : D_DEC1; T[mark].w = w;
                    i64 vA = tryDec(t, c, B, rc, K, lvl);
                    double sA = vA < INF ? score(vA) : 1e300;
                    std::vector<TNode> subA(T.begin() + mark + 1, T.end());
                    std::vector<LF> fA(tr.F.begin() + fmark, tr.F.end());
                    restore(mark, t); tr.F.resize(fmark);
                    bool done;
                    curExcl = excl;
                    i64 vB = cutBySamples(t, B, rc, K, lvl, mark, S, false, PEELMIN, 0, done);
                    double sB = (done && vB < INF) ? score(vB) : 1e300;
                    CUTS[t][5]++;
                    if (sB < sA) return vB;
                    restore(mark, t); tr.F.resize(fmark);
                    if (vA >= INF) { T.resize(mark); return INF; }
                    T[mark].dec = c == 0 ? D_DEC0 : D_DEC1; T[mark].w = w;
                    // re-index the forms of subtree A
                    size_t base = tr.F.size();
                    for (auto& nd : subA) if (nd.dec == D_LSPLIT) nd.w = nd.w - fmark + base;
                    tr.F.insert(tr.F.end(), fA.begin(), fA.end());
                    T.insert(T.end(), subA.begin(), subA.end());
                    return vA;
                }
            }
            T[mark].dec = c == 0 ? D_DEC0 : D_DEC1; T[mark].w = w;
            traceNode(t, B, K, lvl, c == 0 ? "DEC0" : "DEC1", sampled ? &S : nullptr);
            i64 v = tryDec(t, c, B, rc, K, lvl);
            if (d.plus && v < INF) {
                if (canDrop && !better(v)) return toDrop();
                return v;
            }
            if (!d.plus && v < INF) return v;
            restore(mark, t); tr.F.resize(fmark);
            if (canDrop) return toDrop();
        }
        if (!sampled) samples(t, B, rc, K, S);
        int nOut = 0, nLoss = 0, nOther = 0;
        for (auto& s : S) { if (s.cls == 0) ++nOut; else if (s.cls == 4) ++nLoss; else ++nOther; }
        if (canDrop && nOut == 0 && nOther == 0) {
            // a pure loss region: split only when omega*'s slack is worth it
            double x[8] = {0, 0, 0, 0, 0, 0, 0, 0}, r = 1;
            for (int j = 0; j < B.n; ++j) x[j] = 0.5 * (B.lo[j] + B.hi[j]);
            for (auto& o : d.om) {
                double ob = (double)omegaBox(o.N, o.k, B) / SCW;
                double u = lfval(o.N, x) * DEN / x[o.k];
                double op = u < 1 ? 0 : u >= 3 ? (double)OMT_TOP / SCW : (double)OMT[std::min(1023, (int)(512 * (u - 1)))] / SCW;
                r *= ob > 0 ? op / ob : 1;
            }
            if ((double)drop / SC * (1 - r) <= EPS_SLACK || lvl >= MAXLVL) return toDrop();
            int j = chooseSplit(B, S);
            if (j < 0) return toDrop();
            CUTS[t][2]++;
            i64 v = cut(t, B, rc, K, lvl, mark, j, B.lo[j] + (B.hi[j] - B.lo[j]) / 2, excl);
            if (better(v)) return v;
            return toDrop();
        }
        if (lvl >= MAXLVL) {
            if (canDrop) return toDrop();
            { i64 v = lastResort(); if (v < INF) return v; }
            T.resize(mark); return INF;
        }
        bool done;
        curExcl = excl;
        i64 v = cutBySamples(t, B, rc, K, lvl, mark, S, false, PEELMIN, d.plus ? drop : 0, done);
        if (TRACE && canDrop && (double)drop / SC > TRACEMIN) {
            int nD = 0, nA = 0;
            for (auto& s : S) { if (s.cls == 1) ++nA; if (s.cls == 2 || s.cls == 3) ++nD; }
            printf("TRACE %s lvl %d cuts %d drop %.3e sub %.3e nodes %zu dec %d done %d samples out %d loss %d asym %d dec %d -> %s\n",
                   d.name.c_str(), lvl, K.n, (double)drop / SC, v >= INF ? -1.0 : (double)v / SC, T.size() - mark,
                   (int)T[mark].dec, (int)done, nOut, nLoss, nA, nD, (!done || (canDrop && !better(v))) ? "DROP" : "keep");
        }
        if (!done) {
            if (canDrop) return toDrop();
            { i64 v = lastResort(); if (v < INF) return v; }
            T.resize(mark); return INF;
        }
        if (canDrop && !better(v)) return toDrop();
        if (v >= INF) { { i64 w = lastResort(); if (w < INF) return w; } T.resize(mark); return INF; }
        return v;
    }
};

// ---------------- the verifier: exact checks only ----------------
struct Stats {
    long long cnt[NT_COUNT][10] = {{0}};
    i64 cost[NT_COUNT] = {0};
    long long tiiKinds[4] = {0}, tiiGrp[4] = {0}, tiiNg[12] = {0};
    long long vsParts = 0, maxCuts = 0, cutSum = 0, nodesWithCuts = 0;
};
static int WASTE = 0;
struct WasteAcc { double bound = 0, loss = 0, asym = 0, out = 0, dec = 0; };
static WasteAcc WA[NT_COUNT];
static double OUTBY[NT_COUNT][32];
static double LEAFLW[NT_COUNT]; static long long LEAFN[NT_COUNT], LEAFC[NT_COUNT];
static std::mutex WAmu;
struct Ver {
    double outBy[NT_COUNT][32] = {{0}};
    const Tree& tr;
    size_t pos = 0;
    Stats st;
    bool ok = true;
    std::string err;
    WasteAcc wa[NT_COUNT];
    Ver(const Tree& t) : tr(t) {}
    void fail(const char* m, NT t) { if (ok) { ok = false; err = std::string(m) + " at " + ND[t].name; } }
    double leafLogW[NT_COUNT] = {0}; long long leafN[NT_COUNT] = {0}, leafCut[NT_COUNT] = {0};
    void leafStat(NT t, const Box& B, const Cuts& K) {
        double lw = 0; int n = 0;
        for (int j = 2; j < B.n; ++j) { lw += std::log((double)std::max<i64>(1, B.hi[j] - B.lo[j]) / DEN); ++n; }
        if (n) { leafLogW[t] += lw / n; leafN[t]++; if (K.n) leafCut[t]++; }
    }
    i64 ver(NT t, Box B, const RootCtx& rc, const Cuts& K0) {
        if (pos >= tr.T.size()) { fail("tree ends", t); return 0; }
        const TNode& N = tr.T[pos++];
        if (N.type != t) { fail("type mismatch", t); return 0; }
        st.cnt[t][N.dec]++;
        const NodeDef& d = ND[t];
        bool in = tightenC(t, B, rc, K0);
        if (N.dec == D_OUT) { if (in && !outsideC(t, B, rc, K0)) fail("not outside", t); return 0; }
        if (!in) { fail("empty region with a decision", t); return 0; }
        const Cuts K = PRUNE ? pruneCuts(K0, B) : K0;
        if (K.n) { st.nodesWithCuts++; st.cutSum += K.n; st.maxCuts = std::max<long long>(st.maxCuts, K.n); }
        Act act;
        activesC(t, B, rc, K, act);
        const Act* saveAct = CUR_ACT;
        CUR_ACT = &act;
        struct Restore { const Act* s; ~Restore() { CUR_ACT = s; } } restore{saveAct};
        switch (N.dec) {
            case D_ASYM_G2:
                if (!checkG2(d.items, B, N.w & 0xffff, (N.w >> 16) & 0xffff)) fail("G2", t);
                leafStat(t, B, K);
                return 0;
            case D_ASYM_TII: {
                if (!checkTIIlin(d.items, B, N.w)) fail("TII", t);
                leafStat(t, B, K);
                int k = d.items.size(), mask[16] = {0}, ng = 0;
                for (int j = 0; j < k; ++j) { int g = (N.w >> (4 * j)) & 15; mask[g] |= 1 << j; ng = std::max(ng, g + 1); }
                int big = 0; bool hasR = false, hasRC = false;
                for (int g = 0; g < ng; ++g) {
                    big = std::max(big, __builtin_popcount(mask[g]));
                    for (int j = 0; j < k; ++j) if ((mask[g] >> j & 1) && d.items[j].rough) {
                        hasR = true;
                        if (lfmax(d.items[j].a - 2 * lfT(d.items[j].sift), B) >= 0) hasRC = true;
                    }
                }
                st.tiiNg[std::min(ng, 11)]++;
                st.tiiGrp[big >= 4 ? 3 : big - 1]++;
                st.tiiKinds[hasRC ? 3 : hasR ? 2 : big > 1 ? 1 : 0]++;
                return 0;
            }
            case D_DROP: {
                if (!d.plus) { fail("drop of a - node", t); return 0; }
                if (N.k1 < 1 || N.k2 < 1 || N.k1 > 64 || N.k2 > 64 || N.sc >= B.n || N.q2 >= B.n) { fail("bad virtual split", t); return 0; }
                long long p0 = WK_VSPARTS;
                i64 c = dropCostVS(t, B, rc, K, N.sc, N.k1, N.q2, N.k2);
                st.vsParts += WK_VSPARTS - p0;
                if (c >= ((i64)1 << 62)) fail("capped bound", t);
                st.cost[t] += c;
                if (WASTE) {
                    std::mt19937_64 rg(pos * 7919 + 13);
                    double vol = 1, acc[5] = {0, 0, 0, 0, 0};
                    for (int j = 0; j < B.n; ++j) vol *= (double)(B.hi[j] - B.lo[j]) / DEN;
                    for (int q = 0; q < WASTE; ++q) {
                        std::array<i64, 8> x{};
                        double xd[8] = {0, 0, 0, 0, 0, 0, 0, 0};
                        for (int j = 0; j < B.n; ++j) { x[j] = B.lo[j] + (i64)(rg() % (uint64_t)(B.hi[j] - B.lo[j])); xd[j] = x[j]; }
                        Samp s = classify(t, x, rc, Cuts());
                        // points outside the cuts belong to other nodes: count them as outside here
                        Box P; P.n = B.n; for (int j = 0; j < B.n; ++j) P.lo[j] = P.hi[j] = x[j];
                        bool inCuts = !pointOutsideC(t, P, rc, K);
                        double f = integrandPt(t, xd);
                        acc[!inCuts || s.cls == 0 ? 2 : s.cls == 4 ? 0 : s.cls == 1 ? 1 : 3] += f;
                        if (!inCuts || s.cls == 0) {
                            // attribute the outside mass to the first violated constraint: domain index, 30 region, 31+ cuts
                            int ci = -1, q = 0;
                            for (auto& c : d.dom) { i64 v = lfmin(c.L, P); if (c.lt ? v >= 0 : v < 0) { ci = q; break; } ++q; }
                            if (ci < 0 && t != NA2 && regionOutside(P, rc)) ci = 30;
                            if (ci < 0) for (int i = 0; i < K.n; ++i) { i64 v = lfmin(K.c[i].L, P); if (K.c[i].lt ? v >= 0 : v < 0) { ci = 31; break; } }
                            if (ci >= 0) outBy[t][ci] += f * vol / WASTE;
                        }
                    }
                    wa[t].bound += (double)c / SC;
                    wa[t].loss += acc[0] * vol / WASTE; wa[t].asym += acc[1] * vol / WASTE;
                    wa[t].out += acc[2] * vol / WASTE; wa[t].dec += acc[3] * vol / WASTE;
                    const char* dd = getenv("DUMPDROP");
                    if (dd && ND[t].name == dd) {
                        double inr = acc[0] + acc[1] + acc[3];
                        double fd = inr > 0 ? acc[3] / inr : 0, fa = inr > 0 ? acc[1] / inr : 0;
                        if ((fd > 0.25 || fa > 0.25) && (double)c / SC > atof(getenv("DUMPMIN") ? getenv("DUMPMIN") : "1e-7")) {
                            printf("DUMP %s cost %.3e loss %.2f asym %.2f dec %.2f cuts %d vs %d/%d,%d/%d box", d.name.c_str(), (double)c / SC,
                                   inr > 0 ? acc[0] / inr : 0, fa, fd, K.n, N.sc, N.k1, N.q2, N.k2);
                            for (int j = 0; j < B.n; ++j) printf(" %lld %lld", (long long)B.lo[j], (long long)B.hi[j]);
                            printf(" |");
                            for (int i = 0; i < K.n; ++i) {
                                printf(" %c", K.c[i].lt ? '<' : '>');
                                printf("%lld", (long long)K.c[i].L.c0);
                                for (int j = 0; j < B.n; ++j) printf(",%d", K.c[i].L.c[j]);
                            }
                            printf("\n");
                        }
                    }
                }
                return c;
            }
            case D_SPLIT: {
                int j = N.sc;
                if (j >= B.n || N.sp <= B.lo[j] || N.sp >= B.hi[j]) { fail("bad split", t); return 0; }
                Box L = B, R = B; L.hi[j] = N.sp; R.lo[j] = N.sp;
                i64 a = ver(t, L, rc, K);
                return a + ver(t, R, rc, K);
            }
            case D_LSPLIT: {
                if (N.w >= tr.F.size() || K.n >= MAXCUT) { fail("bad diagonal split", t); return 0; }
                const LF& L = tr.F[N.w];
                for (int j = B.n; j < MAXD; ++j) if (L.c[j]) { fail("diagonal split on a missing coordinate", t); return 0; }
                Cuts K1 = K, K2 = K;
                K1.c[K1.n++] = {L, true};
                K2.c[K2.n++] = {L, false};
                i64 a = ver(t, B, rc, K1);
                return a + ver(t, B, rc, K2);
            }
            case D_DEC0: case D_DEC1: {
                int c = N.dec == D_DEC0 ? 0 : 1;
                if (c >= (int)d.ch.size()) { fail("no such decomposition", t); return 0; }
                if (!checkDec(t, c, B, N.w)) fail("Type I", t);
                const Child& ch = d.ch[c];
                Box C = B; C.n = B.n + 1;
                i64 U = childUpper(ch.type, B);
                C.lo[B.n] = NU0; C.hi[B.n] = std::max(U, NU0 + 1);
                return ver(ch.type, C, rc, K);
            }
        }
        fail("bad decision", t);
        return 0;
    }
};

struct Root { NT t; Box B; RootCtx rc; };
static std::vector<Root> roots() {
    std::vector<Root> R;
    for (int k = CK0; k < CK1; ++k)
        for (int j = CJ0; j < CJ1; ++j) {
            Box B; B.n = 2;
            B.lo[0] = k * DG; B.hi[0] = (k + 1) * DG + 1;   // the Lean's cell: alpha1 in (k/G, (k + 1)/G]
            B.lo[1] = j * DG; B.hi[1] = (j + 1) * DG;
            RootCtx rc{rootBranch(k), rootH(k)};
            R.push_back({N2, B, rc});
        }
    for (int k = AK0; k < AK1; ++k)
        for (int j = AJ0; j < AJ1; ++j) {
            Box B; B.n = 2;
            B.lo[0] = k * DG; B.hi[0] = (k + 1) * DG;
            B.lo[1] = j * DG; B.hi[1] = (j + 1) * DG;
            R.push_back({NA2, B, {0, 0}});
        }
    for (int k = OK0; k < OK1; ++k)                          // the Lean's cells outside region C
        for (int j = OJ0; j < OJ1; ++j) {
            Box B; B.n = 2;
            B.lo[0] = k * DG; B.hi[0] = (k + 1) * DG + 1;
            B.lo[1] = j * DG; B.hi[1] = (j + 1) * DG;
            R.push_back({N2, B, {2 + rootBranch(k), rootH(k)}});
        }
    return R;
}

int main(int argc, char** argv) {
    initNodes();
    int threads = 2, r0 = 0, r1 = 1 << 30;
    std::string only = "N2";
    std::string treeOut = "";
    for (int a = 1; a < argc; ++a) {
        std::string s = argv[a];
        auto eq = s.find('=');
        std::string k = s.substr(0, eq), v = eq == std::string::npos ? "" : s.substr(eq + 1);
        if (k == "maxlvl") MAXLVL = atoi(v.c_str());
        else if (k == "minw") MINW = DEN >> atoi(v.c_str());
        else if (k == "nsamp") NSAMP = atoi(v.c_str());
        else if (k == "slack") EPS_SLACK = atof(v.c_str());
        else if (k == "peelmin") PEELMIN = atof(v.c_str());
        else if (k == "peelmin2") PEELMIN2 = atof(v.c_str());
        else if (k == "kappa") KQ = (i64)(atof(v.c_str()) * DEN);
        else if (k == "threads") threads = atoi(v.c_str());
        else if (k == "only") only = v;
        else if (k == "trace") TRACE = atoi(v.c_str());
        else if (k == "tracemin") TRACEMIN = atof(v.c_str());
        else if (k == "tracet") TRACET = strdup(v.c_str());
        else if (k == "tracemax") TRACEMAX = atoll(v.c_str());
        else if (k == "waste") WASTE = atoi(v.c_str());
        else if (k == "tandom") TANDOM = atoi(v.c_str()) != 0;
        else if (k == "pbf") PBF = atof(v.c_str());
        else if (k == "lambda") LAMBDA = atof(v.c_str());
        else if (k == "asymfrac") ASYMFRAC = atof(v.c_str());
        else if (k == "chainbound") CHAINBOUND = atoi(v.c_str());
        else if (k == "chainref") CHAINREF = atoi(v.c_str());
        else if (k == "diag") DIAG = atoi(v.c_str());
        else if (k == "filt") USEFILT = atoi(v.c_str());
        else if (k == "diagtii") DIAGTII = atoi(v.c_str());
        else if (k == "diagnzp") DIAGNZP = atoi(v.c_str());
        else if (k == "diagnzm") DIAGNZM = atoi(v.c_str());
        else if (k == "minin") MININ = atoi(v.c_str());
        else if (k == "covsel") COVSEL = atoi(v.c_str());
        else if (k == "prune") PRUNE = atoi(v.c_str());
        else if (k == "orthant") ORTHANT = atoi(v.c_str());
        else if (k == "pal") PAL = atoi(v.c_str());
        else if (k == "paln") PALN = atoi(v.c_str());
        else if (k == "palmax") PALMAX = atoi(v.c_str());
        else if (k == "palmin") PALMIN = atof(v.c_str());
        else if (k == "cornercut") CORNERCUT = atoi(v.c_str());
        else if (k == "maxdiag") MAXDIAG = atoi(v.c_str());
        else if (k == "diagpref") DIAGPREF = atof(v.c_str());
        else if (k == "vsmax") VSMAX = atoi(v.c_str());
        else if (k == "vsw") VSW = atof(v.c_str());
        else if (k == "altminus") ALTMINUS = atoi(v.c_str());
        else if (k == "altmin") ALTMIN = atof(v.c_str());
        else if (k == "n2drop") N2DROP = atoi(v.c_str());
        else if (k == "r0") r0 = atoi(v.c_str());
        else if (k == "r1") r1 = atoi(v.c_str());
        else if (k == "tree") treeOut = v;
        else { fprintf(stderr, "unknown parameter %s\n", k.c_str()); return 1; }
    }
    printf("cert3 lambda %.3g theta 1/2+1/%d kappa %.3g chainbound %d chainref %d diag %d maxdiag %d diagpref %.2f vsmax %d vsw %.2f "
           "altminus %d altmin %.2g peelmin %.3g minw 2^-%d\n", LAMBDA, (int)G, (double)KQ / DEN, CHAINBOUND, CHAINREF, DIAG, MAXDIAG,
           DIAGPREF, VSMAX, VSW, ALTMINUS, ALTMIN, PEELMIN, (int)std::round(std::log2((double)DEN / MINW)));
    auto R = roots();
    std::vector<Tree> trees(R.size());
    std::vector<i64> gcost(R.size(), 0);
    std::vector<double> gsec(R.size(), 0);
    std::atomic<int> next(0);
    auto t0 = std::chrono::steady_clock::now();
    std::vector<std::thread> th;
    for (int w = 0; w < threads; ++w) th.emplace_back([&]() {
        for (;;) {
            int i = next++;
            if (i >= (int)R.size()) break;
            if (!only.empty() && only != ND[R[i].t].name) continue;
            if (i < r0 || i >= r1) continue;
            auto s0 = std::chrono::steady_clock::now();
            Gen g(1234567 + i);
            Palette palette;
            if (PAL) { buildPalette(i, R[i].B, R[i].rc, palette, 99991 + i); g.pal = &palette; }
            gcost[i] = g.gen(R[i].t, R[i].B, R[i].rc, Cuts(), 0);
            trees[i] = std::move(g.tr);
            gsec[i] = std::chrono::duration<double>(std::chrono::steady_clock::now() - s0).count();
        }
    });
    for (auto& x : th) x.join();
    double gsecs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    WK = Work(); WK_LF = 0; WK_OM = 0; WK_LFA = 0; WK_LFS = 0; WK_CHAINOPS = 0; WK_VSPARTS = 0;
    Stats tot;
    i64 totalC = 0, totalA = 0, totalO = 0;
    long long nnodes = 0;
    bool allok = true;
    t0 = std::chrono::steady_clock::now();
    FILE* fr = getenv("ROOTLOG") ? fopen(getenv("ROOTLOG"), "w") : nullptr;
    for (size_t i = 0; i < R.size(); ++i) {
        bool selected = (only.empty() || only == ND[R[i].t].name) && (int)i >= r0 && (int)i < r1;
        if (selected && (trees[i].T.empty() || gcost[i] >= INF)) { allok = false; fprintf(stderr, "root %zu: not certified\n", i); }
        if (trees[i].T.empty()) continue;
        Ver v(trees[i]);
        i64 c = v.ver(R[i].t, R[i].B, R[i].rc, Cuts());
        if (!v.ok || v.pos != trees[i].T.size()) { allok = false; fprintf(stderr, "root %zu: %s\n", i, v.err.c_str()); }
        if (gcost[i] < INF && c != gcost[i]) { allok = false; fprintf(stderr, "root %zu: cost mismatch %lld %lld\n", i, (long long)c, (long long)gcost[i]); }
        (R[i].t == NA2 ? totalA : R[i].rc.branch >= 2 ? totalO : totalC) += c;
        nnodes += trees[i].T.size();
        if (fr) fprintf(fr, "%zu %d %.4f %.4f %.8f %zu %.1f %lld\n", i, (int)R[i].t, (double)R[i].B.lo[0] / DEN,
                        (double)R[i].B.lo[1] / DEN, (double)c / SC, trees[i].T.size(), gsec[i], (long long)c);
        for (int a = 0; a < NT_COUNT; ++a) for (int q = 0; q < 32; ++q) OUTBY[a][q] += v.outBy[a][q];
        for (int a = 0; a < NT_COUNT; ++a) { LEAFLW[a] += v.leafLogW[a]; LEAFN[a] += v.leafN[a]; LEAFC[a] += v.leafCut[a]; }
        for (int a = 0; a < NT_COUNT; ++a) {
            for (int b = 0; b < 10; ++b) tot.cnt[a][b] += v.st.cnt[a][b];
            tot.cost[a] += v.st.cost[a];
            WA[a].bound += v.wa[a].bound; WA[a].loss += v.wa[a].loss; WA[a].asym += v.wa[a].asym; WA[a].out += v.wa[a].out; WA[a].dec += v.wa[a].dec;
        }
        for (int a = 0; a < 4; ++a) { tot.tiiKinds[a] += v.st.tiiKinds[a]; tot.tiiGrp[a] += v.st.tiiGrp[a]; }
        for (int a = 0; a < 12; ++a) tot.tiiNg[a] += v.st.tiiNg[a];
        tot.vsParts += v.st.vsParts; tot.cutSum += v.st.cutSum; tot.nodesWithCuts += v.st.nodesWithCuts;
        tot.maxCuts = std::max(tot.maxCuts, v.st.maxCuts);
        if (!treeOut.empty()) {
            std::string fn = treeOut + "_" + std::to_string(i) + ".bin";
            FILE* ft = fopen(fn.c_str(), "wb");
            if (ft) {
                uint64_t nT = trees[i].T.size(), nF = trees[i].F.size();
                fwrite(&nT, 8, 1, ft); fwrite(trees[i].T.data(), sizeof(TNode), nT, ft);
                fwrite(&nF, 8, 1, ft); fwrite(trees[i].F.data(), sizeof(LF), nF, ft);
                fclose(ft);
            }
        }
    }
    if (fr) fclose(fr);
    if (WASTE) {
        printf("outside mass of dropped boxes by first violated constraint (domain index: mass; 30 region, 31 cuts):\n");
        for (int a = 0; a < NT_COUNT; ++a) {
            double tt = 0; for (int q = 0; q < 32; ++q) tt += OUTBY[a][q];
            if (tt <= 0) continue;
            printf("  %-6s", ND[a].name.c_str());
            for (int q = 0; q < 32; ++q) if (OUTBY[a][q] > 0.02 * tt) printf(" %d:%.2e", q, OUTBY[a][q]);
            printf("\n");
        }
        printf("waste analysis (dropped regions, %d points each): type bound | loss-part asym-part out-part dec-part (MC)\n", WASTE);
        for (int a = 0; a < NT_COUNT; ++a) if (WA[a].bound > 0)
            printf("  %-6s %.6f | %.6f %.6f %.6f %.6f\n", ND[a].name.c_str(), WA[a].bound, WA[a].loss, WA[a].asym, WA[a].out, WA[a].dec);
    }
    printf("asymptotic leaves: geometric mean width of the coordinates x2.. (and share with cuts):");
    for (int a = 0; a < NT_COUNT; ++a) if (LEAFN[a]) printf(" %s %.4f (%.0f%%)", ND[a].name.c_str(), std::exp(LEAFLW[a] / LEAFN[a]), 100.0 * LEAFC[a] / LEAFN[a]);
    printf("\n");
    double vsecs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    double C = (double)totalC / SC, A = (double)totalA / SC;
    printf("generation %.0fs, verification %.1fs, %lld nodes, verified %s\n", gsecs, vsecs, nnodes, allok ? "OK" : "FAILED");
    printf("C (exact, units 2^-50) = %lld = %.6f\n", (long long)totalC, C);
    printf("A (exact)              = %lld = %.6f\n", (long long)totalA, A);
    printf("outside C (exact)      = %lld = %.6f\n", (long long)totalO, (double)totalO / SC);
    printf("margin against 1 - 2*0.240227 = 0.519546: %.6f\n", 0.519546 - C);
    const char* dn[9] = {"out", "asymG2", "asymTII", "drop", "split", "dec0", "dec1", "fail", "dsplit"};
    printf("%-6s %9s %9s %9s %9s %9s %9s %9s %9s   cost\n", "type", dn[0], dn[1], dn[2], dn[3], dn[4], dn[5], dn[6], dn[8]);
    for (int a = 0; a < NT_COUNT; ++a) {
        long long s = 0;
        for (int b = 0; b < 9; ++b) s += tot.cnt[a][b];
        if (!s) continue;
        printf("%-6s", ND[a].name.c_str());
        for (int b : {0, 1, 2, 3, 4, 5, 6, 8}) printf(" %9lld", tot.cnt[a][b]);
        printf("   %.6f\n", (double)tot.cost[a] / SC);
    }
    printf("TII witnesses: primes only %lld, prime groups %lld, rough factor surely prime %lld, rough possibly composite %lld\n",
           tot.tiiKinds[0], tot.tiiKinds[1], tot.tiiKinds[2], tot.tiiKinds[3]);
    printf("TII largest group: 1: %lld, 2: %lld, 3: %lld, >=4: %lld;  factors:", tot.tiiGrp[0], tot.tiiGrp[1], tot.tiiGrp[2], tot.tiiGrp[3]);
    for (int a = 2; a < 12; ++a) if (tot.tiiNg[a]) printf(" %d:%lld", a, tot.tiiNg[a]);
    printf("\n");
    printf("cuts explored (peel, midpoint, slack, minus-peel, diagonal, alt-minus):");
    for (int a = 0; a < NT_COUNT; ++a) if (CUTS[a][0] + CUTS[a][1] + CUTS[a][2] + CUTS[a][3] + CUTS[a][4] + CUTS[a][5])
        printf(" %s %lld/%lld/%lld/%lld/%lld/%lld", ND[a].name.c_str(), CUTS[a][0].load(), CUTS[a][1].load(), CUTS[a][2].load(),
               CUTS[a][3].load(), CUTS[a][4].load(), CUTS[a][5].load());
    printf("\n");
    printf("root drops (last resort) %lld\n", (long long)ROOTDROPS);
    printf("kernel work: outside %lld, G2 %lld, TII %lld (f evals %lld), TypeI %lld, bounds %lld; linear forms %lld (domain-aware %lld), "
           "omega* %lld, chain DP steps %lld, virtual parts %lld; nodes with cuts %lld (mean %.2f cuts, max %lld); multiplier evaluations %lld\n",
           WK.out, WK.g2, WK.tii, WK.tiiGroups, WK.tyI, WK.bound, WK_LF, WK_LFA, WK_OM, WK_CHAINOPS, tot.vsParts, tot.nodesWithCuts,
           tot.nodesWithCuts ? (double)tot.cutSum / tot.nodesWithCuts : 0.0, tot.maxCuts, WK_LFS);
    return allok ? 0 : 2;
}
