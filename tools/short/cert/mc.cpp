// Monte Carlo of the true loss per root and per node type, with the certificate's own exact point classification
// (the same G2 / Type II / Type I searches as the generator, Li's order of decompositions) and the exact omega*.
// Floating point only for the weights; not part of the certificate.
//   ./mc r0 r1 N [threads] [seed]
#include "wit.h"
#include <random>
#include <thread>
#include <cmath>
#include <array>
#include <mutex>

static bool pointOutside(NT t, const Box& P, const RootCtx& rc) {
    for (auto& c : ND[t].dom) {
        i64 v = lfmin(c.L, P);
        if (c.lt ? v >= 0 : v < 0) return true;
    }
    return t != NA2 && regionOutside(P, rc);
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
// 0 out, 1 asym, 2 dec0, 3 dec1, 4 none
static int classify(NT t, const Box& P, const RootCtx& rc) {
    const NodeDef& d = ND[t];
    if (pointOutside(t, P, rc)) return 0;
    int M, R; uint64_t part;
    if (USE_G2 && searchG2(d.items, P, M, R)) return 1;
    if (USE_TII && searchTII(d.items, P, part)) return 1;
    for (int c = 0; c < (int)d.ch.size(); ++c) {
        uint64_t w;
        if (searchDec(t, c, P, w)) return 2 + c;
    }
    return 4;
}
static double omstar(double u) {
    if (u < 1) return 0;
    if (u < 2) return 1 / u;
    if (u <= 3) return (1 + std::log(u - 1)) / u;
    return 0.565073;
}
static double omtab(double u) {
    if (u < 1) return 0;
    if (u >= 3) return (double)OMT_TOP / SCW;
    return (double)OMT[std::min(1023, (int)(512 * (u - 1)))] / SCW;
}

int main(int argc, char** argv) {
    initNodes();
    int r0 = atoi(argv[1]), r1 = atoi(argv[2]);
    long N = atol(argv[3]);
    int nth = argc > 4 ? atoi(argv[4]) : 1;
    unsigned long long seed = argc > 5 ? strtoull(argv[5], 0, 10) : 1;
    for (int ri = r0; ri < r1; ++ri) {
        int k = CK0 + ri / (CJ1 - CJ0), j = CJ0 + ri % (CJ1 - CJ0);
        RootCtx rc{rootBranch(k), rootH(k)};
        double lo0 = (double)k / G, hi0 = (double)(k + 1) / G, lo1 = (double)j / G, hi1 = (double)(j + 1) / G;
        std::vector<double> S(NT_COUNT * nth, 0), Q(NT_COUNT * nth, 0), ST(NT_COUNT * nth, 0), UNR(nth, 0), MASS(NT_COUNT * nth * 5, 0);
        std::vector<std::thread> th;
        for (int w = 0; w < nth; ++w) th.emplace_back([&, w]() {
            std::mt19937_64 rng(seed * 1000003ULL + 7919ULL * w + 104729ULL * ri);
            std::uniform_real_distribution<double> U(0, 1);
            for (long s = w; s < N; s += nth) {
                double x[8] = {0, 0, 0, 0, 0, 0, 0, 0};
                x[0] = lo0 * std::exp(std::log(hi0 / lo0) * U(rng));
                x[1] = lo1 * std::exp(std::log(hi1 / lo1) * U(rng));
                double W = x[0] * std::log(hi0 / lo0) * x[1] * std::log(hi1 / lo1);
                NT t = N2;
                Box P; P.n = 2;
                for (int q = 0; q < 2; ++q) P.lo[q] = P.hi[q] = (i64)std::llround(x[q] * DEN);
                for (;;) {
                    int c = classify(t, P, rc);
                    {
                        const NodeDef& d0 = ND[t];
                        if (d0.plus && t != N2 && c != 0) {
                            double xd[8], xD[8];
                            for (int q = 0; q < 8; ++q) { xd[q] = q < P.n ? (double)P.lo[q] / DEN : 0; xD[q] = q < P.n ? (double)P.lo[q] : 0; }
                            double f = 1;
                            for (auto& o : d0.om) f *= omstar(lfval(o.N, xD) / xd[o.k]);
                            for (int q = 0; q < d0.dim; ++q) f *= d0.wt[q] == 0 ? 1 : d0.wt[q] == 1 ? 1 / xd[q] : 1 / (xd[q] * xd[q]);
                            MASS[(NT_COUNT * w + t) * 5 + c] += W * f;
                        }
                    }
                    if (c == 0 || c == 1) break;
                    const NodeDef& d = ND[t];
                    if (c == 4) {
                        if (!d.plus || t == N2) { UNR[w] += W; break; }
                        double f = 1, ft = 1;
                        double xd[8], xD[8];
                        for (int q = 0; q < 8; ++q) { xd[q] = q < P.n ? (double)P.lo[q] / DEN : 0; xD[q] = q < P.n ? (double)P.lo[q] : 0; }
                        for (auto& o : d.om) {
                            double u = lfval(o.N, xD) / xd[o.k];
                            f *= omstar(u); ft *= omtab(u);
                        }
                        double wt = 1;
                        for (int q = 0; q < d.dim; ++q) wt *= d.wt[q] == 0 ? 1 : d.wt[q] == 1 ? 1 / xd[q] : 1 / (xd[q] * xd[q]);
                        S[NT_COUNT * w + t] += W * f * wt; Q[NT_COUNT * w + t] += (W * f * wt) * (W * f * wt);
                        ST[NT_COUNT * w + t] += W * ft * wt;
                        break;
                    }
                    NT ch = d.ch[c - 2].type;
                    i64 Uc = childUpper(ch, P);
                    if (Uc <= NU0) break;
                    double a = (double)NU0 / DEN, b = (double)Uc / DEN;
                    double xn = a * std::exp(std::log(b / a) * U(rng));
                    i64 xi = (i64)std::llround(xn * DEN);
                    if (xi >= Uc) xi = Uc - 1;
                    if (xi < NU0) xi = NU0;
                    W *= xn * std::log(b / a);
                    P.lo[P.n] = P.hi[P.n] = xi; P.n++;
                    t = ch;
                }
            }
        });
        for (auto& x : th) x.join();
        double tot = 0, tott = 0, var = 0, unr = 0;
        printf("root %d (a1 [%.2f,%.2f) a2 [%.2f,%.2f)):", ri, lo0, hi0, lo1, hi1);
        for (int t = 0; t < NT_COUNT; ++t) {
            double s = 0, q = 0, st = 0;
            for (int w = 0; w < nth; ++w) { s += S[NT_COUNT * w + t]; q += Q[NT_COUNT * w + t]; st += ST[NT_COUNT * w + t]; }
            if (s == 0) continue;
            double m = s / N, se = std::sqrt(std::max(0.0, q / N - m * m) / N);
            tot += m; tott += st / N; var += se * se;
            printf(" %s %.6f(%.0f)", ND[t].name.c_str(), m, se * 1e6);
        }
        for (int w = 0; w < nth; ++w) unr += UNR[w];
        printf("  total %.6f(%.0f) table %.6f unresolved %.2e\n", tot, std::sqrt(var) * 1e6, tott, unr / N);
        if (getenv("MASS")) {
            for (int t = 0; t < NT_COUNT; ++t) {
                double m[5] = {0, 0, 0, 0, 0};
                for (int w = 0; w < nth; ++w) for (int c = 0; c < 5; ++c) m[c] += MASS[(NT_COUNT * w + t) * 5 + c] / N;
                if (m[1] + m[2] + m[3] + m[4] <= 0) continue;
                printf("   mass %s: asym %.5f dec0 %.5f dec1 %.5f loss %.5f\n", ND[t].name.c_str(), m[1], m[2], m[3], m[4]);
            }
        }
        fflush(stdout);
    }
}
