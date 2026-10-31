// Li's lower-bound loss pieces at a given theta (the 0.521 code with theta a parameter) (arXiv:2308.04458v8, ancillary LB_520_160_1/2.cpp), with the
// Type-II_n predicates (his Lemmas 4.2, 4.4, 4.5) in four variants:
//   V0  Li's predicates as published;
//   V1  Li's tuples, the last factor's threshold from Guth-Maynard's large values (delta_req_GM(D) < delta);
//   V2  V0, or any Hoelder tuple with real moments, Huxley's large values;
//   V3  V1, or any Hoelder tuple with real moments, Guth-Maynard's large values.
// Each piece is integrated by Monte Carlo in log coordinates, all variants on the same points.
#include "li_param.inc"
#include "dtables.h"
#include "li_tuples.h"
#include <random>
#include <cstdio>
#include <cstdlib>
#include <chrono>

thread_local int VARIANT = 0;
static double OMT = 1 - 0.52;

static inline double dreq(double D, bool gm) {           // least moment with a power saving, T = N^D
    if (D <= DT_D0) return gm ? DT_GM[0] : DT_HX[0];
    double x = (D - DT_D0) / DT_STEP;
    int i = (int)std::ceil(x - 1e-9);                     // the grid point above D: a conservative value
    if (i >= DT_N) return 1e9;
    return gm ? DT_GM[i] : DT_HX[i];
}
static inline double w_mv(double a) {                     // mean value theorem: an even moment with L^{delta/2} >= T
    if (a <= 0) return 0;
    double r = a / OMT;
    return 1.0 / (2 * std::ceil(1 / r - 1e-12));
}
static inline double w_ml(double a, bool gm) {            // the moment lemma: 1/delta for delta > delta_req
    if (a <= 0) return 0;
    return 1.0 / dreq(OMT / a, gm);
}
// Hoelder over n factors: one factor with the moment lemma (the saving), the others by the better of the two
thread_local bool DBG = false;
thread_local double DBG_A[8]; thread_local int DBG_N = 0, DBG_S = -1;
static bool gen_test(const double* a, int n, bool gm) {
    double any[8], ml[8], tot = 0;
    for (int j = 0; j < n; ++j) { ml[j] = w_ml(a[j], gm); any[j] = std::max(w_mv(a[j]), ml[j]); tot += any[j]; }
    for (int s = 0; s < n; ++s)
        if (tot - any[s] + ml[s] > 1 + 1e-12) {
            if (DBG) { DBG_N = n; DBG_S = s; for (int j = 0; j < n; ++j) DBG_A[j] = a[j]; }
            return true;
        }
    return false;
}
// Li's tuple with the last threshold from the moment lemma (GM): delta_req(D_last) < delta_last
static bool tuple_gm(const double* t, int n, const int* mid, int last) {
    if (t[0] < OMT) return false;
    for (int j = 0; j < n - 1; ++j) if (t[j + 1] < OMT / (mid[j] / 2.0)) return false;
    double l = 1; for (int j = 0; j < n; ++j) l -= t[j];
    return l > 0 && dreq(OMT / l, true) < last;
}
// the general test once per factor set: the explicit factors sorted down, the implicit one the smallest
static bool canonical(const double* t, int n, double l) {
    for (int j = 0; j + 1 < n; ++j) if (t[j] < t[j + 1]) return false;
    return l <= t[n - 1];
}

bool AsymptoticRegion3DL722(double t1, double t2, double t3) {
    if (Li3DL722(t1, t2, t3)) return true;
    if (VARIANT == 0) return false;
    double t[3] = {t1, t2, t3}, l = 1 - t1 - t2 - t3;
    if (VARIANT == 1 || VARIANT == 3)
        for (int k = 0; k < T3_N; ++k) if (tuple_gm(t, 3, T3_MID[k], T3_LAST[k])) return true;
    if ((VARIANT == 2 || VARIANT == 3) && canonical(t, 3, l)) {
        double a[4] = {t1, t2, t3, l};
        return gen_test(a, 4, VARIANT == 3);
    }
    return false;
}
bool AsymptoticRegion4DL722(double t1, double t2, double t3, double t4) {
    if (Li4DL722(t1, t2, t3, t4)) return true;
    if (VARIANT == 0) return false;
    double t[4] = {t1, t2, t3, t4}, l = 1 - t1 - t2 - t3 - t4;
    if (VARIANT == 1 || VARIANT == 3)
        for (int k = 0; k < T4_N; ++k) if (tuple_gm(t, 4, T4_MID[k], T4_LAST[k])) return true;
    if ((VARIANT == 2 || VARIANT == 3) && canonical(t, 4, l)) {
        double a[5] = {t1, t2, t3, t4, l};
        return gen_test(a, 5, VARIANT == 3);
    }
    return false;
}
bool AsymptoticRegion5DL722(double t1, double t2, double t3, double t4, double t5) {
    if (Li5DL722(t1, t2, t3, t4, t5)) return true;
    if (VARIANT == 0) return false;
    double t[5] = {t1, t2, t3, t4, t5}, l = 1 - t1 - t2 - t3 - t4 - t5;
    if (VARIANT == 1 || VARIANT == 3)
        for (int k = 0; k < T5_N; ++k) if (tuple_gm(t, 5, T5_MID[k], T5_LAST[k])) return true;
    if ((VARIANT == 2 || VARIANT == 3) && canonical(t, 5, l)) {
        double a[6] = {t1, t2, t3, t4, t5, l};
        return gen_test(a, 6, VARIANT == 3);
    }
    return false;
}


static double gamma_of(double th) {             // Lemma 4.1: max over g of gamma_g(theta)
    double best = -1;
    for (int g = 1; g <= 400; ++g) {
        double a = 4 * th - 2, b = ((8.0 * g - 4) * th - (4.0 * g - 3)) / (4.0 * g - 1);
        double c = (24.0 * g * th - (12.0 * g + 1)) / (4.0 * g - 1);
        best = std::max(best, std::min(a, std::min(b, c)));
    }
    return best;
}


// U_C05: the U_C03 branch (alpha4 in D*) with alpha6 in D**, two more Buchstab steps
static bool RegionUC05(const double* t) {
    double th0 = 2 * TH - 1, t1 = t[0], t2 = t[1], t3 = t[2], t4 = t[3], t5 = t[4], t6 = t[5];
    return ((t1 < 0.4 && t2 < min(t1, 1.0 / 3 * (1 - t1))) || (t1 >= 0.4 && t2 < 0.5 * t1))
        && !belowNu(t1, t2) && !AsymptoticRegion2DAll(t1, t2) && !AsymptoticRegion3DAll(t1, t2, t3) && !AsymptoticRegion4DAll(t1, t2, t3, t4)
        && TypeIRegion3D(t1, t2, t3) && TypeIRegion5D(t1, t2, t3, t4, t4)
        && !AsymptoticRegion5DAll(t1, t2, t3, t4, t5) && !AsymptoticRegion6DAll(t1, t2, t3, t4, t5, t6)
        && TypeIRegion7D(t1, t2, t3, t4, t5, t6, t6) && t[7] >= th0;
}
// U_C06: the U_C04 branch (alpha4 in D-double-dagger) with alpha6-dagger in D**
static bool RegionUC06(const double* t) {
    double t1 = t[0], t2 = t[1], t3 = t[2], t4 = t[3], t5 = t[4], t6 = t[5];
    return ((t1 < 0.4 && t2 < min(t1, 1.0 / 3 * (1 - t1))) || (t1 >= 0.4 && t2 < 0.5 * t1))
        && !belowNu(t1, t2) && !AsymptoticRegion2DAll(t1, t2) && !AsymptoticRegion3DAll(t1, t2, t3) && !AsymptoticRegion4DAll(t1, t2, t3, t4)
        && TypeIRegion3D(t1, t2, t3) && !TypeIRegion5D(t1, t2, t3, t4, t4)
        && (TypeIRegion5D(t1, t2, t3, t4, 0) && TypeIRegion5D(1 - t1 - t2 - t3 - t4, t2, t3, t4, 0))
        && !AsymptoticRegion5DAll(t1, t2, t3, t4, t5) && !AsymptoticRegion6DAll(1 - t1 - t2 - t3 - t4 - t5, t2, t3, t4, t5, t6)
        && TypeIRegion7D(1 - t1 - t2 - t3 - t4 - t5, t2, t3, t4, t5, t6, t6);
}
// U_C07: the U_C04 branch with alpha6-dagger not in D** and alpha6-dagger-prime in D**
static bool RegionUC07(const double* t) {
    double t1 = t[0], t2 = t[1], t3 = t[2], t4 = t[3], t5 = t[4], t6 = t[5];
    return ((t1 < 0.4 && t2 < min(t1, 1.0 / 3 * (1 - t1))) || (t1 >= 0.4 && t2 < 0.5 * t1))
        && !belowNu(t1, t2) && !AsymptoticRegion2DAll(t1, t2) && !AsymptoticRegion3DAll(t1, t2, t3) && !AsymptoticRegion4DAll(t1, t2, t3, t4)
        && TypeIRegion3D(t1, t2, t3) && !TypeIRegion5D(t1, t2, t3, t4, t4)
        && (TypeIRegion5D(t1, t2, t3, t4, 0) && TypeIRegion5D(1 - t1 - t2 - t3 - t4, t2, t3, t4, 0))
        && !AsymptoticRegion5DAll(t1, t2, t3, t4, t5) && !AsymptoticRegion6DAll(1 - t1 - t2 - t3 - t4 - t5, t2, t3, t4, t5, t6)
        && !TypeIRegion7D(1 - t1 - t2 - t3 - t4 - t5, t2, t3, t4, t5, t6, t6) && TypeIRegion7D(t1 - t6, t2, t3, t4, t5, t6, t5);
}
static double integrandUC(int p, const double* t) {
    double s5 = 1 - t[0] - t[1] - t[2] - t[3] - t[4];
    if (p == 8) {
        if (!RegionUC05(t)) return 0;
        double s8 = s5 - t[5] - t[6] - t[7];
        return omega1(s8 / t[7]) / (t[0] * t[1] * t[2] * t[3] * t[4] * t[5] * t[6] * t[7] * t[7]);
    }
    if (p == 9) {
        if (!RegionUC06(t)) return 0;
        return omega1((t[0] - t[5] - t[6] - t[7]) / t[7]) * omega1(s5 / t[4])
             / (t[1] * t[2] * t[3] * t[4] * t[4] * t[5] * t[6] * t[7] * t[7]);
    }
    if (!RegionUC07(t)) return 0;
    return omega1((t[0] - t[5]) / t[5]) * omega1((s5 - t[6] - t[7]) / t[7])
         / (t[1] * t[2] * t[3] * t[4] * t[5] * t[5] * t[6] * t[7] * t[7]);
}

// draw t log-uniformly in [lo, hi): returns the weight t log(hi/lo), or 0 if the interval is empty
static inline double draw(double lo, double hi, double u, double& t) {
    if (!(hi > lo)) return 0;
    double L = std::log(hi / lo);
    t = lo * std::exp(L * u);
    return t * L;
}

// sample piece p inside its domain (the range conditions of Li's Region functions); returns the weight
static double sample(int p, double* u, double* t) {
    if (p >= 8) {                                   // U_C05, U_C06, U_C07
        const double v0 = 2 * TH - 1;
        double W = draw(v0, 0.5, u[0], t[0]); if (!W) return 0;
        double U2 = std::min(t[0], 0.5 * (1 - t[0]));
        U2 = t[0] < 0.4 ? std::min(U2, (1 - t[0]) / 3) : std::min(U2, 0.5 * t[0]);
        W *= draw(v0, U2, u[1], t[1]); if (!W) return 0;
        W *= draw(v0, std::min(t[1], 0.5 * (1 - t[0] - t[1])), u[2], t[2]); if (!W) return 0;
        double s3 = 1 - t[0] - t[1] - t[2];
        W *= draw(v0, std::min(t[2], 0.5 * s3), u[3], t[3]); if (!W) return 0;
        double s4 = s3 - t[3];
        W *= draw(v0, std::min(t[3], 0.5 * s4), u[4], t[4]); if (!W) return 0;
        double s5 = s4 - t[4];
        if (p == 8) {
            W *= draw(v0, std::min(t[4], 0.5 * s5), u[5], t[5]); if (!W) return 0;
            double s6 = s5 - t[5];
            W *= draw(v0, std::min(t[5], 0.5 * s6), u[6], t[6]); if (!W) return 0;
            return W * draw(v0, std::min(t[6], 0.5 * (s6 - t[6])), u[7], t[7]);
        }
        W *= draw(v0, 0.5 * t[0], u[5], t[5]); if (!W) return 0;
        if (p == 9) {
            W *= draw(v0, std::min(t[5], 0.5 * (t[0] - t[5])), u[6], t[6]); if (!W) return 0;
            return W * draw(v0, std::min(t[6], 0.5 * (t[0] - t[5] - t[6])), u[7], t[7]);
        }
        W *= draw(v0, std::min(t[4], 0.5 * s5), u[6], t[6]); if (!W) return 0;
        return W * draw(v0, std::min(t[6], 0.5 * (s5 - t[6])), u[7], t[7]);
    }
    const double v0 = 2 * TH - 1;
    double W = draw(v0, 0.5, u[0], t[0]); if (!W) return 0;
    if (p == 7) {                                   // region A
        W = draw(0.25, 0.4, u[0], t[0]);
        return W * draw((1 - t[0]) / 3, std::min(t[0], 1 - 2 * t[0]), u[1], t[1]);
    }
    double U2 = std::min(t[0], 0.5 * (1 - t[0]));
    U2 = t[0] < 0.4 ? std::min(U2, (1 - t[0]) / 3) : std::min(U2, 0.5 * t[0]);
    W *= draw(v0, U2, u[1], t[1]); if (!W) return 0;
    W *= draw(v0, std::min(t[1], 0.5 * (1 - t[0] - t[1])), u[2], t[2]); if (!W) return 0;
    double s3 = 1 - t[0] - t[1] - t[2];
    if (p <= 2) {
        W *= draw(v0, std::min(t[2], 0.5 * s3), u[3], t[3]); if (!W) return 0;
        if (p == 0) return W;
        double s4 = s3 - t[3];
        W *= draw(v0, std::min(t[3], 0.5 * s4), u[4], t[4]); if (!W) return 0;
        if (p == 1) return W * draw(v0, std::min(t[4], 0.5 * (s4 - t[4])), u[5], t[5]);
        return W * draw(v0, 0.5 * t[0], u[5], t[5]);
    }
    W *= draw(v0, 0.5 * t[0], u[3], t[3]); if (!W) return 0;
    if (p == 3) return W;
    if (p == 4) {
        W *= draw(t[3], 0.5 * (t[0] - t[3]), u[4], t[4]); if (!W) return 0;
        return W * draw(t[2], 0.5 * s3, u[5], t[5]);
    }
    if (p == 5) {
        W *= draw(v0, std::min(t[3], 0.5 * (t[0] - t[3])), u[4], t[4]); if (!W) return 0;
        return W * draw(v0, std::min(t[4], 0.5 * (t[0] - t[3] - t[4])), u[5], t[5]);
    }
    W *= draw(v0, std::min(t[2], 0.5 * s3), u[4], t[4]); if (!W) return 0;
    return W * draw(v0, std::min(t[4], 0.5 * (s3 - t[4])), u[5], t[5]);
}

static double integrand(int p, const double* t) {
    switch (p) {
        case 0: return integrandC4DLoss(t[0], t[1], t[2], t[3]);
        case 1: return integrandC6DLoss1(t[0], t[1], t[2], t[3], t[4], t[5]);
        case 2: return integrandC6DLoss2(t[0], t[1], t[2], t[3], t[4], t[5]);
        case 3: return integrandC4DRRLoss(t[0], t[1], t[2], t[3]);
        case 4: return integrandC6DRRLoss1(t[0], t[1], t[2], t[3], t[4], t[5]);
        case 5: return integrandC6DRRLoss2(t[0], t[1], t[2], t[3], t[4], t[5]);
        case 6: return integrandC6DRRLoss3(t[0], t[1], t[2], t[3], t[4], t[5]);
        case 7: return integrandA2DLoss(t[0], t[1]);
        default: return integrandUC(p, t);
    }
}

int main(int argc, char** argv) {
    long N = argc > 1 ? atol(argv[1]) : 200000;
    int nth = argc > 2 ? atoi(argv[2]) : 4;
    const char* only = argc > 3 ? argv[3] : "all";
    unsigned long long seed = argc > 4 ? strtoull(argv[4], 0, 10) : 12345;
    TH = argc > 5 ? atof(argv[5]) : 0.521; GAMMA = gamma_of(TH); OMT = 1 - TH;
    printf("theta %.4f  nu0 %.4f  gamma %.6f  N %ld\n", TH, 2 * TH - 1, GAMMA, N); fflush(stdout);
    const char* names[11] = {"C4DLoss", "C6DLoss1", "C6DLoss2", "C4DRRLoss", "C6DRRLoss1", "C6DRRLoss2", "C6DRRLoss3", "A2DLoss",
                             "UC05", "UC06", "UC07"};
    const bool monotone[11] = {true, true, true, true, false, true, true, true, true, true, true};
    double tot[4] = {0}, totvar[4] = {0};
    for (int p = 0; p < 11; ++p) {
        if (std::string(only) != "all" && std::string(only) != names[p]) continue;
        auto t0 = std::chrono::steady_clock::now();
        std::vector<double> S(4 * nth, 0), Q(4 * nth, 0), DS(4 * nth, 0), DQ(4 * nth, 0);
        std::vector<std::thread> th;
        for (int w = 0; w < nth; ++w) th.emplace_back([&, w]() {
            std::mt19937_64 rng(seed * 1000003ULL + 7919ULL * w + 104729ULL * p);
            std::uniform_real_distribution<double> U(0, 1);
            for (long k = w; k < N; k += nth) {
                double u[8], t[8] = {0, 0, 0, 0, 0, 0, 0, 0};
                for (int i = 0; i < 8; ++i) u[i] = U(rng);
                double W = sample(p, u, t), f[4] = {0, 0, 0, 0};
                if (W > 0) {
                    VARIANT = 0; f[0] = W * integrand(p, t);
                    for (int v = 1; v < 4; ++v) {
                        if (p == 7) { f[v] = f[0]; continue; }
                        if (monotone[p] && f[0] == 0) { f[v] = 0; continue; }
                        VARIANT = v; f[v] = W * integrand(p, t);
                    }
                }
                for (int v = 0; v < 4; ++v) {
                    S[4 * w + v] += f[v]; Q[4 * w + v] += f[v] * f[v];
                    double d = f[0] - f[v]; DS[4 * w + v] += d; DQ[4 * w + v] += d * d;
                }
            }
        });
        for (auto& x : th) x.join();
        double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        printf("%-11s (%4.0fs):", names[p], secs);
        for (int v = 0; v < 4; ++v) {
            double s = 0, q = 0, ds = 0, dq = 0;
            for (int w = 0; w < nth; ++w) { s += S[4 * w + v]; q += Q[4 * w + v]; ds += DS[4 * w + v]; dq += DQ[4 * w + v]; }
            double m = s / N, se = std::sqrt(std::max(0.0, q / N - m * m) / N);
            double dm = ds / N, dse = std::sqrt(std::max(0.0, dq / N - dm * dm) / N);
            if (p != 4 && p != 7) { tot[v] += m; totvar[v] += se * se; }
            if (v == 0) printf("  V0 %.5f+-%.5f", m, se);
            else printf("  V%d -%.5f+-%.5f", v, dm, dse);
        }
        printf("\n"); fflush(stdout);
    }
    printf("C total    ");
    for (int v = 0; v < 4; ++v) printf("  V%d %.5f+-%.5f", v, tot[v], std::sqrt(totvar[v]));
    printf("\n");
    return 0;
}
