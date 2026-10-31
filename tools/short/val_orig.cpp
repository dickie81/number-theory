#include "li521_orig.inc"
#include <string>
double TH = 0.521;

#include <random>
#include <cstdio>
// draw t log-uniformly in [lo, hi): returns the weight t log(hi/lo), or 0 if the interval is empty
static inline double draw(double lo, double hi, double u, double& t) {
    if (!(hi > lo)) return 0;
    double L = std::log(hi / lo);
    t = lo * std::exp(L * u);
    return t * L;
}

// sample piece p inside its domain (the range conditions of Li's Region functions); returns the weight
static double sample(int p, double* u, double* t) {
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
        default: return integrandA2DLoss(t[0], t[1]);
    }
}


int main() {
    long Ns[8] = {20000, 4000, 20000, 20000, 4000, 20000, 20000, 20000};
    for (int p = 0; p < 8; ++p) {
        std::mt19937_64 rng(4242 + p); std::uniform_real_distribution<double> U(0, 1);
        double sum = 0; long nz = 0;
        for (long k = 0; k < Ns[p]; ++k) {
            double u[6], t[6] = {0, 0, 0, 0, 0, 0};
            for (int i = 0; i < 6; ++i) u[i] = U(rng);
            double W = sample(p, u, t); if (!W) continue;
            double f = integrand(p, t); sum += W * f; nz += f != 0;
        }
        printf("%d %.12g %ld\n", p, sum / Ns[p], nz);
    }
}
