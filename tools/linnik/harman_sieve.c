/* harman_sieve.c: a Harman decomposition for the least prime in a progression that does not lean on the window.
 * Compiled and driven by harman_sieve.py, which also states what is computed and what is assumed.
 *
 * Exponents are in base x = q^L; tau = 1/L, theta = 1 - tau.  A node is a set of k atoms (primes, or a sifted
 * number flagged in `npm`) with product r, and the term S(A_r, x^lam): the n = r m in A with every prime factor of
 * m at least x^lam.  mu, the exponent of the cofactor m, is 1 minus the atoms'.  In the main tree lam is the
 * exponent of the last prime.  Terms carry a sign: `odd` nodes need an upper bound, the others a lower bound.
 *
 * The exponents of the atoms are affine in independent cells (a flip makes the old cofactor an atom, with exponent
 * 1 minus the others), and the table of a node gives, for every set of atoms, the exact range [Slo, Shi] of their
 * sum over the box of cells.  Every test holds, and every cost is taken, on the whole box:
 *
 *   evaluable    one choice of parts A, B and rest R is a two-factor (or window) Type II configuration at every
 *                point: A in the zone [Alo(rho), Ahi(rho)] of the rest, the cofactor in B or in the rest;
 *   capacity T   the products r P, P < x^T, are in the reach of the Type I estimates (plain, bilinear, and with
 *                `wide` the bilinear estimate without the condition 2HD < q);
 *   exact floor  the largest f at which Harman's comparison evaluates S(A_r, x^f): its tree over the primes below
 *                x^f is stopped by a Type II configuration (rest a set of atoms, or the first small prime, or the
 *                window) before a leaf leaves the capacity;
 *   cost         0 if evaluable, or if the exact floor reaches lam; else the least of
 *                  - (lower bounds) the B-version of the term: it is dropped;
 *                  - the cost of the children with their prime in [f, lam), f the exact floor;
 *                  - the same from a higher floor f, plus the loss of a linear sieve of level x^T for S(A_r, x^f):
 *                    e^{-gamma} F(T/f) - omega (upper bounds) or omega - e^{-gamma} f(T/f) (lower bounds), over f,
 *                    with omega = omega(mu / f) the density of S(B_r, x^f);
 *                  - (upper bounds) an upper-bound sieve of level x^kappa on a prime p_j: 2 a_j / kappa - 1 times
 *                    the B-version;
 *                  - a flip: the same numbers are r' k with r' = (r / p_j) m and k = p_j a prime, the term
 *                    S(A_{r'}, x^{a_j / 2}), whose tree runs over the prime factors of k.
 * The value of a node is an upper bound for its cost density on the box, relative to prod d a_i / a_i over the
 * independent cells.  With `pointwise`, each cell is replaced by its midpoint: the limit of fine cells, a model.
 */
#include <math.h>
#include <stdlib.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif

#define MAXK 11
#define INF 1e300
#define BIG 1e200
#define UPEAK 2.7632228          /* omega increases on [2, UPEAK], to OMPEAK, and stays above OMMIN beyond */
#define OMPEAK 0.567144
#define OMMIN 0.560822
#define EG 0.5614594835668851    /* e^{-gamma}, the limit of omega */

typedef struct {
    double tau, theta, eps1;
    int wide;
    int NR;
    double DL;
    const double *Alo, *Ahi;
    double rmax, amin, amax;
    const double *f0hi, *f0t;
    const int *f0ok;
    int f0lo;
    int haswin;
    double u1, u2;
    int NW;
    double DW;
    const double *om;
    int NS;
    double DS;
    const double *Fm1, *omf;
    double step[MAXK + 2];
    int maxdepth;
    int use_ub, use_lb, use_rev;
    double fmin, smax;
    int flip, flipdepth, flipmax;
    double flipmin;
    double wmin;
    int split, splitdepth;
    int pointwise;
    int rev_odd, rev_even, rev_prime, rev_linear, rev_floor, rev_offdiag;
} Ctx;

typedef struct {
    long nodes[MAXK + 2];
} Stats;

static inline double omega(const Ctx *c, double u) {
    if (u < 1) return 0;
    double x = (u - 1) / c->DW;
    int i = (int)x;
    if (i >= c->NW - 1) return c->om[c->NW - 1];
    double f = x - i;
    return c->om[i] * (1 - f) + c->om[i + 1] * f;
}

/* The largest value of omega on [ulo, uhi]. */
static inline double omega_max(const Ctx *c, double ulo, double uhi) {
    if (uhi < 1) return 0;
    if (ulo == uhi) return omega(c, uhi);
    if (ulo < 1) ulo = 1;
    if (uhi <= 2) return 1 / ulo;
    double m = ulo < 2 ? 1 / ulo : 0;
    double v = uhi <= UPEAK ? omega(c, uhi) + 1e-6 : OMPEAK;
    return m > v ? m : v;
}

/* The least value of omega on [ulo, uhi]. */
static inline double omega_min(const Ctx *c, double ulo, double uhi) {
    if (ulo == uhi) return omega(c, ulo);
    if (ulo < 1) return 0;
    if (uhi <= 2) return 1 / uhi;
    double m = ulo < 2 ? 0.5 : omega(c, ulo) - 1e-6;
    if (uhi > UPEAK && m > OMMIN) m = OMMIN;
    return m;
}

/* The largest value of a decreasing table at s >= slo. */
static inline double tab(const double *t, int n, double ds, double s) {
    double x = s / ds;
    int i = (int)x;
    if (i >= n - 1) return t[n - 1];
    if (i < 0) return t[0];
    return t[i];
}

/* The zone valid for every rest in [rlo, rhi]: Alo and Ahi decrease as the rest grows. */
static inline int zone(const Ctx *c, double rlo, double rhi, double *zl, double *zh) {
    if (rlo < c->DL || rhi > c->rmax) return 0;
    int i = (int)floor(rlo / c->DL), j = (int)ceil(rhi / c->DL);
    if (i < 1 || j > c->NR) return 0;
    double l = c->Alo[i], h = c->Ahi[j];
    if (!(l <= h)) return 0;
    *zl = l;
    *zh = h;
    return 1;
}

/* The loss of the linear sieve of level x^T for S(A_r, x^f), per unit of prod d a_i / a_i: the sieve's bound has
 * the main term e^{-gamma} F(s) / f (upper) or e^{-gamma} f(s) / f (lower), s = T / f, where the B-version has
 * omega(mu / f) / f. */
static inline double penalty(const Ctx *c, int odd, double T, double f, double mulo, double muhi) {
    double s = T / f, v;
    if (odd) v = EG * (1 + tab(c->Fm1, c->NS, c->DS, s)) - omega_min(c, mulo / f, muhi / f);
    else v = omega_max(c, mulo / f, muhi / f) - EG * (1 - tab(c->omf, c->NS, c->DS, s));
    return (v > 0 ? v : 0) / f;
}

static int evaluable(const Ctx *c, int k, const double *Slo, const double *Shi) {
    int full = (1 << k) - 1;
    double zl, zh;
    for (int A = 1; A <= full; A++) {
        double lo = Slo[A], hi = Shi[A];
        if (c->haswin && ((lo > c->u1 && hi < c->u2) || (lo > 1 - c->u2 && hi < 1 - c->u1))) return 1;
        if (hi < c->amin || lo > c->amax) continue;
        int comp = full ^ A;
        for (int R = comp;; R = (R - 1) & comp) {
            if (R && zone(c, Slo[R], Shi[R], &zl, &zh) && lo >= zl && hi <= zh) return 1;
            /* the cofactor in the rest: rho = 1 - S[all but R] */
            if (zone(c, 1 - Shi[full ^ R], 1 - Slo[full ^ R], &zl, &zh) && lo >= zl && hi <= zh) return 1;
            if (!R) break;
        }
    }
    return 0;
}

static double capacity(const Ctx *c, int k, const double *Shi, int linear) {
    int full = (1 << k) - 1;
    if (linear) return c->theta - c->eps1 - Shi[full];   /* the linear Type I estimate alone: r P < x^theta */
    double th = c->theta - c->eps1, one = 1 - c->eps1, W = 2 - c->tau - c->eps1, best = -1;
    for (int S1 = 0; S1 <= full; S1++) {
        double a1 = Shi[S1], a2 = Shi[full ^ S1];
        if (a1 >= th) continue;
        double t = one - a1 - 2 * a2;
        if (c->wide) {
            double tA = W - c->tau - a1 - 2 * a2, tw;
            if (a1 < c->tau && tA <= c->tau - a1) tw = tA;
            else tw = (W - 2 * a1 - 2 * a2) / 2;
            if (tw > t) t = tw;
        }
        if (t > th - a1) t = th - a1;
        if (t > best) best = t;
        double t2 = (one - a1 - 2 * a2) / 2;
        if (c->wide) {
            double m = a1 > c->tau ? a1 : c->tau, tw = (W - m - a1 - 2 * a2) / 2;
            if (tw > t2) t2 = tw;
        }
        if (t2 > best) best = t2;
    }
    return best;
}

static int f0_rule(const Ctx *c, int k, const double *Slo, const double *Shi, int idx, double f, double T) {
    if (idx < 1 || idx > c->NR || !c->f0ok[idx]) return 0;
    double hi = c->f0hi[idx], m = 0;
    int full = (1 << k) - 1;
    for (int A = 1; A <= full; A++)
        if (Shi[A] <= hi && Slo[A] > m) m = Slo[A];
    double t = c->f0t[idx] - m;
    if (t < f) t = f;
    return t < T;
}

/* The largest f <= cap at which S(A_r, x^f) is evaluated at every point of the box; -1 if there is none. */
static double exact_floor(const Ctx *c, int k, const double *Slo, const double *Shi, double cap, double T) {
    if (T <= 0) return -1;
    int full = (1 << k) - 1;
    double best = -1, zl, zh;
    for (int R = 1; R <= full; R++) {
        if (!zone(c, Slo[R], Shi[R], &zl, &zh)) continue;
        double wdt = zh - zl;
        if (wdt <= best) continue;
        int comp = full ^ R;
        double m = 0;
        for (int A = comp; A; A = (A - 1) & comp)
            if (Shi[A] <= zh && Slo[A] > m) m = Slo[A];
        if (zl - m < T) best = wdt;
    }
    if (c->haswin && c->u2 - c->u1 > best) {
        double m1 = 0, m2 = 0;
        for (int A = 1; A <= full; A++) {
            if (Shi[A] < c->u2 && Slo[A] > m1) m1 = Slo[A];
            if (Shi[A] < 1 - c->u1 && Slo[A] > m2) m2 = Slo[A];
        }
        if (c->u1 - m1 < T || 1 - c->u2 - m2 < T) best = c->u2 - c->u1;
    }
    if (best >= cap) return cap;
    int itop = (int)ceil(cap / c->DL);
    if (f0_rule(c, k, Slo, Shi, itop, cap, T)) return cap;
    int lo = best > 0 ? (int)ceil(best / c->DL) : 1, hi = (int)floor(cap / c->DL);
    if (lo < c->f0lo) lo = c->f0lo;
    if (hi > c->NR) hi = c->NR;
    if (lo > hi || !f0_rule(c, k, Slo, Shi, lo, lo * c->DL, T)) return best;
    while (lo < hi) {
        int mid = (lo + hi + 1) / 2;
        if (f0_rule(c, k, Slo, Shi, mid, mid * c->DL, T)) lo = mid;
        else hi = mid - 1;
    }
    double f = lo * c->DL;
    return f > best ? f : best;
}

/* An upper-bound sieve on the prime p_j: the largest factor 2 a_j / kappa - 1 over the box. */
static double reversal(const Ctx *c, int k, const double *Slo, const double *Shi, int npm) {
    int full = (1 << k) - 1;
    double th = c->theta - c->eps1, one = 1 - c->eps1, W = 2 - c->tau - c->eps1, best = INF;
    for (int j = 0; j < k; j++) {
        if (npm >> j & 1) continue;
        int bj = 1 << j, O = full ^ bj;
        double kap = -1;
        for (int S1 = O;; S1 = (S1 - 1) & O) {
            for (int mf = 0; mf < 2; mf++) {
                /* the cofactor on side 1 (mf) or on side 2: its sum with a set is 1 minus the other atoms */
                double a1 = mf ? 1 - Slo[(O ^ S1) | bj] : Shi[S1];
                double a2 = mf ? Shi[O ^ S1] : 1 - Slo[S1 | bj];
                if (a1 >= th) continue;
                double room = one - a1 - 2 * a2;
                if (room >= 0) {
                    double k1 = th - a1 < room ? th - a1 : room, tot = k1 + (room - k1) / 2;
                    if (tot > kap) kap = tot;
                }
                if (c->wide) {
                    if (a1 >= c->tau) {
                        double tot = (W - 2 * a1 - 2 * a2) / 2;
                        if (tot > kap) kap = tot;
                    } else {
                        double X = W - c->tau - a1 - 2 * a2;
                        if (X >= 0) {
                            double k1 = c->tau - a1 < X ? c->tau - a1 : X, tot = k1 + (X - k1) / 2;
                            if (tot > kap) kap = tot;
                        }
                    }
                }
            }
            if (!S1) break;
        }
        if (kap > Slo[bj]) kap = Slo[bj];
        if (kap > 1e-6) {
            double fac = 2 * Shi[bj] / kap - 1;
            if (fac < best) best = fac;
        }
    }
    return best;
}

static double node(const Ctx *c, int k, double *Slo, double *Shi, double llo, double lhi, int odd, int npm,
                   int std, int fl, Stats *st);

/* The cost of the child whose new prime has its exponent in [qlo, qhi], split in two where that helps. */
static double child(const Ctx *c, int k, double *Slo, double *Shi, double qlo, double qhi, int odd, int npm, int std,
                    int fl, int split, Stats *st) {
    int bit = 1 << k;
    if (c->pointwise) qlo = qhi = (qlo + qhi) / 2;
    for (int m = 0; m < bit; m++) {
        Slo[m | bit] = Slo[m] + qlo;
        Shi[m | bit] = Shi[m] + qhi;
    }
    double v = node(c, k + 1, Slo, Shi, qlo, qhi, odd, npm, std, fl, st);
    if (v > 0 && split > 0 && qhi - qlo > c->wmin) {
        double mid = (qlo + qhi) / 2;
        double v1 = child(c, k, Slo, Shi, mid, qhi, odd, npm, std, fl, split - 1, st);
        if (v1 < BIG) {
            double v2 = child(c, k, Slo, Shi, qlo, mid, odd, npm, std, fl, split - 1, st);
            if (v2 < BIG) {
                double vv = (v1 * log(qhi / mid) + v2 * log(mid / qlo)) / log(qhi / qlo);
                if (vv < v) v = vv;
            }
        }
    }
    return v;
}

static double node(const Ctx *c, int k, double *Slo, double *Shi, double llo, double lhi, int odd, int npm,
                   int std, int fl, Stats *st) {
    int full = (1 << k) - 1;
    double mulo = 1 - Shi[full], muhi = 1 - Slo[full];
    st->nodes[std ? k : MAXK + 1]++;
    if (muhi < llo) return 0;                    /* u < 1 on the whole box: the term is empty */
    if (evaluable(c, k, Slo, Shi)) return 0;
    double T = capacity(c, k, Shi, !std && c->rev_linear);
    double fs = exact_floor(c, k, Slo, Shi, lhi, T);
    if (c->rev_floor && !std && fs >= 0)         /* a floor below every atom of a reversed term */
        for (int j = 0; j < k; j++)
            if (fs > Slo[1 << j]) fs = Slo[1 << j];
    if (fs >= lhi) return 0;
    if (fs > llo) fs = llo;                      /* a floor is below the sifting level at every point */
    double ulo = mulo / lhi, uhi = muhi / llo;
    double cdrop = omega_max(c, ulo, uhi) / llo;
    double best = odd ? INF : cdrop;
    if (odd && c->use_rev) {
        double r = reversal(c, k, Slo, Shi, npm);
        if (r < BIG && r * cdrop < best) best = r * cdrop;
    }
    if (fl > 0 && k >= 2 && k <= c->flipdepth && !(c->rev_even && odd) && !(c->rev_odd && !odd) &&
        !(c->rev_prime && uhi >= 2)) {
        double S2lo[1 << MAXK], S2hi[1 << MAXK];
        for (int j = 0; j < k; j++) {
            int bj = 1 << j;
            if (Slo[bj] < c->flipmin) continue;
            if (npm >> j & 1) continue;          /* only a prime can be opened */
            if (j == k - 1 && uhi >= 2) continue;
            if (c->rev_offdiag && std) {         /* the cell of p_j apart from its neighbours' */
                if (j + 1 < k && Slo[bj] < Shi[1 << (j + 1)]) continue;
                if (j > 0 && Shi[bj] > Slo[1 << (j - 1)]) continue;
            }
            /* the atoms other than j keep their order; the last atom is the cofactor */
            int map[MAXK], n = 0;
            for (int i = 0; i < k; i++)
                if (i != j) map[n++] = i;
            int mb = 1 << n;                     /* the bit of the cofactor among the new atoms */
            for (int m2 = 0; m2 < mb; m2++) {
                int old = 0;
                for (int i = 0; i < n; i++)
                    if (m2 >> i & 1) old |= 1 << map[i];
                S2lo[m2] = Slo[old];
                S2hi[m2] = Shi[old];
                S2lo[m2 | mb] = 1 - Shi[full ^ old];
                S2hi[m2 | mb] = 1 - Slo[full ^ old];
            }
            int npm2 = 0;
            for (int i = 0; i < n; i++)
                if (npm >> map[i] & 1) npm2 |= 1 << i;
            if (uhi >= 2) npm2 |= mb;
            double v = node(c, n + 1, S2lo, S2hi, Slo[bj] / 2, Shi[bj] / 2, odd, npm2, 0, fl - 1, st);
            if (v < BIG && v * Shi[bj] * cdrop < best) best = v * Shi[bj] * cdrop;
        }
    }
    if (k >= (std ? c->maxdepth : c->flipmax)) return best;
    int inexact = (odd ? c->use_ub : c->use_lb) && T > 0;
    double top = lhi < muhi / 2 ? lhi : muhi / 2;
    double flow = fs;
    if (flow < 0) {
        if (!inexact) return best;
        flow = T / c->smax > c->fmin ? T / c->smax : c->fmin;
        if (flow > llo) flow = llo;
    }
    if (fs >= 0 && top <= fs) return 0;
    if (inexact && top <= llo) {
        double pen = penalty(c, odd, T, top, mulo, muhi);
        if (pen < best) best = pen;
    }
    if (top <= flow) return best;
    int n = (int)ceil((top - flow) / c->step[k + 1] - 1e-9);
    if (n < 1) n = 1;
    double w = (top - flow) / n, cum = 0;
    int sp = k + 1 <= c->splitdepth ? c->split : 0;
    for (int j = 0; j < n; j++) {
        double qhi = top - j * w, qlo = j == n - 1 ? flow : top - (j + 1) * w;
        double ch = child(c, k, Slo, Shi, qlo, qhi, !odd, npm, std, fl, sp, st);
        if (ch >= BIG) {
            cum = INF;
            break;
        }
        cum += ch * log(qhi / qlo);
        if (cum >= best) break;
        double pen;
        if (fs >= 0 && j == n - 1) pen = 0;
        else if (inexact && qlo <= llo) pen = penalty(c, odd, T, qlo, mulo, muhi);
        else continue;
        if (cum + pen < best) best = cum + pen;
    }
    return best;
}

/* An upper bound for the loss: the sum over the cells of a_1 in [nu, 1/2] of the bounds for the nodes of depth 1. */
double hs_loss(const Ctx *c, double nu, int n1, double *prof, Stats *out) {
    double w = (0.5 - nu) / n1, tot = 0;
    Stats total;
    memset(&total, 0, sizeof total);
#pragma omp parallel
    {
        double *Slo = malloc(sizeof(double) << (MAXK + 1)), *Shi = malloc(sizeof(double) << (MAXK + 1));
        Stats st;
        memset(&st, 0, sizeof st);
        Slo[0] = Shi[0] = 0;
#pragma omp for schedule(dynamic, 1) reduction(+ : tot)
        for (int i = 0; i < n1; i++) {
            double hi = 0.5 - i * w, lo = i == n1 - 1 ? nu : 0.5 - (i + 1) * w;
            double v = child(c, 0, Slo, Shi, lo, hi, 1, 0, 1, c->flip, 1 <= c->splitdepth ? c->split : 0, &st);
            prof[i] = v;
            tot += v * log(hi / lo);
        }
#pragma omp critical
        {
            for (int d = 0; d < MAXK + 2; d++) total.nodes[d] += st.nodes[d];
        }
        free(Slo);
        free(Shi);
    }
    if (out) *out = total;
    return tot;
}
