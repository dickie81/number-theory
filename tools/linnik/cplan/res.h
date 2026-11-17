/* The resonant window's test (res_test.py): the float filters `quick`, `quickY` and the hint searches `hint`,
   `hintY`, definition by definition, in the same order of operations (the floats are IEEE doubles evaluated as Python
   evaluates them, the sums from the left). The constants come from res_test.py through the parameters file. */

#define MAXT 16                     /* terms of a rest */
#define MAXREC 15                   /* `Box.find`'s maxint */

typedef struct {
    i64 Ln, Ld, DEN;
    int NP, PK, GB, EB, SH, LVKS;
    U S, S2, HALF;                  /* 2^64, 2^128, 2^63 */
    U FT[32], FTM[32], IA[32], DH[32];
    U WC, MG, K1U, K1D, M1U, M1D, HP, LVE, OFF, E23, C310, C15U, C15D, C65D, C43, W2;
    U CK[64];                       /* the curve's kinks: fl(A(1 − lo)) and fl(A(1 − hi)) for each step */
    int nck;
    double HFlo[32], HFhi[32], HFA[32], TF[32], CHI, LVEQ;
} ResC;
static ResC RC;

static inline U mulF(U x, U y) { return Ushr(Umul(x, y), 64); }
static inline U mulC(U x, U y) { return Ushr(Uadd(Umul(x, y), Uu(((u128)1 << 64) - 1)), 64); }
static inline U Us(u64 x) { return Uu(x); }

typedef struct { U lo, a0, a1, b1, lw; } Term;
typedef struct { U k, g; } Tv;

static U loOf(i64 c) {
    /* (Lnum * sub(c, 1) * S) // (Lden * DEN) */
    U n = Umul(Umul(Uu(RC.Ln), Uu(tsub(c, 1))), RC.S);
    return Ufdiv(n, Umul(Uu(RC.Ld), Uu(RC.DEN)));
}

static Term mkTm(U lo) {
    Term t;
    U S = RC.S;
    U k0 = Uz(lo) ? U0() : Ufdiv(Uadd(S, Ust(lo, Us(1))), lo);
    if (Ule(k0, Us(1))) {
        t.a0 = RC.S2;
        t.a1 = U0();
    } else {
        U k = Usub(k0, Us(1));
        U k2 = Umul(Us(2), k);
        t.a0 = Ufdiv(Uadd(Ust(S, Umul(k, lo)), Ust(k2, Us(1))), k2);
        t.a1 = Ufdiv(S, k2);
    }
    t.b1 = Uz(k0) ? U0() : Ufdiv(S, Umul(Us(2), k0));
    t.lo = lo;
    t.lw = mulC(lo, RC.WC);
    return t;
}

static inline U getFT(int p) { return RC.FT[p]; }

static int pieceOf(U b) {
    for (int p = 0; p < RC.NP; p++)
        if (Ule(b, RC.FT[p])) return p;
    return RC.NP;
}

/* `best`: the line (i, A, B) in place of c = (ci, cA, cB) if A + cB < cA + B */
typedef struct { int i; U A, B; } Line;
static inline Line best(Line c, int i, U A, U B) {
    if (Ult(Uadd(A, c.B), Uadd(c.A, B))) {
        Line r = {i, A, B};
        return r;
    }
    return c;
}

static int pickT(const Term *t, U dS, U iax, U x) {
    Line c = {0, t->a0, mulF(t->a1, x)};
    c = best(c, 1, U0(), mulF(t->b1, x));
    c = best(c, 2, U0(), mulF(t->lo, dS));
    c = best(c, 3, t->lw, mulF(mulF(t->lo, iax), x));
    return c.i;
}

typedef struct { U c1, yuP, yuN, ydP, ydN; } Clamp;
typedef struct { U P0, P1, N0; } CLine;

static CLine clampL(const Clamp *k, U a, U b, int cc) {
    CLine r;
    if (cc == 0) {
        r.P0 = Ust(Uadd(Ushr(Uadd(b, Us(1)), 1), k->yuP), k->yuN);
        r.P1 = U0();
        r.N0 = U0();
    } else if (cc == 1) {
        r.P0 = Uadd(k->yuP, Ust(k->ydN, Uadd(Ushr(a, 1), k->ydP)));
        r.P1 = RC.HALF;
        r.N0 = k->yuN;
    } else {
        r.P0 = k->c1;
        r.P1 = U0();
        r.N0 = U0();
    }
    return r;
}

static int pickC(const Clamp *k, U a, U b, U x) {
    CLine l0 = clampL(k, a, b, 0);
    Line c = {0, Uadd(l0.P0, mulC(l0.P1, x)), l0.N0};
    for (int i = 1; i <= 2; i++) {
        CLine li = clampL(k, a, b, i);
        c = best(c, i, Uadd(li.P0, mulC(li.P1, x)), li.N0);
    }
    return c.i;
}

static inline int le0(U p0, U p1, U n0, U n1, U x) {
    return Ule(Uadd(p0, mulC(p1, x)), Uadd(n0, mulF(n1, x)));
}

static Clamp clampOf(U mlo) {
    Clamp k;
    U S = RC.S;
    U mtu = mulC(mlo, RC.M1U), mtd = mulF(mlo, RC.M1D);
    k.c1 = Ushr(Uadd(Ust(S, mlo), Us(1)), 1);
    k.yuP = Ushr(Uadd(Ust(RC.K1U, mtd), Us(1)), 1);
    k.yuN = Ushr(Ust(mtd, RC.K1U), 1);
    k.ydP = Ushr(Ust(RC.K1D, mtu), 1);
    k.ydN = Ushr(Uadd(Ust(mtu, RC.K1D), Us(1)), 1);
    return k;
}

static U lvVal(U lo, U k, U x) {
    U OFF = RC.OFF, LVE = RC.LVE;
    U k2 = Umul(Us(2), k), k4 = Umul(Us(4), k);
    U v = Ust(OFF, mulF(lo, RC.C310));
    U t = Ufdiv(Ust(Uadd(Uadd(Umul(k2, OFF), LVE), Ust(k2, Us(1))), x), k2);
    v = Umax(v, t);
    t = Ufdiv(Ust(Uadd(Uadd(Uadd(Umul(k4, OFF), Ushr(RC.S, 1)), LVE), Ust(k4, Us(1))), Uadd(x, Umul(k, lo))), k4);
    v = Umax(v, t);
    t = Ufdiv(Ust(Uadd(Uadd(Uadd(Umul(k4, OFF), RC.C43), LVE), Ust(k4, Us(1))), Uadd(x, Umul(k2, lo))), k4);
    v = Umax(v, t);
    return v;
}

static void mkTv(U lo, U ub, Tv *out) {
    U S = RC.S;
    U k0 = Uz(lo) ? U0() : Ufdiv(Uadd(S, Ust(lo, Us(1))), lo);
    for (int d = 1; d <= RC.LVKS; d++) {
        U k = Ust(k0, Us(d));
        U g;
        if (Ule(Us(1), k) && Ule(RC.E23, Umul(k, lo))) {
            U kl = Umul(k, lo);
            g = mulC(Umul(Umul(Us(2), k), Uadd(ub, lo)), RC.C15U);
            g = Umax(g, Ust(Ushr(S, 1), mulF(kl, RC.C15D)));
            g = Umax(g, Ust(RC.C43, mulF(kl, RC.C65D)));
            g = Uadd(RC.LVE, g);
        } else
            g = RC.S2;
        out[d - 1].k = k;
        out[d - 1].g = g;
    }
}

static int pickT2(const Term *t, const Tv *tv, U dS, U iax, U a, U x) {
    Line c = {0, t->a0, mulF(t->a1, x)};
    c = best(c, 1, U0(), mulF(t->b1, x));
    c = best(c, 2, U0(), mulF(t->lo, dS));
    c = best(c, 3, t->lw, mulF(mulF(t->lo, iax), x));
    for (int i = 0; i < RC.LVKS; i++)
        if (Ult(tv[i].g, a)) c = best(c, 4 + i, lvVal(t->lo, tv[i].k, x), RC.OFF);
    return c.i;
}

/* the interval's ends, pieces and lines: what `intv`, `intv2`, `intv3` share */
static int intvHead(U a, int pa, u64 r, U *b, int *pb) {
    *b = Ushl(Us(r & (((u64)1 << RC.EB) - 1)), RC.SH);
    *pb = pieceOf(*b);
    return *pb <= RC.NP && Ult(RC.FTM[*pb], *b) && Ule(*b, RC.FT[*pb]) && Ule(a, *b);
}

static int intv(const Term *ts, int n, const Clamp *k, U ltm, U a, int pa, u64 r) {
    U b;
    int pb;
    if (!intvHead(a, pa, r, &b, &pb)) return 0;
    U dS = Umax(RC.DH[pa], Ust(mulF(a, RC.IA[pa]), RC.WC));
    U iax = Umin(RC.IA[pa], RC.IA[pb]);
    if (pa <= RC.PK && RC.PK <= pb) iax = Umin(iax, RC.IA[RC.PK]);
    U x = Ushr(Uadd(a, b), 1);
    CLine cl = clampL(k, a, b, pickC(k, a, b, x));
    U p0 = Uadd(ltm, cl.P0), n0 = cl.N0, n1 = U0();
    for (int j = 0; j < n; j++) {
        const Term *t = &ts[j];
        int c = pickT(t, dS, iax, x);
        if (c == 0) {
            p0 = Uadd(p0, t->a0);
            n1 = Uadd(n1, t->a1);
        } else if (c == 1)
            n1 = Uadd(n1, t->b1);
        else if (c == 2)
            n0 = Uadd(n0, mulF(t->lo, dS));
        else {
            p0 = Uadd(p0, t->lw);
            n1 = Uadd(n1, mulF(t->lo, iax));
        }
    }
    U p1 = Uadd(RC.HALF, cl.P1);
    return le0(p0, p1, n0, n1, a) && le0(p0, p1, n0, n1, b);
}

static int intv2(const Term *ts, const Tv *tvs, int n, const Clamp *k, U ltm, U a, int pa, u64 r) {
    U b;
    int pb;
    if (!intvHead(a, pa, r, &b, &pb)) return 0;
    U dS = Umax(RC.DH[pa], Ust(mulF(a, RC.IA[pa]), RC.WC));
    U iax = Umin(RC.IA[pa], RC.IA[pb]);
    if (pa <= RC.PK && RC.PK <= pb) iax = Umin(iax, RC.IA[RC.PK]);
    U x = Ushr(Uadd(a, b), 1);
    CLine cl = clampL(k, a, b, pickC(k, a, b, x));
    U p0 = Uadd(ltm, cl.P0), n0 = cl.N0, n1 = U0(), va = U0(), vb = U0();
    for (int j = 0; j < n; j++) {
        const Term *t = &ts[j];
        const Tv *tv = &tvs[j * RC.LVKS];
        int c = pickT2(t, tv, dS, iax, a, x);
        if (c == 0) {
            p0 = Uadd(p0, t->a0);
            n1 = Uadd(n1, t->a1);
        } else if (c == 1)
            n1 = Uadd(n1, t->b1);
        else if (c == 2)
            n0 = Uadd(n0, mulF(t->lo, dS));
        else if (c == 3) {
            p0 = Uadd(p0, t->lw);
            n1 = Uadd(n1, mulF(t->lo, iax));
        } else {
            U kk = tv[c - 4].k;
            va = Uadd(va, lvVal(t->lo, kk, a));
            vb = Uadd(vb, lvVal(t->lo, kk, b));
            n0 = Uadd(n0, RC.OFF);
        }
    }
    U p1 = Uadd(RC.HALF, cl.P1);
    return le0(Uadd(p0, va), p1, n0, n1, a) && le0(Uadd(p0, vb), p1, n0, n1, b);
}

static inline U lvU(U lo, U k, U g, U a, U x) { return Ult(g, a) ? lvVal(lo, k, x) : RC.OFF; }

static int intv3(const Term *ts, const Tv *tvs, int n, const Clamp *k, U ltm, U a, int pa, u64 r) {
    U b;
    int pb;
    if (!intvHead(a, pa, r, &b, &pb)) return 0;
    U dS = Umax(RC.DH[pa], Ust(mulF(a, RC.IA[pa]), RC.WC));
    U iax = Umin(RC.IA[pa], RC.IA[pb]);
    u64 ch = r >> (RC.EB + 2);
    CLine cl = clampL(k, a, b, (int)((r >> RC.EB) & 3));
    U p0 = Uadd(ltm, cl.P0), n0 = cl.N0, n1 = U0(), va = U0(), vb = U0();
    for (int j = 0; j < n; j++) {
        const Term *t = &ts[j];
        const Tv *tv = &tvs[j * RC.LVKS];
        int c = (int)(ch & 7);
        ch >>= 3;
        if (c == 0) {
            p0 = Uadd(p0, t->a0);
            n1 = Uadd(n1, t->a1);
        } else if (c == 1)
            n1 = Uadd(n1, t->b1);
        else if (c == 2)
            n0 = Uadd(n0, mulF(t->lo, dS));
        else if (c == 3) {
            p0 = Uadd(p0, t->lw);
            n1 = Uadd(n1, mulF(t->lo, iax));
        } else {
            const Tv *kg = (c == 4) ? &tv[0] : &tv[1];
            va = Uadd(va, lvU(t->lo, kg->k, kg->g, a, a));
            vb = Uadd(vb, lvU(t->lo, kg->k, kg->g, a, b));
            n0 = Uadd(n0, RC.OFF);
        }
    }
    U p1 = Uadd(RC.HALF, cl.P1);
    return le0(Uadd(p0, va), p1, n0, n1, a) && le0(Uadd(p0, vb), p1, n0, n1, b);
}

/* ---------------------------------------------------------------------------------------------------------------
   The hint search (`Box`, `Corner`). */
typedef struct {
    int corner;                     /* 0: `Box` (records `intv`/`intv2`), 1: `Corner` (`intv3`) */
    int n, lv;
    Term ts[MAXT];
    Tv tvs[MAXT * 2];
    Clamp k;
    U ltm;
    int ok;
    i128 y0;
} Finder;

static U ltmOf(void) {
    /* (Lnum * S + sub(Lden * 10**6, 1)) // (Lden * 10**6) + MG */
    U d = Umul(Uu(RC.Ld), Uu(1000000));
    return Uadd(Ufdiv(Uadd(Umul(Uu(RC.Ln), RC.S), Ust(d, Us(1))), d), RC.MG);
}

static void boxInit(Finder *F, const i64 *cs, int n, i64 hs, int lv) {
    F->corner = 0;
    F->n = n;
    F->lv = lv;
    U sumlo = U0();
    for (int j = 0; j < n; j++) {
        F->ts[j] = mkTm(loOf(cs[j]));
        sumlo = Uadd(sumlo, F->ts[j].lo);
    }
    U mlo = Ufdiv(Umul(Umul(Uu(RC.Ln), Uu(tsub(tsub(RC.DEN, hs), 1))), RC.S), Umul(Uu(RC.Ld), Uu(RC.DEN)));
    if (lv) {
        U d5 = Umul(Uu(RC.Ld), Uu(100000));
        U ls5 = Uadd(Ufdiv(Umul(Uadd(Umul(Uu(RC.Ln), Uu(100000)), Uu(RC.Ld)), RC.S), d5), Us(1));
        U ub = Ust(ls5, Uadd(mlo, sumlo));
        for (int j = 0; j < n; j++) mkTv(F->ts[j].lo, ub, &F->tvs[j * RC.LVKS]);
    }
    F->ltm = ltmOf();
    F->k = clampOf(mlo);
    U sp = U0();
    for (int j = 0; j < n; j++) sp = Uadd(sp, mulF(F->ts[j].lo, RC.HP));
    F->ok = (hs + 1 < RC.DEN) && Ule(Uadd(F->ltm, Umin(F->k.c1, F->k.yuP)), sp);
    F->y0 = UtoI(F->k.yuP) - UtoI(F->k.yuN);
}

static void cornerInit(Finder *F, const Term *ts, const Tv *tvs, int n, U mlo, U ltm) {
    F->corner = 1;
    F->n = n;
    F->lv = 1;
    memcpy(F->ts, ts, sizeof(Term) * n);
    memcpy(F->tvs, tvs, sizeof(Tv) * n * RC.LVKS);
    F->ltm = ltm;
    F->k = clampOf(mlo);
    U sp = U0();
    for (int j = 0; j < n; j++) sp = Uadd(sp, mulF(ts[j].lo, RC.HP));
    F->ok = Ule(Uadd(ltm, Umin(F->k.c1, F->k.yuP)), sp);
    F->y0 = UtoI(F->k.yuP) - UtoI(F->k.yuN);
}

/* the record of the end e if the interval [a, e·2^-GB] passes, else 0 (a record is never 0: its end is) */
static u64 tryChoice(const Finder *F, U aS, int pa, u64 e) {
    if (!F->corner) {
        if (F->lv) return intv2(F->ts, F->tvs, F->n, &F->k, F->ltm, aS, pa, e) ? e : 0;
        return intv(F->ts, F->n, &F->k, F->ltm, aS, pa, e) ? e : 0;
    }
    U b = Ushl(Us(e), RC.SH);
    int pb = pieceOf(b);
    if (!(pb <= RC.NP && Ult(RC.FTM[pb], b) && Ule(b, RC.FT[pb]) && Ule(aS, b))) return 0;
    U dS = Umax(RC.DH[pa], Ust(mulF(aS, RC.IA[pa]), RC.WC));
    U iax = Umin(RC.IA[pa], RC.IA[pb]);
    U x = Ushr(Uadd(aS, b), 1);
    int cc = pickC(&F->k, aS, b, x);
    u64 ch = 0;
    for (int j = 0; j < F->n; j++)
        ch |= (u64)pickT2(&F->ts[j], &F->tvs[j * RC.LVKS], dS, iax, aS, x) << (3 * j);
    u64 r = e | ((u64)cc << RC.EB) | (ch << (RC.EB + 2));
    return intv3(F->ts, F->tvs, F->n, &F->k, F->ltm, aS, pa, r) ? r : 0;
}

static int cmpu64(const void *x, const void *y) {
    u64 a = *(const u64 *)x, b = *(const u64 *)y;
    return a < b ? -1 : a > b;
}

/* the kinks: the sorted ends e, 0 < e < 2^GB, and e + 1, of the points where a line or the clamp turns */
static int kinks(const Finder *F, u64 *out) {
    u64 tmp[1024];
    int m = 0;
    u64 lim = (u64)1 << RC.GB;
#define ADDPT(X)                                                                                                  \
    do {                                                                                                          \
        U _x = (X);                                                                                               \
        U _e = Ushr(_x, RC.SH);                                                                                   \
        if (Ufits(_e)) {                                                                                          \
            u128 _ee = Uto(_e);                                                                                   \
            if (_ee > 0 && _ee < lim) {                                                                           \
                tmp[m++] = (u64)_ee;                                                                              \
                tmp[m++] = (u64)_ee + 1;                                                                          \
            }                                                                                                     \
        }                                                                                                         \
    } while (0)
    for (int i = 0; i < RC.nck; i++) ADDPT(RC.CK[i]);
    i128 g0 = -2 * F->y0;
    if (g0 > 0) ADDPT(Ui(g0));
    i128 g1 = g0 + 2 * UtoI(F->k.c1);
    if (g1 > 0) ADDPT(Ui(g1));
    U S = RC.S;
    for (int j = 0; j < F->n; j++) {
        U lo = F->ts[j].lo;
        U k0 = Uz(lo) ? U0() : Ufdiv(Usub(Uadd(S, lo), Us(1)), lo);
        if (Ule(Us(2), k0)) ADDPT(Umul(k0, Ust(S, Umul(Usub(k0, Us(1)), lo))));
    }
    if (F->lv) {
        for (int j = 0; j < F->n; j++) {
            U lo = F->ts[j].lo;
            for (int i = 0; i < RC.LVKS; i++) {
                U k = F->tvs[j * RC.LVKS + i].k, g = F->tvs[j * RC.LVKS + i].g;
                if (Ult(g, S)) {
                    U c0 = mulF(lo, RC.C310);
                    U kl = Umul(k, lo), k2l = Umul(Umul(Us(2), k), lo), k4c0 = Umul(Umul(Us(4), k), c0);
                    ADDPT(Uadd(g, Us(1)));
                    ADDPT(Ust(Uadd(kl, RC.LVE), Ushr(S, 1)));
                    ADDPT(Ust(Uadd(k2l, RC.LVE), RC.C43));
                    ADDPT(Uadd(RC.LVE, Umul(Umul(Us(2), k), c0)));
                    ADDPT(Ust(Uadd(Uadd(Ushr(S, 1), RC.LVE), k4c0), kl));
                    ADDPT(Ust(Uadd(Uadd(RC.C43, RC.LVE), k4c0), k2l));
                }
            }
        }
    }
#undef ADDPT
    CHECK(m <= 1024, "too many kinks");
    qsort(tmp, m, sizeof(u64), cmpu64);
    int n = 0;
    for (int i = 0; i < m; i++)
        if (n == 0 || out[n - 1] != tmp[i]) out[n++] = tmp[i];
    return n;
}

/* `Box.find`: the records of the intervals, or -1 */
static int find(const Finder *F, int fast, u64 *recs) {
    if (!F->ok) return -1;
    u64 K[1024];
    int nk = kinks(F, K);
    U S = RC.S;
    U aS = U0();
    int pa = 0, nr = 0;
    u64 top = (u64)1 << RC.GB;
    while (Ult(aS, S)) {
        if (nr >= MAXREC) return -1;
        u64 a24 = (u64)Uto(Ushr(aS, RC.SH));
        u64 r = tryChoice(F, aS, pa, top);
        if (!r) {
            /* cand = the kinks above a24 */
            int c0 = 0;
            while (c0 < nk && K[c0] <= a24) c0++;
            const u64 *cand = K + c0;
            int nc = nk - c0;
            u64 lo_e = a24, bestr = 0;
            int have = 0;
            if (fast && nc) {
                int i0 = -1, i1 = nc;
                while (i1 - i0 > 1) {
                    int im = (i0 + i1) / 2;
                    u64 rr = tryChoice(F, aS, pa, cand[im]);
                    if (rr) {
                        i0 = im;
                        lo_e = cand[im];
                        bestr = rr;
                        have = 1;
                    } else
                        i1 = im;
                }
                if (!have) nc = 0;
            }
            if (!(fast && have))
                for (int i = 0; i < nc; i++) {
                    u64 rr = tryChoice(F, aS, pa, cand[i]);
                    if (rr) {
                        lo_e = cand[i];
                        bestr = rr;
                        have = 1;
                    }
                }
            u64 hi_e = top;
            for (int i = 0; i < nc; i++)
                if (cand[i] > lo_e) {
                    hi_e = cand[i];
                    break;
                }
            while (hi_e - lo_e > 1) {
                u64 mid = (lo_e + hi_e) / 2;
                u64 rr = tryChoice(F, aS, pa, mid);
                if (rr) {
                    lo_e = mid;
                    bestr = rr;
                    have = 1;
                } else
                    hi_e = mid;
            }
            if (!have) return -1;
            r = bestr;
        }
        recs[nr++] = r;
        aS = Ushl(Us(r & (((u64)1 << RC.EB) - 1)), RC.SH);
        pa = pieceOf(aS);
    }
    return nr;
}

/* `hint`: k ≥ 1 records of `resT`, or with the large values (`resT2`) k = 0 and the records; the form in `*lvf` */
typedef struct {
    int k;                          /* the number of records */
    int lvf;                        /* 1: the test with the large values' term (the hint `(0, k + 16h)`) */
    u64 rec[MAXREC];
} HintX;

static int hintX(const i64 *cs, int n, i64 hs, int lv, int fast, HintX *out) {
    Finder F;
    for (int pass = 0; pass < 2; pass++) {
        int lvp = pass;
        if (lvp && !lv) break;
        boxInit(&F, cs, n, hs, lvp);
        for (int fi = 0; fi < (fast ? 2 : 1); fi++) {
            int f = fast ? (fi == 0) : 0;
            int k = find(&F, f, out->rec);
            if (k >= 0) {
                out->k = k;
                out->lvf = lvp;
                return 1;
            }
        }
    }
    return 0;
}

/* the hint of the test at the two corners: kH records of the upper corner, kL of the lower */
typedef struct {
    int n, kH, kL;
    u64 recH[MAXREC], recL[MAXREC];
} HintY;

static U loW0(i64 c) {
    return Ust(Ufdiv(Umul(Umul(Uu(RC.Ln), Uu(c)), RC.S), Umul(Uu(RC.Ld), Uu(RC.DEN))), RC.W2);
}
static U hiW0(i64 d) {
    U den = Umul(Uu(RC.Ld), Uu(RC.DEN));
    return Uadd(Ufdiv(Uadd(Umul(Umul(Uu(RC.Ln), Uu(d)), RC.S), Usub(den, Us(1))), den), RC.W2);
}
/* loW and hiW of a cell's end, cached (pure) */
#define WCACHE (1 << 16)
static struct { i64 c; int set; U lo, hi; } WC_[WCACHE];
static inline int wslot(i64 c) {
    u64 h = (u64)c * 0x9E3779B97F4A7C15ULL;
    return (int)(h >> 48);
}
static U loW(i64 c) {
    int i = wslot(c);
    if (!(WC_[i].set && WC_[i].c == c)) {
        WC_[i].c = c;
        WC_[i].set = 1;
        WC_[i].lo = loW0(c);
        WC_[i].hi = hiW0(c);
    }
    return WC_[i].lo;
}
static U hiW(i64 d) {
    int i = wslot(d);
    if (!(WC_[i].set && WC_[i].c == d)) {
        WC_[i].c = d;
        WC_[i].set = 1;
        WC_[i].lo = loW0(d);
        WC_[i].hi = hiW0(d);
    }
    return WC_[i].hi;
}
static U lvG(U lo, U hi, U k) {
    if (Ule(Us(1), k) && Ule(RC.E23, Umul(k, lo))) {
        U kl = Umul(k, lo);
        U g = mulC(Umul(Umul(Us(2), k), hi), RC.C15U);
        g = Umax(g, Ust(Ushr(RC.S, 1), mulF(kl, RC.C15D)));
        g = Umax(g, Ust(RC.C43, mulF(kl, RC.C65D)));
        return Uadd(RC.LVE, g);
    }
    return RC.S2;
}

static int hintYc(const i64 *lo_, const i64 *hi_, int n, int fast, HintY *out) {
    U S = RC.S;
    U los[MAXT], his[MAXT], sl = U0(), sh = U0();
    for (int j = 0; j < n; j++) {
        los[j] = loW(lo_[j]);
        his[j] = hiW(hi_[j]);
        sl = Uadd(sl, los[j]);
        sh = Uadd(sh, his[j]);
    }
    U ls = Ufdiv(Umul(Uu(RC.Ln), S), Uu(RC.Ld));
    U need = Uadd(Uadd(Uadd(sh, RC.W2), Ufdiv(Ust(sh, sl), Us(11))), Us(2));
    U ltm = ltmOf();
    int ok = Ule(need, ls);
    for (int j = 0; j < n; j++) ok = ok && lo_[j] <= hi_[j] && Ule(Us(1), los[j]);
    if (!ok) return 0;
    Term tH[MAXT], tL[MAXT];
    Tv vH[MAXT * 2], vL[MAXT * 2];
    for (int j = 0; j < n; j++) {
        U lo = los[j], hi = his[j];
        tH[j] = mkTm(hi);
        U k0 = Uz(hi) ? U0() : Ufdiv(Uadd(S, Ust(hi, Us(1))), hi);
        U k1 = Ust(k0, Us(1)), k2 = Ust(k0, Us(2));
        vH[2 * j].k = k1;
        vH[2 * j].g = lvG(lo, hi, k1);
        vH[2 * j + 1].k = k2;
        vH[2 * j + 1].g = lvG(lo, hi, k2);
        tL[j] = mkTm(lo);
        mkTv(lo, Ust(sh, sl), &vL[2 * j]);
    }
    CHECK(RC.LVKS == 2, "the corners' test reads two powers");
    Finder F;
    for (int side = 0; side < 2; side++) {
        int k = -1;
        for (int fi = 0; fi < (fast ? 2 : 1); fi++) {
            int f = fast ? (fi == 0) : 0;
            if (side == 0)
                cornerInit(&F, tH, vH, n, Ust(ls, need), ltm);
            else
                cornerInit(&F, tL, vL, n, S, ltm);
            k = find(&F, f, side == 0 ? out->recH : out->recL);
            if (k >= 0) break;
        }
        if (k < 0) return 0;
        if (side == 0)
            out->kH = k;
        else
            out->kL = k;
    }
    out->n = n;
    /* `packY`: the fields must fit */
    if (!(n < 16 && out->kH < 16 && out->kL < 16)) return 0;
    return 1;
}

/* ---------------------------------------------------------------------------------------------------------------
   The float filters (`quick`, `quickY`). */
static inline int pcF(double a) {
    for (int i = 0; i < RC.NP; i++)
        if (a <= RC.TF[i]) return i;
    return RC.NP;
}
static inline double bmF(double a) {
    int i = pcF(a);
    if (i == RC.NP) return RC.CHI;
    double hi = RC.HFhi[i], v = 1 - a / RC.HFA[i];
    return v < hi ? v : hi;                       /* min(hi, v) */
}
static inline double pmax0(double v) { return (0.0 > v) ? 0.0 : v; }      /* max(v, 0): v unless 0 > v */
static inline double pmaxF(double a, double b) { return b > a ? b : a; } /* max(a, b) */
static inline double pminF(double a, double b) { return b < a ? b : a; } /* min(a, b) */

typedef struct {
    int n;
    double los[MAXT], zl[MAXT], tlo[MAXT];
    int nk[MAXT];
    double k0p[MAXT][2], k1p[MAXT][2];           /* the moments' lines (p0, p1) */
    int nlv[MAXT];
    double lvk[MAXT][4], lvG[MAXT][4];
    double c1, y0, thr, w;
    int leaves, maxleaf;
} QState;

static inline double lvv(double lo, double k, double g) {
    double e = RC.LVEQ;
    double v = -lo * (0.3 - e);
    v = pmaxF(v, (e - g) / (2 * k));
    v = pmaxF(v, (0.5 + e - g - k * lo) / (4 * k));
    v = pmaxF(v, (4.0 / 3 + e - g - 2 * k * lo) / (4 * k));
    return v;
}

static int qcheck(QState *Q, double a, double b, int fuel) {
    double y0 = Q->y0, c1 = Q->c1, w = Q->w;
    double ya = a / 2 + y0, yb = b / 2 + y0;
    double ab = a + b;
    /* cl = min of three lines by 2·l0 + l1·(a + b) */
    double l0s[3] = {pmaxF(0.0, yb), y0 + pmaxF(0.0, -ya), c1};
    double l1s[3] = {0.0, 0.5, 0.0};
    int ci = 0;
    double ck = 2 * l0s[0] + l1s[0] * ab;
    for (int i = 1; i < 3; i++) {
        double kk = 2 * l0s[i] + l1s[i] * ab;
        if (kk < ck) {
            ck = kk;
            ci = i;
        }
    }
    double t0 = l0s[ci], t1 = l1s[ci] + 0.5;
    int ia = pcF(a), ib = pcF(b);
    double dS = 1 - w - bmF(a);
    double ia_inv;
    if (ib == RC.NP)
        ia_inv = 0.0;
    else {
        ia_inv = pminF(ia < RC.NP ? 1 / RC.HFA[ia] : 0.0, 1 / RC.HFA[ib]);
        if (ia <= RC.PK && RC.PK <= ib) ia_inv = pminF(ia_inv, 1 / RC.HFA[RC.PK]);
    }
    double ta = t0 + t1 * a, tb = t0 + t1 * b;
    for (int j = 0; j < Q->n; j++) {
        double ca[8], cb[8];
        int m = 0;
        for (int i = 0; i < Q->nk[j]; i++) {
            double l0 = Q->k0p[j][i], l1 = Q->k1p[j][i];
            ca[m] = l0 + l1 * a;
            cb[m++] = l0 + l1 * b;
        }
        double zlo = Q->zl[j];
        {
            double l0 = -zlo * dS, l1 = 0.0;
            ca[m] = l0 + l1 * a;
            cb[m++] = l0 + l1 * b;
            l0 = zlo * w;
            l1 = -zlo * ia_inv;
            ca[m] = l0 + l1 * a;
            cb[m++] = l0 + l1 * b;
        }
        for (int i = 0; i < Q->nlv[j]; i++)
            if (Q->lvG[j][i] < a) {
                ca[m] = lvv(Q->los[j], Q->lvk[j][i], a);
                cb[m++] = lvv(Q->los[j], Q->lvk[j][i], b);
            }
        int bi = 0;
        double bk = ca[0] + cb[0];
        for (int i = 1; i < m; i++) {
            double kk = ca[i] + cb[i];
            if (kk < bk) {
                bk = kk;
                bi = i;
            }
        }
        ta += ca[bi];
        tb += cb[bi];
    }
    if (ta <= Q->thr && tb <= Q->thr) {
        Q->leaves += 1;
        return Q->maxleaf < 0 || Q->leaves <= Q->maxleaf;
    }
    if (fuel == 0) return 0;
    double mid = (a + b) / 2;
    return qcheck(Q, a, mid, fuel - 1) && qcheck(Q, mid, b, fuel - 1);
}

/* `quick`: with `pt` null, the rest's lower ends `cs` and upper ends' sum `hs`; else the point (los, m, tlo, thi,
   clamp) */
typedef struct {
    int n;
    double los[MAXT], m, tlo[MAXT], thi[MAXT];
    int clamp;
} QPt;

static int quick(const i64 *cs, int n, i64 hs, int fuel, double slack, int lv, int maxleaf, const QPt *pt) {
    QState Q;
    double L = (double)RC.Ln / (double)RC.Ld;
    double kq = L / (double)RC.DEN;
    const double *tlo;
    const double *thi = NULL;
    int clamp;
    double m = 0;
    Q.n = n;
    if (!pt) {
        if (n == 0) return 0;
        for (int j = 0; j < n; j++) Q.los[j] = kq * (double)(cs[j] - 1);
        double mn = Q.los[0];
        for (int j = 1; j < n; j++) mn = pminF(mn, Q.los[j]);
        if (mn <= 0 || hs + 1 >= RC.DEN) return 0;
        tlo = Q.los;
        clamp = 1;
    } else {
        n = Q.n = pt->n;
        for (int j = 0; j < n; j++) Q.los[j] = pt->los[j];
        m = pt->m;
        tlo = pt->tlo;
        thi = pt->thi;
        clamp = pt->clamp;
        if (n == 0) return 0;
        double mn = tlo[0];
        for (int j = 1; j < n; j++) mn = pminF(mn, tlo[j]);
        if (mn <= 0) return 0;
    }
    double s = 0;
    for (int j = 0; j < n; j++) s += Q.los[j];
    if (s < 1 + 2.0 / 25000) return 0;
    if (!pt) m = kq * (double)(RC.DEN - hs - 1);
    double w = 4e-6, tau = 1e-6, marg = 1.0 / 25000;
    Q.w = w;
    Q.c1 = clamp ? pmax0(1 - m) / 2 : 0.0;
    Q.y0 = clamp ? (5.0 / 12 + 3.0 / 1000 - m * (11.0 / 12 + 1.0 / 1000)) / 2 : -1.0;
    Q.thr = -marg - L * tau + slack;
    for (int j = 0; j < n; j++) Q.zl[j] = Q.los[j];
    s = 0;
    for (int j = 0; j < n; j++) s += Q.zl[j] * (1 - w - 11.0 / 12);
    if (-s + pminF(Q.c1, pmaxF(0.0, Q.y0)) > Q.thr) return 0;
    for (int j = 0; j < n; j++) {
        double lo = Q.los[j];
        double kc = ceil(1 / lo - 1e-12);
        CHECK(kc < 1e15, "quick: a power too large");
        i64 k0 = (i64)kc;
        if (k0 < 1) k0 = 1;
        int m2 = 0;
        for (i64 k = k0 - 1; k <= k0; k++)
            if (k >= 1) {
                double dk = (double)k;
                Q.k0p[j][m2] = pmax0(1 - dk * lo) / (double)(2 * k);
                Q.k1p[j][m2] = -1.0 / (double)(2 * k);
                m2++;
            }
        Q.nk[j] = m2;
        Q.nlv[j] = 0;
    }
    if (lv) {
        double e = RC.LVEQ;
        for (int j = 0; j < n; j++) {
            double lo = Q.los[j];
            double kc = ceil(1 / lo - 1e-12);
            i64 k0 = (i64)kc;
            if (k0 < 1) k0 = 1;
            double hi;
            if (!thi) {
                double sz = 0;
                for (int i = 0; i < n; i++) sz += Q.zl[i];
                hi = (L + 1e-5 - m - (sz - lo)) - slack;
            } else
                hi = thi[j] - slack;
            double tl = tlo[j];
            for (i64 k = k0 - 1; k > k0 - 1 - RC.LVKS; k--) {
                double dk = (double)k;
                if (k >= 1 && dk * tl >= 2.0 / 3 + e - slack) {
                    double v = (double)(2 * k) * hi * (0.2 + e);
                    v = pmaxF(v, 0.5 - dk * tl * (0.2 - 4 * e));
                    v = pmaxF(v, 4.0 / 3 - dk * tl * (1.2 - 4 * e));
                    Q.lvk[j][Q.nlv[j]] = dk;
                    Q.lvG[j][Q.nlv[j]] = e + v - slack;
                    Q.nlv[j]++;
                }
            }
        }
    }
    static const double GS[9] = {0.0, 0.17, 0.26, 0.34, 0.4, 0.45, 0.5, 0.75, 1.0};
    for (int gi = 0; gi < 9; gi++) {
        double g = GS[gi];
        double v = g / 2 + pminF(Q.c1, pmaxF(0.0, g / 2 + Q.y0));
        double b = bmF(g) + w - 1;
        for (int j = 0; j < n; j++) {
            double mn = Q.zl[j] * b;
            for (int i = 0; i < Q.nk[j]; i++) mn = pminF(mn, Q.k0p[j][i] + Q.k1p[j][i] * g);
            for (int i = 0; i < Q.nlv[j]; i++)
                if (Q.lvG[j][i] < g) mn = pminF(mn, lvv(Q.los[j], Q.lvk[j][i], g));
            v += mn;
        }
        if (v > Q.thr) return 0;
    }
    Q.leaves = 0;
    Q.maxleaf = maxleaf;
    return qcheck(&Q, 0.0, 1.0, fuel);
}

/* `quickY`: the cells (lo_[j], hi_[j]) */
static int quickY(const i64 *lo_, const i64 *hi_, int n, int lv, int strict) {
    if (n == 0) return 0;
    U S = RC.S;
    U lo[MAXT], hi[MAXT], sl = U0(), sh = U0();
    for (int j = 0; j < n; j++) {
        lo[j] = loW(lo_[j]);
        hi[j] = hiW(hi_[j]);
        sl = Uadd(sl, lo[j]);
        sh = Uadd(sh, hi[j]);
    }
    static U ls;
    static int lsSet;
    if (!lsSet) {
        ls = Ufdiv(Umul(Uu(RC.Ln), S), Uu(RC.Ld));
        lsSet = 1;
    }
    U need = Uadd(Uadd(Uadd(sh, RC.W2), Ufdiv(Ust(sh, sl), Us(11))), Us(2));
    for (int j = 0; j < n; j++)
        if (lo_[j] > hi_[j]) return 0;
    U mn = lo[0];
    for (int j = 1; j < n; j++) mn = Umin(mn, lo[j]);
    if (Ult(mn, Us(1)) || Ult(ls, need)) return 0;
    QPt p1, p2;
    double ub = U_div_S(Ust(sh, sl));
    p1.n = p2.n = n;
    for (int j = 0; j < n; j++) {
        double fl = U_div_S(lo[j]), fh = U_div_S(hi[j]);
        p1.los[j] = fh;
        p1.tlo[j] = fl;
        p1.thi[j] = fh;
        p2.los[j] = fl;
        p2.tlo[j] = fl;
        p2.thi[j] = fl + ub;
    }
    p1.m = U_div_S(Usub(ls, need));
    p1.clamp = 1;
    p2.m = 1.0;
    p2.clamp = 0;
    int fuel = strict ? 12 : 22, maxleaf = strict ? 15 : -1;
    double slack = strict ? -1e-7 : 1e-9;
    return quick(NULL, 0, 0, fuel, slack, lv, maxleaf, &p1) && quick(NULL, 0, 0, fuel, slack, lv, maxleaf, &p2);
}
