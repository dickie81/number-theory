/* gen.h: the generator of tools/linnik/hint_cert.py (`--cgen`): the hints of a plan (`Planner.dHints`, `dser`,
   `dserF`, `dserKids`, `resFields` with `res_test.hintH`), the kernel's search led by them (`dPart`, `dCheck`, the
   mirror that every part passes before it is kept), the cut of a heavy cell into parts (`cut`, `add_part`) and the
   window's lines named in a part's hints (`hl_parts`, `transcode_hl`). Each function is the Python one of the same
   name, in the same order of operations: the parts, their hints and their costs are the Python generator's.

   The hints are a stream of bits, the first field in the low bits (`pack`). Python reads them as one number, `h`,
   and returns the number's rest; here the stream is an array of words and a position, and a read past the end
   gives zeros, as a shift of the number does. */

/* ---------------------------------------------------------------------------------------------------------------
   Bit streams */
typedef struct { u64 *w; long n, cap; } BV;          /* `n` bits written; the words past them are 0 */
static void bvInit(BV *b) {
    b->w = NULL;
    b->n = 0;
    b->cap = 0;
}
static void bvFree(BV *b) {
    free(b->w);
    bvInit(b);
}
static void bvReserve(BV *b, long nbits) {
    long nw = nbits / 64 + 2;
    if (nw <= b->cap) return;
    long c = b->cap ? b->cap : 64;
    while (c < nw) c *= 2;
    b->w = realloc(b->w, sizeof(u64) * c);
    CHECK(b->w, "out of memory");
    memset(b->w + b->cap, 0, sizeof(u64) * (c - b->cap));
    b->cap = c;
}
/* the bits [at, at + k) of the words `w` (`nw` of them), k ≤ 64: 0 past the end */
static inline u64 bget(const u64 *w, long nw, long at, int k) {
    if (k == 0) return 0;
    long i = at >> 6;
    int o = (int)(at & 63);
    u64 v = i < nw ? w[i] >> o : 0;
    if (o && o + k > 64 && i + 1 < nw) v |= w[i + 1] << (64 - o);
    return k == 64 ? v : v & (((u64)1 << k) - 1);
}
/* the field `(v, k)`: `pack` asserts `0 <= v < 2^k` */
static void bvPut(BV *b, u64 v, int k) {
    CHECK(k >= 0 && k <= 64 && (k == 64 || v >> k == 0), "pack: a field does not fit");
    if (k == 0) return;
    bvReserve(b, b->n + k);
    long i = b->n >> 6;
    int o = (int)(b->n & 63);
    b->w[i] |= v << o;
    if (o && o + k > 64) b->w[i + 1] |= v >> (64 - o);
    b->n += k;
}
/* the bits [at, at + k) of another stream, as one field */
static void bvPutSlice(BV *b, const u64 *w, long nw, long at, long k) {
    while (k > 0) {
        int m = k > 64 ? 64 : (int)k;
        bvPut(b, bget(w, nw, at, m), m);
        at += m;
        k -= m;
    }
}
/* the number's bit length: one more than its highest bit set */
static long bvLen(const u64 *w, long nw) {
    for (long i = nw - 1; i >= 0; i--)
        if (w[i]) return 64 * i + 64 - __builtin_clzll(w[i]);
    return 0;
}
static void bvHex(FILE *f, const u64 *w, long nw) {
    long nb = bvLen(w, nw);
    long nd = (nb + 3) / 4;
    if (nd == 0) {
        fputc('0', f);
        return;
    }
    for (long i = nd - 1; i >= 0; i--) fputc("0123456789abcdef"[bget(w, nw, 4 * i, 4)], f);
}
static void bvFromHex(BV *b, const char *s) {
    bvInit(b);
    long nd = (long)strlen(s);
    bvReserve(b, 4 * nd);
    for (long i = 0; i < nd; i++) {
        char ch = s[nd - 1 - i];
        int v = ch >= '0' && ch <= '9' ? ch - '0' : ch >= 'a' && ch <= 'f' ? ch - 'a' + 10 : -1;
        CHECK(v >= 0, "a malformed hexadecimal number");
        b->w[i / 16] |= (u64)v << (4 * (i % 16));
    }
    b->n = 4 * nd;
}

/* ---------------------------------------------------------------------------------------------------------------
   The rests that the window's tests read (`restIR`, `restIRC`, `restIRF`, and the cells of `chkIRY`, `chkIRFY`) */
typedef struct { int n; i64 cs[MAXT]; i64 hs; } Rest;

static int cellsAllIn(const Cell *bl, int n) {
    if (n > 13) return 0;
    for (int i = 0; i < n; i++)
        if (!(1 <= bl[i].lo && bl[i].lo <= bl[i].hi && bl[i].hi <= DEN)) return 0;
    return 1;
}
/* `restIR` (cof 0) and `restIRC` (cof 1) */
static int restIRg(const Cell *bl, int n, u32 sr, int cof, Rest *r) {
    if (!cellsAllIn(bl, n)) return 0;
    r->n = 0;
    r->hs = 0;
    for (int p = 0; p < n; p++)
        if (sr >> p & 1) {
            r->cs[r->n++] = bl[p].lo;
            r->hs += bl[p].hi;
        }
    if (r->n == 0) return 0;
    if (cof && (sr >> n & 1)) {
        i64 slo = loSum(bl, n), shi = hiSum(bl, n), lk = bl[0].lo;
        if (!(shi + 2 <= DEN)) return 0;
        r->cs[r->n++] = max64(tsub(tsub(DEN, shi), 1), lk);
        r->hs += tsub(DEN, slo) + 1;
    }
    return 1;
}
static int restIRFg(i64 e1, i64 e2, const Cell *beta, int nb, const Cell *bl, int n, u32 sr, Rest *r) {
    if (!cellsAllIn(bl, n)) return 0;
    r->n = 0;
    r->hs = 0;
    for (int p = 0; p < n; p++)
        if (sr >> p & 1) {
            r->cs[r->n++] = bl[p].lo;
            r->hs += bl[p].hi;
        }
    if (r->n == 0) return 0;
    if (sr >> n & 1) {
        i64 slo = tsub(loSum(bl, n), loSum(beta, nb)), shi = tsub(hiSum(bl, n), hiSum(beta, nb));
        i64 lk = n ? bl[0].lo : 0;
        if (!(e2 + shi + 2 <= DEN)) return 0;
        r->cs[r->n++] = max64(tsub(tsub(tsub(DEN, e2), shi), 1), lk);
        r->hs += tsub(tsub(DEN, e1), slo) + 1;
    }
    return 1;
}
/* the cells of `chkIRY` (frozen 0) and `chkIRFY` (frozen 1) */
static int cellsIRY(int frozen, const Cell *bl, int n, u32 sr, Cell *out, int *no) {
    if (!cellsAllIn(bl, n)) return 0;
    int m = 0;
    for (int p = 0; p < n; p++)
        if (sr >> p & 1) out[m++] = bl[p];
    if (m == 0) return 0;
    if (sr >> n & 1) {
        if (!frozen) {
            i64 slo = loSum(bl, n), shi = hiSum(bl, n), lk = bl[0].lo;
            if (!(shi + 2 <= DEN)) return 0;
            out[m].lo = max64(tsub(tsub(DEN, shi), 1), lk);
            out[m].hi = tsub(DEN, slo) + 1;
        } else {
            i64 e1 = FZ.e1, e2 = FZ.e2;
            i64 slo = tsub(loSum(bl, n), loSum(FZ.beta, FZ.nb)), shi = tsub(hiSum(bl, n), hiSum(FZ.beta, FZ.nb));
            i64 lk = n ? bl[0].lo : 0;
            if (!(e2 + shi + 2 <= DEN)) return 0;
            out[m].lo = max64(tsub(tsub(tsub(DEN, e2), shi), 1), lk);
            out[m].hi = tsub(tsub(DEN, e1), slo) + 1;
        }
        m++;
    }
    *no = m;
    return 1;
}

/* ---------------------------------------------------------------------------------------------------------------
   The window's tests on hints (res_test.py: `resT`, `resT2`, `resXH`, `resYH`) and `hintH` */
static inline int recW(int n, int lv) { return RC.EB + 2 + (lv ? 3 : 2) * n; }
static inline u64 emask(void) { return ((u64)1 << RC.EB) - 1; }

/* `pieceC`: `pieceOf` by bisection */
static int pieceC(U b) {
    int lo = 0, hi = RC.NP;
    while (lo < hi) {
        int mid = (lo + hi) / 2;
        if (Ule(b, RC.FT[mid]))
            hi = mid;
        else
            lo = mid + 1;
    }
    return lo;
}

/* `resT` (lv 0) and `resT2` (lv 1): `kk` records of `EB` bits */
static int resTg(const Rest *r, int lv, int kk, const u64 *recs) {
    Finder F;
    boxInit(&F, r->cs, r->n, r->hs, lv);
    if (!F.ok) return 0;
    U a = U0();
    int pa = 0;
    for (int i = 0; i < kk; i++) {
        u64 rr = recs[i] & emask();
        if (!(lv ? intv2(F.ts, F.tvs, F.n, &F.k, F.ltm, a, pa, rr) : intv(F.ts, F.n, &F.k, F.ltm, a, pa, rr)))
            return 0;
        a = Ushl(Us(rr), RC.SH);
        pa = pieceOf(a);
    }
    return Ucmp(a, RC.S) == 0;
}

/* `intvH` and `intv2H`: one interval whose record names its lines */
static int intvHg(const Finder *F, int lv, U a, int pa, u64 r) {
    U b = Ushl(Us(r & emask()), RC.SH);
    int pb = pieceC(b);
    if (!(pb <= RC.NP && Ult(RC.FTM[pb], b) && Ule(b, RC.FT[pb]) && Ule(a, b))) return 0;
    U dS = Umax(RC.DH[pa], Ust(mulF(a, RC.IA[pa]), RC.WC));
    U iax = Umin(RC.IA[pa], RC.IA[pb]);
    CLine cl = clampL(&F->k, a, b, (int)((r >> RC.EB) & 3));
    U p0 = Uadd(F->ltm, cl.P0), n0 = cl.N0, n1 = U0(), va = U0(), vb = U0();
    u64 ch = r >> (RC.EB + 2);
    for (int j = 0; j < F->n; j++) {
        const Term *t = &F->ts[j];
        int c;
        if (lv) {
            c = (int)(ch & 7);
            ch >>= 3;
        } else {
            c = (int)(ch & 3);
            ch >>= 2;
        }
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
            const Tv *tv = &F->tvs[j * RC.LVKS];
            const Tv *kg = (c == 4) ? &tv[0] : &tv[1];
            if (Ult(kg->g, a)) {
                va = Uadd(va, lvVal(t->lo, kg->k, a));
                vb = Uadd(vb, lvVal(t->lo, kg->k, b));
            } else {
                va = Uadd(va, RC.OFF);
                vb = Uadd(vb, RC.OFF);
            }
            n0 = Uadd(n0, RC.OFF);
        }
    }
    U p1 = Uadd(RC.HALF, cl.P1);
    if (!lv) return le0(p0, p1, n0, n1, a) && le0(p0, p1, n0, n1, b);
    return le0(Uadd(p0, va), p1, n0, n1, a) && le0(Uadd(p0, vb), p1, n0, n1, b);
}

/* `resXH`: `kk` records of `recW(n, lv)` bits */
static int resXHg(const Rest *r, int lv, int kk, const u64 *recs) {
    Finder F;
    boxInit(&F, r->cs, r->n, r->hs, lv);
    if (!F.ok) return 0;
    U a = U0();
    int pa = 0;
    for (int i = 0; i < kk; i++) {
        u64 rr = recs[i];
        if (!intvHg(&F, lv, a, pa, rr)) return 0;
        a = Ushl(Us(rr & emask()), RC.SH);
        pa = pieceC(a);
    }
    return Ucmp(a, RC.S) == 0;
}

/* `hintH`: the records of `resXH` from those of `resX`, the lines that `resX` picks at the interval's midpoint */
static void hintHg(const Rest *r, int lv, int kk, const u64 *recs, u64 *out) {
    Finder F;
    boxInit(&F, r->cs, r->n, r->hs, lv);
    U a = U0();
    int pa = 0;
    for (int i = 0; i < kk; i++) {
        u64 rr = recs[i] & emask();
        U b = Ushl(Us(rr), RC.SH);
        int pb = pieceOf(b);
        U dS = Umax(RC.DH[pa], Ust(mulF(a, RC.IA[pa]), RC.WC));
        U iax = Umin(RC.IA[pa], RC.IA[pb]);
        U x = Ushr(Uadd(a, b), 1);
        u64 cc = (u64)pickC(&F.k, a, b, x);
        u64 ch = 0;
        for (int j = 0; j < F.n; j++) {
            if (lv)
                ch |= (u64)pickT2(&F.ts[j], &F.tvs[j * RC.LVKS], dS, iax, a, x) << (3 * j);
            else
                ch |= (u64)pickT(&F.ts[j], dS, iax, x) << (2 * j);
        }
        CHECK(recW(r->n, lv) <= 64, "hintH: a record wider than 64 bits");
        out[i] = rr | cc << RC.EB | ch << (RC.EB + 2);
        a = b;
        pa = pieceOf(b);
    }
}

/* `resTM3`: `k` records of `EB + 2 + 3n` bits from the bits [at, end) of the stream */
static int resTM3g(const Term *ts, const Tv *tvs, int n, U mlo, U ltm, int k, const u64 *w, long nw, long at,
                   long end) {
    Finder F;
    cornerInit(&F, ts, tvs, n, mlo, ltm);
    if (!F.ok) return 0;
    int wr = RC.EB + 2 + 3 * n;
    CHECK(wr <= 64, "resTM3: a record wider than 64 bits");
    U a = U0();
    int pa = 0;
    for (int i = 0; i < k; i++) {
        long p = at + (long)wr * i;
        u64 rr = 0;
        if (p < end) {
            int m = (int)(end - p < wr ? end - p : wr);
            rr = bget(w, nw, p, m);
        }
        if (!intv3(F.ts, F.tvs, F.n, &F.k, F.ltm, a, pa, rr)) return 0;
        a = Ushl(Us(rr & emask()), RC.SH);
        pa = pieceOf(a);
    }
    return Ucmp(a, RC.S) == 0;
}

/* `resYH` on the cells `cells` with its hints the bits [at, end) of the stream */
static int resYHg(const Cell *cells, int n, const u64 *w, long nw, long at, long end) {
    CHECK(n <= MAXT && RC.LVKS == 2, "resYH: too many cells");
    long len = end - at;
    u64 head = bget(w, nw, at, len < 12 ? (int)len : 12);
    int nh = (int)(head & 15), kH = (int)(head >> 4 & 15), kL = (int)(head >> 8 & 15);
    long sh = (long)(15 + 3 * nh) * kH;
    long hs = at + 12, hm = hs + sh < end ? hs + sh : end;
    /* cornersOf */
    U S = RC.S;
    U los[MAXT], his[MAXT], sl = U0(), shs = U0();
    for (int j = 0; j < n; j++) {
        los[j] = loW(cells[j].lo);
        his[j] = hiW(cells[j].hi);
        sl = Uadd(sl, los[j]);
        shs = Uadd(shs, his[j]);
    }
    U ls = Ufdiv(Umul(Uu(RC.Ln), S), Uu(RC.Ld));
    U need = Uadd(Uadd(Uadd(shs, RC.W2), Ufdiv(Ust(shs, sl), Us(11))), Us(2));
    U ltm = ltmOf();
    int ok = Ule(need, ls);
    for (int j = 0; j < n; j++) ok = ok && cells[j].lo <= cells[j].hi && Ule(Us(1), los[j]);
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
        mkTv(lo, Ust(shs, sl), &vL[2 * j]);
    }
    return resTM3g(tH, vH, n, Ust(ls, need), ltm, kH, w, nw, hs, hm) &&
           resTM3g(tL, vL, n, S, ltm, kL, w, nw, hm, end);
}

/* ---------------------------------------------------------------------------------------------------------------
   The plan's own hints at a window's leaf, checked as the plan has them (`chkNode` with `res_hl` off) */
static int resXplan(const Rest *r, const HintX *h) { return resTg(r, h->lvf, h->k, h->rec); }
static void packYbits(const HintY *h, BV *b) {
    int w = RC.EB + 2 + 3 * h->n;
    bvInit(b);
    bvPut(b, (u64)h->n, 4);
    bvPut(b, (u64)h->kH, 4);
    bvPut(b, (u64)h->kL, 4);
    for (int i = 0; i < h->kH; i++) bvPut(b, h->recH[i], w);
    for (int i = 0; i < h->kL; i++) bvPut(b, h->recL[i], w);
}
static int resYplan(const Cell *cells, int n, const HintY *h) {
    BV b;
    packYbits(h, &b);
    int ok = resYHg(cells, n, b.w, b.cap, 0, b.n);
    bvFree(&b);
    return ok;
}

/* ---------------------------------------------------------------------------------------------------------------
   The kernel's search led by hints (`dStep`, `dSolve`, `dKidsC`, `dPart`, `dCheck`, `dFlipCost`, `dFlipTree`) */

/* a configuration read from the hints: `Cfg`, and for a window's leaf (kind 3) its `k`, `k2` and the bits of its
   records, for the test at the two corners (kind 4) the bits of its hints */
typedef struct {
    Cfg c;
    int k, k2;
    long rs, re;
} DCfg;

/* a window's leaf found by `transcode_hl`'s run: where its records are, their width, and its rest */
typedef struct {
    long at, oldw;
    int has;
    Rest rest;
    int k, k2;
    long rs, re;
} Leaf;

static struct {
    const u64 *w;
    long nw;
    int hl;                         /* `res_hl`: the records name the lines */
    int hook;                       /* `transcode_hl`'s run: the window's leaves are kept */
    Leaf *lv;
    int nl, cap;
    int maxbox;
} D;

static inline u64 rdb(long *pos, int k) {
    u64 v = bget(D.w, D.nw, *pos, k);
    *pos += k;
    return v;
}

static void cfgIPd(int w, long *pos, DCfg *d) {
    memset(d, 0, sizeof *d);
    d->c.kind = 1;
    if (rdb(pos, 1) == 0) {
        d->c.s0 = (u32)rdb(pos, w);
        d->c.sr = 1;
    } else {
        int j = (int)rdb(pos, 3);
        d->c.s0 = (u32)rdb(pos, w);
        d->c.sr = (u32)1 << j;
    }
}
static void cfgIPRd(int w, long *pos, DCfg *d) {
    if (bget(D.w, D.nw, *pos, 1) == 0) {
        *pos += 1;
        cfgIPd(w, pos, d);
        return;
    }
    *pos += 1;
    memset(d, 0, sizeof *d);
    d->c.kind = 3;
    d->c.sr = (u32)rdb(pos, w);
    d->k = (int)rdb(pos, 4);
    int n = D.hl ? __builtin_popcount(d->c.sr) : 0;
    long nb;
    if (d->k == 0) {
        d->k2 = (int)rdb(pos, 4);
        nb = (long)(D.hl ? recW(n, 1) : RC.EB) * d->k2;
    } else
        nb = (long)(D.hl ? recW(n, 0) : RC.EB) * d->k;
    d->rs = *pos;
    d->re = *pos + nb;
    *pos += nb;
    if (D.hook) {
        if (D.nl == D.cap) {
            D.cap = D.cap ? 2 * D.cap : 64;
            D.lv = realloc(D.lv, sizeof(Leaf) * D.cap);
            CHECK(D.lv, "out of memory");
        }
        Leaf *l = &D.lv[D.nl++];
        memset(l, 0, sizeof *l);
        l->at = d->rs;
        l->oldw = nb;
    }
}
static void cfgIPYd(int w, long *pos, DCfg *d) {
    if (bget(D.w, D.nw, *pos, 1) == 1 && bget(D.w, D.nw, *pos + 1 + w, 8) == 0) {
        memset(d, 0, sizeof *d);
        *pos += 1;
        d->c.kind = 4;
        d->c.sr = (u32)rdb(pos, w);
        *pos += 8;
        u64 head = bget(D.w, D.nw, *pos, 12);
        long nb = 12 + (long)(15 + 3 * (int)(head & 15)) * ((int)(head >> 4 & 15) + (int)(head >> 8 & 15));
        d->rs = *pos;
        d->re = *pos + nb;
        *pos += nb;
        return;
    }
    cfgIPRd(w, pos, d);
}
/* `dI` of the main tree (`cfgIMY`, `cfgIMRC`, `cfgIMR`, `cfgIM`) and over a frozen part (`cfgIFY`, `cfgIFR`,
   `cfgIF`) */
static void dIg(const Cell *bl, int n, long *pos, DCfg *d) {
    (void)bl;
    if (!FZ.on) {
        if (G.ycorner)
            cfgIPYd(n + 1, pos, d);
        else if (G.cof)
            cfgIPRd(n + 1, pos, d);
        else if (G.res)
            cfgIPRd(n, pos, d);
        else
            cfgIPd(n, pos, d);
    } else {
        if (G.ycorner)
            cfgIPYd(n + 1, pos, d);
        else if (G.resF)
            cfgIPRd(n + 1, pos, d);
        else
            cfgIPd(n + 1, pos, d);
    }
}

/* the records of a window's leaf, from the stream, `kk` of `w` bits each in [rs, re) */
static void recsOf(const DCfg *d, int kk, int w, u64 *out) {
    for (int i = 0; i < kk; i++) {
        long p = d->rs + (long)w * i;
        u64 v = 0;
        if (p < d->re) {
            int m = (int)(d->re - p < w ? d->re - p : w);
            v = bget(D.w, D.nw, p, m);
        }
        out[i] = v;
    }
}
/* `resTest` (`resXH` with `res_hl`, else `resX`) on the rest `r` with the leaf's records */
static int resTestD(const Rest *r, const DCfg *d) {
    int lv = d->k == 0, kk = lv ? d->k2 : d->k;
    u64 recs[16];
    if (D.hl) {
        int w = recW(r->n, lv);
        CHECK(w <= 64, "resXH: a record wider than 64 bits");
        recsOf(d, kk, w, recs);
        return resXHg(r, lv, kk, recs);
    }
    recsOf(d, kk, RC.EB, recs);
    return resTg(r, lv, kk, recs);
}

/* `okIm` */
static int okImD(const Cell *bl, int n, const DCfg *d) {
    if (G.ycorner && d->c.kind == 4) {
        Cell cells[MAXT + 1];
        int nc;
        if (!cellsIRY(FZ.on, bl, n, d->c.sr, cells, &nc)) return 0;
        return resYHg(cells, nc, D.w, D.nw, d->rs, d->re);
    }
    if ((FZ.on ? G.resF : G.res) && d->c.kind == 3) {
        Rest r;
        int has = FZ.on ? restIRFg(FZ.e1, FZ.e2, FZ.beta, FZ.nb, bl, n, d->c.sr, &r)
                        : restIRg(bl, n, d->c.sr, G.cof, &r);
        int ok = has && resTestD(&r, d);
        if (D.hook) {
            CHECK(ok && has && D.nl > 0 && !D.lv[D.nl - 1].has, "transcode_hl: a window's leaf that fails");
            Leaf *l = &D.lv[D.nl - 1];
            l->has = 1;
            l->rest = r;
            l->k = d->k;
            l->k2 = d->k2;
            l->rs = d->rs;
            l->re = d->re;
        }
        return ok;
    }
    return FZ.on ? okIF(bl, n, &d->c) : okI_T(bl, n, &d->c);
}

/* `cfgJP`: the floor and the configuration of a Buchstab step */
static FC cfgJPd(int sel, i64 lm, i64 lo, i64 hi, int w, long *pos) {
    FC r;
    r.ok = 1;
    u32 s0 = (u32)rdb(pos, w), s1;
    int e;
    if (rdb(pos, 1) == 0) {
        s1 = (u32)tsub((i64)1 << w >> 1, 1);
        e = 1;
    } else {
        s1 = (u32)rdb(pos, w);
        e = (int)rdb(pos, 1);
    }
    if (sel % 2 == 0) {
        r.f = (i64)minI(lm, tsubI(vOfF(hi), uOfF(lo) + 1));
        Cfg c = {1, s0, (u32)1 << (sel / 2), s1, e};
        r.cfg = c;
    } else {
        r.f = floorP(sel / 2, (i64)minI(lm, fmax3));
        Cfg c = {2, s0, 0, s1, e};
        r.cfg = c;
    }
    return r;
}
static FC cfgJMd(const Cell *bl, int n, long *pos) {
    int sel = (int)rdb(pos, 4);
    u32 m;
    i64 lm, lo, hi;
    pickCc(bl, n, (u32)1 << (sel / 2), &m, &lm, &lo, &hi);
    return cfgJPd(sel, lm, lo, hi, n, pos);
}
static FC cfgJFd(i64 Kb, i64 cl, i64 chh, const Cell *beta, int nb, i64 lomb, const Cell *bl, int n, long *pos) {
    int sel = (int)rdb(pos, 4);
    u32 m;
    i64 lm, lo, hi;
    pickCc(bl, (int)tsub(n, nb), (u32)1 << (sel / 2), &m, &lm, &lo, &hi);
    u32 cofb = (m >> nb) & 1;
    return cfgJPd(sel, max64(1, tsub(min64(lm, lomb), Kb)),
                  max64(1, tsub(lo + mSum(0, beta, nb, m) + cofb * cl, Kb)),
                  hi + mSum(1, beta, nb, m) + cofb * chh + Kb, n + 1, pos);
}

/* the frozen tree's constants of `frozen` */
static struct {
    i64 Kb, cl, chh, lomb;
} FZD;

static i128 dSolveg(const Ops *O, int nf, const Cell *bl, int nbl, int par, i128 lim, long *pos);

/* `dKidsC`: `prm` is `parM` in the main tree, `parF` over a frozen part */
static i128 dKidsg(const Ops *O, int nrec, i64 top, const Cell *bl, int nbl, int par, i64 f, i128 lim, long *pos) {
    i64 st, reg, e, last;
    if (!O->frozen) {
        st = stepOf(nbl + 1);
        reg = min64(top, tsub(DEN, loSum(bl, nbl)) / 2 + 2);
        e = tsub(bl[nbl - 1].lo, 1);
        last = tsub(DEN - 1, hiSum(bl, nbl));
    } else {
        int nch = (int)tsub(nbl, FZ.nb);
        st = nch < 2 ? G.hF : 2 * G.hF;
        reg = min64(top, tsub(FZ.ctx.hi + 1, loSum(bl, nch)) / 2 + 2);
        e = 0;
        last = tsub(tsub(FZ.ctx.lo, 1), hiSum(bl, nch));
    }
    CHECK(nbl + 1 <= D.maxbox, "a box of too many primes");
    Cell box[MAXB];
    i64 c = f, a = f;
    i128 tot = 0;
    for (int it = 0; it < 4096; it++) {
        if (bget(D.w, D.nw, *pos, 1) == 0) {
            *pos += 1;
            mkBox(a, top, bl, nbl, box);
            i128 r = dSolveg(O, nrec, box, nbl + 1, par, lim, pos);
            return tot + r;
        }
        int j = (int)bget(D.w, D.nw, *pos + 1, 2);
        long hh;
        i64 p, nc;
        if (j != 3) {
            p = c;
            for (int s = 0; s < j + 1; s++) p = p + max64(1, min64(st, p / G.kappa));
            hh = *pos + 3;
            nc = p;
        } else {
            int t = (int)bget(D.w, D.nw, *pos + 3, 3);
            if (t <= 3) {
                p = c;
                for (int s = 0; s < t + 4; s++) p = p + max64(1, min64(st, p / G.kappa));
                hh = *pos + 6;
                nc = p;
            } else if (t == 4) {
                for (int s = 0; s < 7; s++) c = c + max64(1, min64(st, c / G.kappa));
                *pos += 6;
                continue;
            } else {
                p = t == 5 ? reg : t == 6 ? e : last;
                hh = *pos + 6;
                nc = c;
            }
        }
        if (!(a < p && p < top)) {
            *pos = hh;
            return tot + lim;
        }
        *pos = hh;
        mkBox(a, p, bl, nbl, box);
        i128 r = dSolveg(O, nrec, box, nbl + 1, par, lim, pos);
        if (lim <= r) return tot + r;
        tot += r;
        lim -= r;
        a = p;
        c = nc;
    }
    return tot + lim;
}

/* `dFlipTree` */
static i128 dFlipTreeg(Cell ctx, const Cell *beta, int nb, int pos_, i128 lim, long *pos) {
    Cell c = beta[0];
    i64 t = flipT(ctx);
    i64 lsb = loSum(beta, nb), hsb = hiSum(beta, nb);
    FZ.on = 1;
    FZ.e1 = tsub(DEN, ctx.hi) + pos_;
    FZ.e2 = tsub(DEN, ctx.lo) + 1 - pos_;
    FZ.Kb = 12 + DEN / beta[0].lo;
    memcpy(FZ.beta, beta, sizeof(Cell) * nb);
    FZ.nb = nb;
    FZ.ctx = ctx;
    FZD.Kb = FZ.Kb;
    FZD.cl = max64(1, tsub(FZ.e1, hsb));
    FZD.chh = tsub(FZ.e2, lsb);
    FZD.lomb = lomin(beta, nb);
    Ops O = {1, ctx, nb};
    FC fc = cfgJFd(FZD.Kb, FZD.cl, FZD.chh, FZ.beta, nb, FZD.lomb, FZ.beta, nb, pos);
    i128 r;
    if (!(1 <= fc.f && fc.f <= min64(c.lo, t) && okJm(FZ.beta, nb, fc.f, &fc.cfg)))
        r = lim;
    else
        r = dKidsg(&O, G.fuel, t, FZ.beta, nb, !pos_, fc.f, lim, pos);
    FZ.on = 0;
    return r;
}

/* `dFlipCost` (`dAltF`) */
static i128 dFlipCostg(const Cell *bl, int n, int pos_, i128 lim, long *pos) {
    if (!flipOK(G.maxlen, bl, n)) return lim;
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
    i128 r = dFlipTreeg(ctx, beta, nb, pos_, CAPK, pos);
    if (CAPK <= r) return lim;
    U A = Umul(Ui(ctx.hi), Ui(dropCost(bl, n)));
    if (!pos_) A = Uadd(A, E);
    U num = Uadd(Umul(Ui(r), A), Umul(Ui(bdK(ctx, flipT(ctx))), E));
    /* cdiv(num, DEN·K) */
    U dk = Umul(Ui((i128)DEN), Ui(KC));
    return UtoI(Ucdiv(num, dk));
}

/* `dStep` */
static i128 dStepg(const Ops *O, int nf, const Cell *bl, int nbl, int par, i128 lim, long *pos) {
    if (nbl == 0 || !Ogrd(O, nbl)) return lim;
    Cell x = bl[0];
    if (bget(D.w, D.nw, *pos, 1) == 0) {
        *pos += 1;
        DCfg d;
        dIg(bl, nbl, pos, &d);
        return okImD(bl, nbl, &d) ? 0 : lim;
    }
    if (bget(D.w, D.nw, *pos + 1, 1) == 0) {
        *pos += 2;
        FC fc = O->frozen ? cfgJFd(FZD.Kb, FZD.cl, FZD.chh, FZ.beta, FZ.nb, FZD.lomb, bl, nbl, pos)
                          : cfgJMd(bl, nbl, pos);
        if (!(1 <= fc.f && fc.f <= x.lo && okJm(bl, nbl, fc.f, &fc.cfg))) return lim;
        return dKidsg(O, nf - 1, x.hi, bl, nbl, !par, fc.f, lim, pos);
    }
    if (bget(D.w, D.nw, *pos + 2, 1) == 0) {
        *pos += 3;
        i128 dc = Odrp(O, bl, nbl, par);
        return dc < 0 ? lim : dc;
    }
    if (bget(D.w, D.nw, *pos + 3, 1) == 0) {
        *pos += 4;
        if (O->frozen) return lim;
        return dFlipCostg(bl, nbl, par, lim, pos);
    }
    if (bget(D.w, D.nw, *pos + 4, 1) == 0) {
        *pos += 5;
        i64 mid = (x.lo + x.hi) / 2;
        if (x.lo < mid && mid < x.hi) {
            Cell box[MAXB];
            memcpy(box, bl, sizeof(Cell) * nbl);
            box[0].hi = mid;
            i128 r = dSolveg(O, nf - 1, box, nbl, par, lim, pos);
            if (lim <= r) return r;
            box[0].lo = mid;
            box[0].hi = x.hi;
            i128 r2 = dSolveg(O, nf - 1, box, nbl, par, tsubI(lim, r), pos);
            return r + r2;
        }
        return lim;
    }
    if (bget(D.w, D.nw, *pos + 5, 1) == 0) {
        *pos += 6;
        return Ovan(O, bl, nbl) ? 0 : lim;
    }
    *pos += 6;
    return lim;
}
static i128 dSolveg(const Ops *O, int nf, const Cell *bl, int nbl, int par, i128 lim, long *pos) {
    if (nf == 0) return lim;
    return dStepg(O, nf, bl, nbl, par, lim, pos);
}
/* `dPart` with `dCheck` */
static i128 dPartg(i64 top, const Cell *bl, int nbl, int par, const i64 *cs, int ncs, i64 a, i128 lim, long *pos) {
    Ops O = {0, {0, 0}, 0};
    Cell box[MAXB];
    CHECK(nbl + 1 <= D.maxbox, "a box of too many primes");
    i128 tot = 0;
    for (int i = 0; i < ncs; i++) {
        i64 c = cs[i];
        if (!(a < c && c < top)) return tot + lim;
        mkBox(a, c, bl, nbl, box);
        i128 r = dSolveg(&O, G.fuel, box, nbl + 1, par, lim, pos);
        if (lim <= r) return tot + r;
        tot += r;
        lim -= r;
        a = c;
    }
    mkBox(a, top, bl, nbl, box);
    i128 r = dSolveg(&O, G.fuel, box, nbl + 1, par, lim, pos);
    return tot + r;
}

/* a run of the decoder on the hints `h` of a part: its cost and the position it stops at */
typedef struct {
    i64 top, a;
    int nbl, par, ncs;
    Cell bl[MAXB];
    i64 *cs;
    i128 c;
    BV h;
    double secs;
    long nsteps;
    long cnt[NKIND][2];
    int ord[2 * NKIND], nord;       /* the kinds in the order `count` meets them */
} Part;

static i128 runPart(const Part *p, const BV *h, int hl, int hook, long *pos) {
    D.w = h->w;
    D.nw = h->cap;
    D.hl = hl;
    D.hook = hook;
    D.nl = 0;
    D.maxbox = MAXB;
    memset(&FZ, 0, sizeof FZ);
    *pos = 0;
    return dPartg(p->top, p->bl, p->nbl, p->par, p->cs, p->ncs, p->a, KC, pos);
}

/* ---------------------------------------------------------------------------------------------------------------
   The hints of a plan (`dHints`, `dser`, `dserF`, `dserKids`, `cfgFields`, `evalFields`, `resFields`) */
static void cfgFieldsg(BV *out, int sel, const Cfg *cfg, int w) {
    bvPut(out, (u64)sel, 4);
    if (cfg->s1 == ((u32)1 << (w - 1)) - 1 && cfg->e) {
        bvPut(out, cfg->s0, w);
        bvPut(out, 0, 1);
        return;
    }
    bvPut(out, cfg->s0, w);
    bvPut(out, 1, 1);
    bvPut(out, cfg->s1, w);
    bvPut(out, (u64)(cfg->e ? 1 : 0), 1);
}
static void evalFieldsg(BV *out, const Cfg *cfg, int w, int res) {
    int j = 31 - __builtin_clz(cfg->sr);
    bvPut(out, 0, 1);
    if (res) bvPut(out, 0, 1);
    if (j == 0)
        bvPut(out, 0, 1);
    else {
        bvPut(out, 1, 1);
        bvPut(out, (u64)j, 3);
    }
    bvPut(out, cfg->s0, w);
}
/* `resFields` of the leaf `x` (its hint as the plan has it) on a set of `w` bits, the rest `r` (with `res_hl`) */
static void resFieldsg(BV *out, const Node *x, int w, const Rest *r) {
    u32 mask = x->u.r.mask;
    const Memo *e = x->u.r.m;
    if (e->y) {
        const HintY *hy = (const HintY *)e->hint;
        BV b;
        packYbits(hy, &b);
        long nb = 12 + (long)(15 + 3 * hy->n) * (hy->kH + hy->kL);
        CHECK(G.ycorner && (w >= 32 || mask >> w == 0) && bvLen(b.w, b.cap) <= nb, "resFields: a corner's hint");
        bvPut(out, 0, 1);
        bvPut(out, 1, 1);
        bvPut(out, mask, w);
        bvPut(out, 0, 8);
        bvPutSlice(out, b.w, b.cap, 0, nb);
        bvFree(&b);
        return;
    }
    const HintX *hx = (const HintX *)e->hint;
    int lv = hx->lvf, kk = hx->k;
    u64 recs[16];
    int eb = RC.EB, eb2 = RC.EB;
    if (G.hl) {
        hintHg(r, lv, kk, hx->rec, recs);
        CHECK(resXHg(r, lv, kk, recs), "resFields: the hint with the lines fails resXH");
        eb = recW(r->n, 0);
        eb2 = recW(r->n, 1);
    } else
        for (int i = 0; i < kk; i++) recs[i] = hx->rec[i];
    CHECK(w >= 32 || mask >> w == 0, "resFields: the rest's set");
    if (lv) {
        CHECK(0 < kk && kk < 16, "resFields: the number of intervals");
        bvPut(out, 0, 1);
        bvPut(out, 1, 1);
        bvPut(out, mask, w);
        bvPut(out, 0, 4);
        bvPut(out, (u64)kk, 4);
        for (int i = 0; i < kk; i++) bvPut(out, recs[i], eb2);
        return;
    }
    CHECK(0 < kk && kk < 16, "resFields: the number of intervals");
    bvPut(out, 0, 1);
    bvPut(out, 1, 1);
    bvPut(out, mask, w);
    bvPut(out, (u64)kk, 4);
    for (int i = 0; i < kk; i++) bvPut(out, recs[i], eb);
}

static void dserg(const Node *x, const Cell *bl, int n, int par, BV *out);
static void dserFg(const Node *x, const Cell *bl, int n, int par, BV *out);

/* `dserKids`: the cells `ends` (nc + 1 ends) of the new prime with the plans `kids` */
static void dserKidsg(int frozen, i64 st, i64 reg, i64 e, i64 last, i64 f, const i64 *ends, int nc,
                      Node *const *kids, const Cell *bl, int n, int par, BV *out) {
    i64 c = f, a = f;
    Cell box[MAXB];
    for (int i = 0; i < nc - 1; i++) {
        i64 p = ends[i + 1];
        int k = 0;
        i64 g = c;
        while (g < p) {
            g = g + max64(1, min64(st, g / G.kappa));
            k++;
        }
        if (g == p && k >= 1) {
            while (k > 7) {
                bvPut(out, 1, 1);
                bvPut(out, 3, 2);
                bvPut(out, 4, 3);
                k -= 7;
            }
            if (k <= 3) {
                bvPut(out, 1, 1);
                bvPut(out, (u64)(k - 1), 2);
            } else {
                bvPut(out, 1, 1);
                bvPut(out, 3, 2);
                bvPut(out, (u64)(k - 4), 3);
            }
            c = p;
        } else {
            CHECK(p == reg || p == e || p == last, "dserKids: a cut off the grid");
            bvPut(out, 1, 1);
            bvPut(out, 3, 2);
            bvPut(out, (u64)(p == reg ? 5 : p == e ? 6 : 7), 3);
        }
        mkBox(a, p, bl, n, box);
        if (frozen)
            dserFg(kids[i], box, n + 1, par, out);
        else
            dserg(kids[i], box, n + 1, par, out);
        a = p;
    }
    bvPut(out, 0, 1);
    mkBox(a, ends[nc], bl, n, box);
    if (frozen)
        dserFg(kids[nc - 1], box, n + 1, par, out);
    else
        dserg(kids[nc - 1], box, n + 1, par, out);
}
/* `kidCells`: the ends of the cells of the new prime that the plan's bits cut out of the proposed cuts */
static int kidEnds(const Vec *cuts, i64 f, i64 top, const uint8_t *bits, int nbits, i64 *ends) {
    int ne = 0, ib = 0;
    ends[ne++] = f;
    for (int i = 0; i < cuts->n; i++) {
        i64 c = cuts->v[i];
        if (ends[ne - 1] < c && c < top) {
            CHECK(ib < nbits, "kidCells: the plan's bits end early");
            if (bits[ib++]) ends[ne++] = c;
        }
    }
    ends[ne++] = top;
    return ne;
}
/* a Buchstab step's fields: its code, the configuration of `guide` (on a set of `w` bits) and the cells */
static void serBuch(int frozen, const Node *x, const Cell *bl, int n, int par, i64 top, int w, BV *out) {
    FC g = guide(bl, n, x->u.b.sel);
    CHECK(g.ok, "dser: no proposal for the plan's step");
    cfgFieldsg(out, x->u.b.sel, &g.cfg, w);
    i64 f = g.f;
    Vec cs = {0, 0, NULL};
    Strat S = {frozen, 0, FZ.ctx, FZ.nb};
    Scuts(&S, bl, n, f, &cs);
    i64 *ends = malloc(sizeof(i64) * (cs.n + 2));
    CHECK(ends, "out of memory");
    int ne = kidEnds(&cs, f, top, x->u.b.bits, x->u.b.nbits, ends);
    free(cs.v);
    CHECK(ne - 1 == x->u.b.nk, "dser: the cells and the plans differ in number");
    i64 st, reg, e, last;
    if (!frozen) {
        st = stepOf(n + 1);
        reg = min64(top, tsub(DEN, loSum(bl, n)) / 2 + 2);
        e = tsub(bl[n - 1].lo, 1);
        last = tsub(DEN - 1, hiSum(bl, n));
    } else {
        int nch = (int)tsub(n, FZ.nb);
        st = nch < 2 ? G.hF : 2 * G.hF;
        reg = min64(top, tsub(FZ.ctx.hi + 1, loSum(bl, nch)) / 2 + 2);
        e = 0;
        last = tsub(tsub(FZ.ctx.lo, 1), hiSum(bl, nch));
    }
    dserKidsg(frozen, st, reg, e, last, f, ends, ne - 1, x->u.b.kids, bl, n, !par, out);
    free(ends);
}

/* `dserF`: a node of a tree over a frozen part */
static void dserFg(const Node *x, const Cell *bl, int n, int par, BV *out) {
    int w = n + 1;
    switch (x->k) {
    case KV:
        bvPut(out, 31, 6);
        break;
    case KE: {
        Cfg cfg;
        CHECK(propIF(bl, n, &cfg) && okIF(bl, n, &cfg), "dserF: an evaluation that fails");
        evalFieldsg(out, &cfg, w, G.resF);
        break;
    }
    case KR: {
        CHECK(G.resF, "dserF: a window's leaf without the window");
        const Memo *e = x->u.r.m;
        CHECK(e->state == MHINT, "dserF: a window's leaf without its hint");
        Rest r;
        if (e->y) {
            Cell cells[MAXT + 1];
            int nc;
            CHECK(cellsIRY(1, bl, n, x->u.r.mask, cells, &nc) && resYplan(cells, nc, (const HintY *)e->hint),
                  "dserF: the plan's corner test fails");
        } else
            CHECK(restIRFg(FZ.e1, FZ.e2, FZ.beta, FZ.nb, bl, n, x->u.r.mask, &r) &&
                      resXplan(&r, (const HintX *)e->hint),
                  "dserF: the plan's window test fails");
        resFieldsg(out, x, w, e->y ? NULL : &r);
        break;
    }
    case KD:
        bvPut(out, 3, 3);
        break;
    case KS: {
        Cell box[MAXB];
        memcpy(box, bl, sizeof(Cell) * n);
        i64 mid = (bl[0].lo + bl[0].hi) / 2;
        bvPut(out, 15, 5);
        box[0].hi = mid;
        dserFg(x->u.s.a, box, n, par, out);
        box[0].lo = mid;
        box[0].hi = bl[0].hi;
        dserFg(x->u.s.b, box, n, par, out);
        break;
    }
    case KB:
        bvPut(out, 1, 2);
        serBuch(1, x, bl, n, par, bl[0].hi, w, out);
        break;
    default:
        die("dserF: a step of the wrong kind");
    }
}

/* `dser`: a node of the main tree */
static void dserg(const Node *x, const Cell *bl, int n, int par, BV *out) {
    int w = n, wI = n + (G.cof ? 1 : 0);
    switch (x->k) {
    case KV:
        bvPut(out, 31, 6);
        break;
    case KE: {
        Cfg cfg;
        CHECK(propI2(bl, n, loSum(bl, n), &cfg) && okI_T(bl, n, &cfg), "dser: an evaluation that fails");
        evalFieldsg(out, &cfg, wI, G.res);
        break;
    }
    case KR: {
        const Memo *e = x->u.r.m;
        CHECK(e->state == MHINT, "dser: a window's leaf without its hint");
        Rest r;
        if (e->y) {
            Cell cells[MAXT + 1];
            int nc;
            CHECK(cellsIRY(0, bl, n, x->u.r.mask, cells, &nc) && resYplan(cells, nc, (const HintY *)e->hint),
                  "dser: the plan's corner test fails");
        } else
            CHECK(restIRg(bl, n, x->u.r.mask, G.cof, &r) && resXplan(&r, (const HintX *)e->hint),
                  "dser: the plan's window test fails");
        resFieldsg(out, x, wI, e->y ? NULL : &r);
        break;
    }
    case KD:
        bvPut(out, 3, 3);
        break;
    case KS: {
        Cell box[MAXB];
        memcpy(box, bl, sizeof(Cell) * n);
        i64 mid = (bl[0].lo + bl[0].hi) / 2;
        bvPut(out, 15, 5);
        box[0].hi = mid;
        dserg(x->u.s.a, box, n, par, out);
        box[0].lo = mid;
        box[0].hi = bl[0].hi;
        dserg(x->u.s.b, box, n, par, out);
        break;
    }
    case KB:
        bvPut(out, 1, 2);
        serBuch(0, x, bl, n, par, bl[0].hi, w, out);
        break;
    case KF:
    case KP: {
        CHECK(par == (x->k == KP), "dser: a reversal of the wrong sign");
        Cell ctx = bl[n - 1];
        int nb = n - 1;
        i64 t = flipT(ctx);
        FZ.on = 1;
        FZ.e1 = tsub(DEN, ctx.hi) + par;
        FZ.e2 = tsub(DEN, ctx.lo) + 1 - par;
        FZ.Kb = 12 + DEN / bl[0].lo;
        memcpy(FZ.beta, bl, sizeof(Cell) * nb);
        FZ.nb = nb;
        FZ.ctx = ctx;
        bvPut(out, 7, 4);
        serBuch(1, x, FZ.beta, nb, par, t, nb + 1, out);
        FZ.on = 0;
        break;
    }
    default:
        die("dser: a step of the wrong kind");
    }
}

/* ---------------------------------------------------------------------------------------------------------------
   The parts (`add_part`, `cut`) */
static void countg(const Node *x, int fz, Part *p) {
    if (p->cnt[x->k][fz] == 0) p->ord[p->nord++] = 2 * x->k + fz;
    p->cnt[x->k][fz]++;
    p->nsteps++;
    if (x->k == KB || x->k == KF || x->k == KP) {
        int fz2 = fz || x->k != KB;
        for (int i = 0; i < x->u.b.nk; i++) countg(x->u.b.kids[i], fz2, p);
    } else if (x->k == KS) {
        countg(x->u.s.a, fz, p);
        countg(x->u.s.b, fz, p);
    }
}

typedef struct { i64 lo, hi; Node *n; } GCell;

/* `add_part`: the consecutive cells `g` of the new prime under the box `bl`; the part is checked by the kernel's
   mirror (`dPart` with `dCheck`) */
static void addPart(const Cell *bl, int nbl, int par, const GCell *g, int ng, Part *p) {
    memset(p, 0, sizeof *p);
    for (int i = 0; i < ng; i++) countg(g[i].n, 0, p);
    bvInit(&p->h);
    Cell box[MAXB];
    for (int i = 0; i < ng; i++) {
        mkBox(g[i].lo, g[i].hi, bl, nbl, box);
        memset(&FZ, 0, sizeof FZ);
        dserg(g[i].n, box, nbl + 1, par, &p->h);
    }
    p->top = g[ng - 1].hi;
    p->a = g[0].lo;
    p->nbl = nbl;
    memcpy(p->bl, bl, sizeof(Cell) * nbl);
    p->par = par;
    p->ncs = ng - 1;
    p->cs = malloc(sizeof(i64) * (ng ? ng : 1));
    CHECK(p->cs, "out of memory");
    for (int i = 1; i < ng; i++) p->cs[i - 1] = g[i].lo;
    long pos;
    i128 c = runPart(p, &p->h, G.hl, 0, &pos);
    CHECK(pos >= bvLen(p->h.w, p->h.cap) && c < KC, "add_part: the part fails the kernel's mirror");
    p->c = c;
    double s = 0.0;
    for (int i = 0; i < ng; i++) s += g[i].n->secs;
    p->secs = s;
}
static void partFree(Part *p) {
    free(p->cs);
    bvFree(&p->h);
}

/* the pieces of a cut cell: a part (`kind` 0, its index) or a Buchstab step (`kind` 1) with its pieces */
typedef struct Piece Piece;
struct Piece {
    int kind, idx;
    Cell bl[MAXB];
    int nbl, par;
    i64 f;
    Cfg cfg;
    Piece **out;
    int nout;
    i128 cost;
};
typedef struct { Part *v; int n, cap; } Parts;
static int partsAdd(Parts *ps) {
    if (ps->n == ps->cap) {
        ps->cap = ps->cap ? 2 * ps->cap : 64;
        ps->v = realloc(ps->v, sizeof(Part) * ps->cap);
        CHECK(ps->v, "out of memory");
    }
    return ps->n++;
}
static Piece *pieceAdd(Piece *pc, Piece *x) {
    pc->out = realloc(pc->out, sizeof(Piece *) * (pc->nout + 1));
    CHECK(pc->out, "out of memory");
    pc->out[pc->nout++] = x;
    return x;
}
static Piece *partPiece(Parts *ps, const Cell *bl, int nbl, int par, GCell *g, int ng) {
    int i = partsAdd(ps);
    addPart(bl, nbl, par, g, ng, &ps->v[i]);
    Piece *x = calloc(1, sizeof(Piece));
    CHECK(x, "out of memory");
    x->kind = 0;
    x->idx = i;
    x->cost = ps->v[i].c;
    return x;
}
static double CAP;
static int LEVELS;
/* the cells of a step's new prime as `cut` goes through them: the part being filled (`group`, `gs`) */
typedef struct {
    Piece *pc;
    Parts *ps;
    const Cell *bl;
    int nbl, par;
    GCell *group;
    int ng, cap;
    double gs;
} CutCtx;
static Piece *cutg(const Node *node, const Cell *bl, int nbl, int par, Parts *ps);
static void cutFlush(CutCtx *x) {
    if (!x->ng) return;
    pieceAdd(x->pc, partPiece(x->ps, x->bl, x->nbl, !x->par, x->group, x->ng));
    x->ng = 0;
    x->gs = 0.0;
}
/* one cell of the new prime; with `split2`, a cell over `cap` that the plan cuts in two is taken as its two halves,
   each a cell of its own (`halves`) */
static void cutCell(CutCtx *x, i64 s, i64 e, Node *k) {
    if (G.split2 && k->k == KS && k->secs > CAP) {
        i64 mid = (s + e) / 2;
        cutCell(x, s, mid, k->u.s.a);
        cutCell(x, mid, e, k->u.s.b);
        return;
    }
    double t = k->secs;
    if (t > CAP && k->k == KB && x->nbl + 1 < LEVELS) {
        cutFlush(x);
        Cell box[MAXB];
        mkBox(s, e, x->bl, x->nbl, box);
        pieceAdd(x->pc, cutg(k, box, x->nbl + 1, !x->par, x->ps));
        return;
    }
    if (x->ng && x->gs + t > CAP) cutFlush(x);
    if (x->ng == x->cap) {
        x->cap = x->cap ? 2 * x->cap : 64;
        x->group = realloc(x->group, sizeof(GCell) * x->cap);
        CHECK(x->group, "out of memory");
    }
    x->group[x->ng].lo = s;
    x->group[x->ng].hi = e;
    x->group[x->ng].n = k;
    x->ng++;
    x->gs += t;
}
/* `cut` */
static Piece *cutg(const Node *node, const Cell *bl, int nbl, int par, Parts *ps) {
    memset(&FZ, 0, sizeof FZ);
    FC gd = guide(bl, nbl, node->u.b.sel);
    CHECK(gd.ok, "cut: no proposal for the plan's step");
    i64 f = gd.f;
    Vec cs = {0, 0, NULL};
    Strat S = {0, 0, {0, 0}, 0};
    Scuts(&S, bl, nbl, f, &cs);
    i64 *ends = malloc(sizeof(i64) * (cs.n + 2));
    CHECK(ends, "out of memory");
    int ne = kidEnds(&cs, f, bl[0].hi, node->u.b.bits, node->u.b.nbits, ends);
    free(cs.v);
    int nc = ne - 1;
    CHECK(nc == node->u.b.nk, "cut: the cells and the plans differ in number");
    Piece *pc = calloc(1, sizeof(Piece));
    CHECK(pc, "out of memory");
    pc->kind = 1;
    memcpy(pc->bl, bl, sizeof(Cell) * nbl);
    pc->nbl = nbl;
    pc->par = par;
    pc->f = f;
    pc->cfg = gd.cfg;
    CutCtx x = {pc, ps, bl, nbl, par, NULL, 0, 0, 0.0};
    for (int i = 0; i < nc; i++) cutCell(&x, ends[i], ends[i + 1], node->u.b.kids[i]);
    cutFlush(&x);
    free(x.group);
    free(ends);
    i128 tot = 0;
    for (int i = 0; i < pc->nout; i++) tot += pc->out[i]->cost;
    pc->cost = tot;
    return pc;
}
static void pieceFree(Piece *x) {
    for (int i = 0; i < x->nout; i++) pieceFree(x->out[i]);
    free(x->out);
    free(x);
}

/* ---------------------------------------------------------------------------------------------------------------
   The window's lines named by a part's hints (`hl_parts`, `transcode_hl`) */

/* `transcode_hl`: the part's hints, written without `hl`, with the records that name the lines */
static void transcode(Part *p) {
    long pos;
    BV *h = &p->h;
    long L = bvLen(h->w, h->cap);
    i128 c0 = runPart(p, h, 0, 1, &pos);
    CHECK(c0 == p->c && pos >= L && pos <= L + 4096, "transcode_hl: the part's hints do not pass without hl");
    for (int i = 0; i < D.nl; i++) CHECK(D.lv[i].has, "transcode_hl: a window's leaf without its rest");
    for (int i = 1; i < D.nl; i++) CHECK(D.lv[i - 1].at + D.lv[i - 1].oldw <= D.lv[i].at, "transcode_hl: order");
    BV nw;
    bvInit(&nw);
    long at = 0;
    for (int i = 0; i < D.nl; i++) {
        Leaf *l = &D.lv[i];
        bvPutSlice(&nw, h->w, h->cap, at, l->at - at);
        int lv = l->k == 0, kk = lv ? l->k2 : l->k;
        u64 recs[16], out[16];
        for (int j = 0; j < kk; j++) {
            long q = l->rs + (long)RC.EB * j;
            u64 v = 0;
            if (q < l->re) {
                int m = (int)(l->re - q < RC.EB ? l->re - q : RC.EB);
                v = bget(h->w, h->cap, q, m);
            }
            recs[j] = v;
        }
        hintHg(&l->rest, lv, kk, recs, out);
        int w = recW(l->rest.n, lv);
        for (int j = 0; j < kk; j++) bvPut(&nw, out[j], w);
        at = l->at + l->oldw;
    }
    long tail = (L > at ? L : at) - at;
    bvPutSlice(&nw, h->w, h->cap, at, tail);
    long L2 = bvLen(nw.w, nw.cap);
    i128 c1 = runPart(p, &nw, 1, 0, &pos);
    CHECK(c1 == p->c && pos >= L2, "transcode_hl: the transcoded part fails");
    bvFree(h);
    *h = nw;
}
/* `hl_parts` on one part: kept if its hints pass with `hl` (written so, or with no window's leaf), else
   transcoded; 1 if transcoded */
static int hlPart(Part *p) {
    static jmp_buf jb;
    static long pos;
    static int ok;
    ok = 0;
    if (setjmp(jb) == 0) {
        DIEJMP = &jb;
        long L = bvLen(p->h.w, p->h.cap);
        i128 c1 = runPart(p, &p->h, 1, 0, &pos);
        ok = c1 == p->c && pos >= L;
    } else
        ok = 0;
    DIEJMP = NULL;
    FZ.on = 0;
    if (ok) return 0;
    transcode(p);
    return 1;
}

/* ---------------------------------------------------------------------------------------------------------------
   Input and output: the plans as `emit` writes them, the parts and the pieces */
static char *GT;                    /* the input's tokens */
static char *gtok(void) {
    char *t = strtok(GT, " \t\r\n");
    GT = NULL;
    return t;
}
static char *gtokx(void) {
    char *t = gtok();
    CHECK(t, "the input ends early");
    return t;
}
static i64 gint(void) { return (i64)parseI(gtokx()); }

typedef struct { Memo **v; int n, cap; } MemoList;
static MemoList GMEMOS;
static Memo *memoOwn(int y) {
    Memo *e = calloc(1, sizeof(Memo));
    CHECK(e, "out of memory");
    e->y = (int8_t)y;
    e->state = MHINT;
    if (GMEMOS.n == GMEMOS.cap) {
        GMEMOS.cap = GMEMOS.cap ? 2 * GMEMOS.cap : 256;
        GMEMOS.v = realloc(GMEMOS.v, sizeof(Memo *) * GMEMOS.cap);
        CHECK(GMEMOS.v, "out of memory");
    }
    GMEMOS.v[GMEMOS.n++] = e;
    return e;
}
static void memosFree(void) {
    for (int i = 0; i < GMEMOS.n; i++) {
        free(GMEMOS.v[i]->hint);
        free(GMEMOS.v[i]);
    }
    GMEMOS.n = 0;
}
/* a plan in prefix order (`emit`'s tokens) */
static Node *parseNode(int fz) {
    char *t = gtokx();
    switch (t[0]) {
    case 'V': return mkLeaf(KV, fz);
    case 'E': return mkLeaf(KE, fz);
    case 'D': return mkLeaf(KD, fz);
    case 'R': {
        u32 mask = (u32)gint();
        int k = (int)gint();
        BV b;
        bvFromHex(&b, gtokx());
        Memo *e = memoOwn(0);
        HintX *hx = calloc(1, sizeof(HintX));
        CHECK(hx, "out of memory");
        long L = bvLen(b.w, b.cap);
        if (k == 0) {
            hx->lvf = 1;
            hx->k = (int)bget(b.w, b.cap, 0, 4);
            CHECK(hx->k <= MAXREC && L <= 4 + (long)RC.EB * hx->k, "a window's hint too long");
            for (int i = 0; i < hx->k; i++) hx->rec[i] = bget(b.w, b.cap, 4 + (long)RC.EB * i, RC.EB);
        } else {
            hx->lvf = 0;
            hx->k = k;
            CHECK(k <= MAXREC && L <= (long)RC.EB * k, "a window's hint too long");
            for (int i = 0; i < k; i++) hx->rec[i] = bget(b.w, b.cap, (long)RC.EB * i, RC.EB);
        }
        bvFree(&b);
        e->hint = hx;
        return mkR(fz, mask, e);
    }
    case 'Y': {
        u32 mask = (u32)gint();
        BV b;
        bvFromHex(&b, gtokx());
        Memo *e = memoOwn(1);
        HintY *hy = calloc(1, sizeof(HintY));
        CHECK(hy, "out of memory");
        hy->n = (int)bget(b.w, b.cap, 0, 4);
        hy->kH = (int)bget(b.w, b.cap, 4, 4);
        hy->kL = (int)bget(b.w, b.cap, 8, 4);
        int w = RC.EB + 2 + 3 * hy->n;
        CHECK(w <= 64 && bvLen(b.w, b.cap) <= 12 + (long)w * (hy->kH + hy->kL), "a corner's hint too long");
        for (int i = 0; i < hy->kH; i++) hy->recH[i] = bget(b.w, b.cap, 12 + (long)w * i, w);
        for (int i = 0; i < hy->kL; i++) hy->recL[i] = bget(b.w, b.cap, 12 + (long)w * (hy->kH + i), w);
        bvFree(&b);
        e->hint = hy;
        return mkR(fz, mask, e);
    }
    case 'B':
    case 'F':
    case 'P': {
        int k = t[0] == 'B' ? KB : t[0] == 'F' ? KF : KP;
        int sel = (int)gint(), nk = (int)gint();
        char *bs = gtokx();
        int nbits = strcmp(bs, "-") ? (int)strlen(bs) : 0;
        uint8_t *bits = malloc(nbits ? nbits : 1);
        CHECK(bits, "out of memory");
        for (int i = 0; i < nbits; i++) bits[i] = (uint8_t)(bs[i] - '0');
        Node **kids = malloc(sizeof(Node *) * (nk ? nk : 1));
        CHECK(kids, "out of memory");
        int fz2 = fz || k != KB;
        for (int i = 0; i < nk; i++) kids[i] = parseNode(fz2);
        return mkBFP(k, fz, sel, kids, nk, bits, nbits);
    }
    case 'S': {
        Node *a = parseNode(fz);
        Node *b = parseNode(fz);
        return mkS(fz, a, b);
    }
    }
    die("a malformed plan");
    return NULL;
}

/* ---------------------------------------------------------------------------------------------------------------
   The plans back from the hints (`RECUT`): the kernel's search led by a part's hints, read as the plan that wrote
   them, step by step (`dStep`'s codes: the step's kind, its configuration, its cells and the plans below them).
   A heavy cell kept in a cache has its parts' hints and its pieces, not its plan; its plan is the pieces' steps
   with the parts' cells under them, so it can be cut again (`cut` with the halves of a split cell). */
static Node *bSolve(const Ops *O, int nf, const Cell *bl, int nbl, int par, long *pos);

/* the bits of a step's plan (`kidCells`) from the ends of its cells: whether each proposed cut is taken */
static uint8_t *bitsOf(int frozen, const Cell *bl, int nbl, i64 f, i64 top, const i64 *ends, int nk, int *nbits) {
    Vec cs = {0, 0, NULL};
    Strat S = {frozen, 0, FZ.ctx, FZ.nb};
    Scuts(&S, bl, nbl, f, &cs);
    uint8_t *bits = malloc(cs.n + 1);
    CHECK(bits, "out of memory");
    int nb = 0, j = 1;
    i64 last = f;
    for (int i = 0; i < cs.n; i++) {
        i64 c = cs.v[i];
        if (last < c && c < top) {
            int b = j < nk && c == ends[j];
            bits[nb++] = (uint8_t)b;
            if (b) {
                last = c;
                j++;
            }
        }
    }
    free(cs.v);
    CHECK(j == nk, "recut: a cell's end that the strategy does not propose");
    *nbits = nb;
    return bits;
}
/* `dKidsC` as a plan: the cells' ends (nk + 1 of them) and their plans */
static Node **bKids(const Ops *O, int nrec, i64 top, const Cell *bl, int nbl, int par, i64 f, long *pos,
                    i64 **endsOut, int *nkOut) {
    i64 st, reg, e, last;
    if (!O->frozen) {
        st = stepOf(nbl + 1);
        reg = min64(top, tsub(DEN, loSum(bl, nbl)) / 2 + 2);
        e = tsub(bl[nbl - 1].lo, 1);
        last = tsub(DEN - 1, hiSum(bl, nbl));
    } else {
        int nch = (int)tsub(nbl, FZ.nb);
        st = nch < 2 ? G.hF : 2 * G.hF;
        reg = min64(top, tsub(FZ.ctx.hi + 1, loSum(bl, nch)) / 2 + 2);
        e = 0;
        last = tsub(tsub(FZ.ctx.lo, 1), hiSum(bl, nch));
    }
    CHECK(nbl + 1 <= MAXB, "recut: a box of too many primes");
    int cap = 16, n = 0;
    Node **kids = malloc(sizeof(Node *) * cap);
    i64 *ends = malloc(sizeof(i64) * (cap + 1));
    CHECK(kids && ends, "out of memory");
    ends[0] = f;
    Cell box[MAXB];
    i64 c = f, a = f;
    for (int it = 0; it < 4096; it++) {
        if (n + 1 >= cap) {
            cap *= 2;
            kids = realloc(kids, sizeof(Node *) * cap);
            ends = realloc(ends, sizeof(i64) * (cap + 1));
            CHECK(kids && ends, "out of memory");
        }
        if (bget(D.w, D.nw, *pos, 1) == 0) {
            *pos += 1;
            mkBox(a, top, bl, nbl, box);
            kids[n++] = bSolve(O, nrec, box, nbl + 1, par, pos);
            ends[n] = top;
            *endsOut = ends;
            *nkOut = n;
            return kids;
        }
        int j = (int)bget(D.w, D.nw, *pos + 1, 2);
        long hh;
        i64 p, nc;
        if (j != 3) {
            p = c;
            for (int s = 0; s < j + 1; s++) p = p + max64(1, min64(st, p / G.kappa));
            hh = *pos + 3;
            nc = p;
        } else {
            int t = (int)bget(D.w, D.nw, *pos + 3, 3);
            if (t <= 3) {
                p = c;
                for (int s = 0; s < t + 4; s++) p = p + max64(1, min64(st, p / G.kappa));
                hh = *pos + 6;
                nc = p;
            } else if (t == 4) {
                for (int s = 0; s < 7; s++) c = c + max64(1, min64(st, c / G.kappa));
                *pos += 6;
                continue;
            } else {
                p = t == 5 ? reg : t == 6 ? e : last;
                hh = *pos + 6;
                nc = c;
            }
        }
        CHECK(a < p && p < top, "recut: a cell out of the step's range");
        *pos = hh;
        mkBox(a, p, bl, nbl, box);
        kids[n++] = bSolve(O, nrec, box, nbl + 1, par, pos);
        ends[n] = p;
        a = p;
        c = nc;
    }
    die("recut: a step of too many cells");
    return NULL;
}
/* a window's leaf from its configuration: the plan's hint (`resX`'s records are the low `EB` bits of `resXH`'s) */
static Node *bLeafR(const DCfg *d, int fz) {
    if (d->c.kind == 4) {
        Memo *e = memoOwn(1);
        HintY *hy = calloc(1, sizeof(HintY));
        CHECK(hy, "out of memory");
        long rs = d->rs;
        hy->n = (int)bget(D.w, D.nw, rs, 4);
        hy->kH = (int)bget(D.w, D.nw, rs + 4, 4);
        hy->kL = (int)bget(D.w, D.nw, rs + 8, 4);
        int w = 15 + 3 * hy->n;
        CHECK(w <= 64 && w == RC.EB + 2 + 3 * hy->n, "recut: a corner's record");
        for (int i = 0; i < hy->kH; i++) hy->recH[i] = bget(D.w, D.nw, rs + 12 + (long)w * i, w);
        for (int i = 0; i < hy->kL; i++) hy->recL[i] = bget(D.w, D.nw, rs + 12 + (long)w * (hy->kH + i), w);
        e->hint = hy;
        return mkR(fz, d->c.sr, e);
    }
    Memo *e = memoOwn(0);
    HintX *hx = calloc(1, sizeof(HintX));
    CHECK(hx, "out of memory");
    hx->lvf = d->k == 0;
    hx->k = hx->lvf ? d->k2 : d->k;
    CHECK(hx->k <= MAXREC, "recut: too many intervals");
    int w = D.hl ? recW(__builtin_popcount(d->c.sr), hx->lvf) : RC.EB;
    for (int i = 0; i < hx->k; i++) hx->rec[i] = bget(D.w, D.nw, d->rs + (long)w * i, w) & emask();
    e->hint = hx;
    return mkR(fz, d->c.sr, e);
}
/* `dFlipCost` and `dFlipTree` as a plan: the reversal's step `F` (a box of the sign −) or `P` (+) */
static Node *bFlip(const Cell *bl, int n, int par, long *pos) {
    CHECK(flipOK(G.maxlen, bl, n), "recut: a reversal that the search does not take");
    Cell ctx = bl[n - 1];
    int nb = n - 1;
    Cell c = bl[0];
    i64 t = flipT(ctx);
    i64 lsb = loSum(bl, nb), hsb = hiSum(bl, nb);
    FZ.on = 1;
    FZ.e1 = tsub(DEN, ctx.hi) + par;
    FZ.e2 = tsub(DEN, ctx.lo) + 1 - par;
    FZ.Kb = 12 + DEN / bl[0].lo;
    memcpy(FZ.beta, bl, sizeof(Cell) * nb);
    FZ.nb = nb;
    FZ.ctx = ctx;
    FZD.Kb = FZ.Kb;
    FZD.cl = max64(1, tsub(FZ.e1, hsb));
    FZD.chh = tsub(FZ.e2, lsb);
    FZD.lomb = lomin(FZ.beta, nb);
    Ops O = {1, ctx, nb};
    int sel = (int)bget(D.w, D.nw, *pos, 4);
    FC fc = cfgJFd(FZD.Kb, FZD.cl, FZD.chh, FZ.beta, nb, FZD.lomb, FZ.beta, nb, pos);
    CHECK(1 <= fc.f && fc.f <= min64(c.lo, t) && okJm(FZ.beta, nb, fc.f, &fc.cfg), "recut: a reversal's step fails");
    i64 *ends;
    int nk, nbits;
    Node **kids = bKids(&O, G.fuel, t, FZ.beta, nb, !par, fc.f, pos, &ends, &nk);
    uint8_t *bits = bitsOf(1, FZ.beta, nb, fc.f, t, ends, nk, &nbits);
    free(ends);
    FZ.on = 0;
    return mkBFP(par ? KP : KF, 0, sel, kids, nk, bits, nbits);
}
static Node *bStep(const Ops *O, int nf, const Cell *bl, int nbl, int par, long *pos) {
    CHECK(nbl > 0 && Ogrd(O, nbl), "recut: a step that the search does not take");
    int fz = O->frozen;
    Cell x = bl[0];
    if (bget(D.w, D.nw, *pos, 1) == 0) {
        *pos += 1;
        DCfg d;
        dIg(bl, nbl, pos, &d);
        if (d.c.kind == 3 || d.c.kind == 4) return bLeafR(&d, fz);
        return mkLeaf(KE, fz);
    }
    if (bget(D.w, D.nw, *pos + 1, 1) == 0) {
        *pos += 2;
        int sel = (int)bget(D.w, D.nw, *pos, 4);
        FC fc = O->frozen ? cfgJFd(FZD.Kb, FZD.cl, FZD.chh, FZ.beta, FZ.nb, FZD.lomb, bl, nbl, pos)
                          : cfgJMd(bl, nbl, pos);
        CHECK(1 <= fc.f && fc.f <= x.lo && okJm(bl, nbl, fc.f, &fc.cfg), "recut: a Buchstab step fails");
        i64 *ends;
        int nk, nbits;
        Node **kids = bKids(O, nf - 1, x.hi, bl, nbl, !par, fc.f, pos, &ends, &nk);
        uint8_t *bits = bitsOf(O->frozen, bl, nbl, fc.f, x.hi, ends, nk, &nbits);
        free(ends);
        return mkBFP(KB, fz, sel, kids, nk, bits, nbits);
    }
    if (bget(D.w, D.nw, *pos + 2, 1) == 0) {
        *pos += 3;
        return mkLeaf(KD, fz);
    }
    if (bget(D.w, D.nw, *pos + 3, 1) == 0) {
        *pos += 4;
        CHECK(!O->frozen, "recut: a reversal over a frozen part");
        return bFlip(bl, nbl, par, pos);
    }
    if (bget(D.w, D.nw, *pos + 4, 1) == 0) {
        *pos += 5;
        i64 mid = (x.lo + x.hi) / 2;
        CHECK(x.lo < mid && mid < x.hi, "recut: a split of a cell too small");
        Cell box[MAXB];
        memcpy(box, bl, sizeof(Cell) * nbl);
        box[0].hi = mid;
        Node *a = bSolve(O, nf - 1, box, nbl, par, pos);
        box[0].lo = mid;
        box[0].hi = x.hi;
        Node *b = bSolve(O, nf - 1, box, nbl, par, pos);
        return mkS(fz, a, b);
    }
    if (bget(D.w, D.nw, *pos + 5, 1) == 0) {
        *pos += 6;
        return mkLeaf(KV, fz);
    }
    die("recut: the search's own alternative in a plan");
    return NULL;
}
static Node *bSolve(const Ops *O, int nf, const Cell *bl, int nbl, int par, long *pos) {
    CHECK(nf > 0, "recut: the search's fuel spent");
    return bStep(O, nf, bl, nbl, par, pos);
}

/* the pieces of a cut cell as read: a part (its index) or a step with its items */
typedef struct PIn PIn;
struct PIn {
    int kind, idx;
    Cell bl[MAXB];
    int nbl, par;
    i64 f;
    Cfg cfg;
    PIn **out;
    int nout;
};
static PIn *readPiece(void) {
    char *t = gtokx();
    PIn *x = calloc(1, sizeof(PIn));
    CHECK(x, "out of memory");
    if (!strcmp(t, "p")) {
        x->kind = 0;
        x->idx = (int)gint();
        return x;
    }
    CHECK(!strcmp(t, "b"), "a malformed piece");
    x->kind = 1;
    x->nbl = (int)gint();
    CHECK(x->nbl >= 1 && x->nbl <= MAXB, "a piece's box");
    for (int i = 0; i < x->nbl; i++) {
        x->bl[i].lo = gint();
        x->bl[i].hi = gint();
    }
    x->par = (int)gint();
    x->f = gint();
    x->cfg.kind = (int)gint();
    x->cfg.s0 = (u32)gint();
    x->cfg.sr = (u32)gint();
    x->cfg.s1 = (u32)gint();
    x->cfg.e = (int)gint();
    x->nout = (int)gint();
    x->out = calloc(x->nout ? x->nout : 1, sizeof(PIn *));
    CHECK(x->out, "out of memory");
    for (int i = 0; i < x->nout; i++) x->out[i] = readPiece();
    return x;
}
static void pinFree(PIn *x) {
    for (int i = 0; i < x->nout; i++) pinFree(x->out[i]);
    free(x->out);
    free(x);
}
/* the plan of a step of a cut cell: its parts' cells (their plans read from the hints) and its steps cut further,
   in order; the step's `sel` the first that `guide` reads as its floor and configuration (the plan's own, or one
   that gives the same cells) */
static Node *rebuild(const PIn *x, Part *parts, int np) {
    CHECK(x->kind == 1, "recut: a part where a step is due");
    int cap = 64, nk = 0;
    Node **kids = malloc(sizeof(Node *) * cap);
    i64 *ends = malloc(sizeof(i64) * (cap + 1));
    CHECK(kids && ends, "out of memory");
    ends[0] = x->f;
    Ops O = {0, {0, 0}, 0};
    for (int i = 0; i < x->nout; i++) {
        const PIn *y = x->out[i];
        if (y->kind == 0) {
            CHECK(y->idx >= 0 && y->idx < np, "recut: a part's index");
            Part *p = &parts[y->idx];
            CHECK(p->nbl == x->nbl && !memcmp(p->bl, x->bl, sizeof(Cell) * x->nbl) && p->par == !x->par,
                  "recut: a part that is not under its step");
            D.w = p->h.w;
            D.nw = p->h.cap;
            D.hl = G.hl;
            D.hook = 0;
            memset(&FZ, 0, sizeof FZ);
            long pos = 0;
            Cell box[MAXB];
            i64 a = p->a;
            for (int j = 0; j <= p->ncs; j++) {
                i64 b = j < p->ncs ? p->cs[j] : p->top;
                CHECK(a == ends[nk], "recut: the parts' cells do not follow each other");
                mkBox(a, b, p->bl, p->nbl, box);
                if (nk + 1 >= cap) {
                    cap *= 2;
                    kids = realloc(kids, sizeof(Node *) * cap);
                    ends = realloc(ends, sizeof(i64) * (cap + 1));
                    CHECK(kids && ends, "out of memory");
                }
                kids[nk++] = bSolve(&O, G.fuel, box, p->nbl + 1, p->par, &pos);
                ends[nk] = b;
                a = b;
            }
            CHECK(pos >= bvLen(p->h.w, p->h.cap), "recut: a part's hints longer than its plans");
        } else {
            CHECK(y->nbl == x->nbl + 1 && !memcmp(y->bl + 1, x->bl, sizeof(Cell) * x->nbl) && y->par == !x->par &&
                      y->bl[0].lo == ends[nk],
                  "recut: a step that is not under its step");
            if (nk + 1 >= cap) {
                cap *= 2;
                kids = realloc(kids, sizeof(Node *) * cap);
                ends = realloc(ends, sizeof(i64) * (cap + 1));
                CHECK(kids && ends, "out of memory");
            }
            kids[nk++] = rebuild(y, parts, np);
            ends[nk] = y->bl[0].hi;
        }
    }
    CHECK(ends[nk] == x->bl[0].hi, "recut: the step's cells do not reach its top");
    memset(&FZ, 0, sizeof FZ);
    int sel = -1;
    for (int s = 0; s < 16 && sel < 0; s++) {
        FC g = guide(x->bl, x->nbl, s);
        if (g.ok && g.f == x->f && cfgEq(&g.cfg, &x->cfg)) sel = s;
    }
    CHECK(sel >= 0, "recut: no proposal gives the step's floor and configuration");
    int nbits;
    uint8_t *bits = bitsOf(0, x->bl, x->nbl, x->f, x->bl[0].hi, ends, nk, &nbits);
    free(ends);
    return mkBFP(KB, 0, sel, kids, nk, bits, nbits);
}

static void putHexF(FILE *f, double x) { fprintf(f, "%a", x); }
static void writePart(FILE *f, const Part *p) {
    fprintf(f, "PART %lld %d", (long long)p->top, p->nbl);
    for (int i = 0; i < p->nbl; i++) fprintf(f, " %lld %lld", (long long)p->bl[i].lo, (long long)p->bl[i].hi);
    fprintf(f, " %d %d", p->par, p->ncs);
    for (int i = 0; i < p->ncs; i++) fprintf(f, " %lld", (long long)p->cs[i]);
    fprintf(f, " %lld ", (long long)p->a);
    putI(f, p->c);
    fputc(' ', f);
    putHexF(f, p->secs);
    fprintf(f, " %ld %d", p->nsteps, p->nord);
    for (int i = 0; i < p->nord; i++) {
        int k = p->ord[i] / 2, z = p->ord[i] % 2;
        fprintf(f, " %c %d %ld", KCH[k], z, p->cnt[k][z]);
    }
    fputc(' ', f);
    bvHex(f, p->h.w, p->h.cap);
    fputc('\n', f);
}
static void writePiece(FILE *f, const Piece *x) {
    if (x->kind == 0) {
        fprintf(f, " p %d", x->idx);
        return;
    }
    fprintf(f, " b %d", x->nbl);
    for (int i = 0; i < x->nbl; i++) fprintf(f, " %lld %lld", (long long)x->bl[i].lo, (long long)x->bl[i].hi);
    fprintf(f, " %d %lld %d %u %u %u %d %d", x->par, (long long)x->f, x->cfg.kind, x->cfg.s0, x->cfg.sr, x->cfg.s1,
            x->cfg.e ? 1 : 0, x->nout);
    for (int i = 0; i < x->nout; i++) writePiece(f, x->out[i]);
}
/* a heavy cell: its parts, then its pieces */
static void writeCut(FILE *f, const Piece *pc, const Parts *ps) {
    fprintf(f, "PARTS %d\n", ps->n);
    for (int i = 0; i < ps->n; i++) writePart(f, &ps->v[i]);
    fputs("PIECE", f);
    writePiece(f, pc);
    fputc('\n', f);
}
static void cutAndWrite(FILE *f, const Node *node, i64 a, i64 b) {
    Parts ps = {NULL, 0, 0};
    Cell box[1] = {{a, b}};
    Piece *pc = cutg(node, box, 1, 0, &ps);
    writeCut(f, pc, &ps);
    pieceFree(pc);
    for (int i = 0; i < ps.n; i++) partFree(&ps.v[i]);
    free(ps.v);
}

/* a part's fields: top nbl (lo hi)… par ncs cs… a c HEX */
static void readPartIn(Part *p) {
    memset(p, 0, sizeof *p);
    p->top = gint();
    p->nbl = (int)gint();
    CHECK(p->nbl + 1 <= MAXB, "a part's box of too many primes");
    for (int i = 0; i < p->nbl; i++) {
        p->bl[i].lo = gint();
        p->bl[i].hi = gint();
    }
    p->par = (int)gint();
    p->ncs = (int)gint();
    p->cs = malloc(sizeof(i64) * (p->ncs ? p->ncs : 1));
    CHECK(p->cs, "out of memory");
    for (int i = 0; i < p->ncs; i++) p->cs[i] = gint();
    p->a = gint();
    p->c = parseI(gtokx());
    bvFromHex(&p->h, gtokx());
}

/* the commands:
     ADD par nbl (lo hi)… ng (lo hi PLAN)…     `add_part` of a group of cells, answered by `PART …`
     CUT a b PLAN                              `cut` of a heavy cell of the first prime: `PARTS m`, the parts,
                                               `PIECE …`
     HL top nbl (lo hi)… par ncs cs… a c HEX   `hl_parts` of a part: `HLPART t HEX`, t = 1 if transcoded
     RECUT a b np (P part)… PIECE piece         a heavy cell kept in a cache (its parts, `P` and the fields of
                                               `HL`, and its pieces) cut again from its plan, read back from
                                               the hints: answered as `CUT`; `REBUILD` the same, answered by
                                               the plan (`TREE …`, as `emit` writes it)
   and `PART` is `PART top nbl (lo hi)… par ncs cs… a c secs steps ncnt (kind fz count)… HEX`; the pieces are
   `p i` (the part i of the cell) or `b nbl (lo hi)… par f kind s0 sr s1 e nout piece…`. */
static void genMain(FILE *in, FILE *out) {
    size_t cap = 1 << 20, n = 0;
    char *buf = malloc(cap);
    CHECK(buf, "out of memory");
    for (;;) {
        if (n + (1 << 16) > cap) {
            cap *= 2;
            buf = realloc(buf, cap);
            CHECK(buf, "out of memory");
        }
        size_t m = fread(buf + n, 1, cap - n - 1, in);
        if (m == 0) break;
        n += m;
    }
    buf[n] = 0;
    GT = buf;
    for (;;) {
        char *t = gtok();
        if (!t) break;
        if (!strcmp(t, "ADD")) {
            int par = (int)gint(), nbl = (int)gint();
            CHECK(nbl + 1 <= MAXB, "ADD: a box of too many primes");
            Cell bl[MAXB];
            for (int i = 0; i < nbl; i++) {
                bl[i].lo = gint();
                bl[i].hi = gint();
            }
            int ng = (int)gint();
            CHECK(ng >= 1, "ADD: no cells");
            GCell *g = malloc(sizeof(GCell) * ng);
            CHECK(g, "out of memory");
            for (int i = 0; i < ng; i++) {
                g[i].lo = gint();
                g[i].hi = gint();
                g[i].n = parseNode(0);
            }
            Part p;
            addPart(bl, nbl, par, g, ng, &p);
            writePart(out, &p);
            partFree(&p);
            for (int i = 0; i < ng; i++) nfree(g[i].n);
            free(g);
            memosFree();
        } else if (!strcmp(t, "CUT")) {
            i64 a = gint(), b = gint();
            Node *node = parseNode(0);
            CHECK(node->k == KB, "CUT: a plan that is not a Buchstab step");
            cutAndWrite(out, node, a, b);
            nfree(node);
            memosFree();
        } else if (!strcmp(t, "HL")) {
            Part p;
            readPartIn(&p);
            int tr = hlPart(&p);
            fprintf(out, "HLPART %d ", tr);
            bvHex(out, p.h.w, p.h.cap);
            fputc('\n', out);
            partFree(&p);
        } else if (!strcmp(t, "RECUT") || !strcmp(t, "REBUILD")) {
            int recut = !strcmp(t, "RECUT");
            i64 a = gint(), b = gint();
            int np = (int)gint();
            Part *parts = calloc(np ? np : 1, sizeof(Part));
            CHECK(parts, "out of memory");
            for (int i = 0; i < np; i++) {
                CHECK(!strcmp(gtokx(), "P"), "RECUT: a part expected");
                readPartIn(&parts[i]);
            }
            CHECK(!strcmp(gtokx(), "PIECE"), "RECUT: the pieces expected");
            PIn *x = readPiece();
            CHECK(x->kind == 1 && x->nbl == 1 && x->bl[0].lo == a && x->bl[0].hi == b && !x->par,
                  "RECUT: the pieces of another cell");
            Node *node = rebuild(x, parts, np);
            if (recut)
                cutAndWrite(out, node, a, b);
            else {
                fputs("TREE ", out);
                emit(out, node);
                fputc('\n', out);
            }
            nfree(node);
            pinFree(x);
            for (int i = 0; i < np; i++) partFree(&parts[i]);
            free(parts);
            memosFree();
        } else
            die("an unknown command");
        fflush(out);
    }
    free(buf);
}
