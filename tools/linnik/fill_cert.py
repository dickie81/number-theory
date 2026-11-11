#!/usr/bin/env python3
"""fill_cert.py [--check] [--stats] [--out DIR] [--try H DEPTH KAPPA DEPTHR HR HQ [a/b] [--norev]]: the search with no Type II
window at L = 2165/1000, searched as the kernel searches it, cut into parts, and the Lean files of the theorem there.

Below 13/6 the Type II estimate in one variable has no window, and a decomposition has the estimate in two
variables alone. Its rest is a product of primes of exponent between 1/2000 and about (L − 2)/0.558 in base q, and
a term whose primes are all larger has none among them. For such a term at a floor, the comparison takes its rest
from the primes of its own tree of Buchstab steps below the floor (`SieveFillComp.prop6_fill`): the first of them
join the first variable until its product enters the window, and the next ones are the rest until their product
reaches q^(1/2000). The tests are `SieveAd.fillTests` (`lib/pnt/SieveAdFillDefs.lean`): `okI2` for a box, and at a
floor `okJ2` (the rest among the box's primes) or, for a configuration of kind 2, `okJ3` (the rest among the
tree's); they are sound (`lib/pnt/SieveAdFill.lean`). The search is `rev_cert.py`'s, with role reversal
(`SieveAd.solveG` with the nodes `SieveAd.opsR`), and its strategy proposes no window and the floors of `okJ3`
(`lib/pnt/SieveAdFillSearchDefs.lean`: `fmax3`, `tryJ3`, `propJ3`, `propJF`, `stratGF`, `stratKF`). This script is
that search in Python, definition by definition, on top of `rev_cert.py` and `tree_cert.py`:

  * `TestsF`: `fillTests` (`chkJ3`, `okJ3`);
  * `FillSearch`: `rev_cert.RevSearch` with `propJ3` and `propJF` for `propJ`, and `propI2` alone for the boxes.

The root is the comparison of the empty box at the floor that `propJ3` gives, x^0.0489 at 2165/1000, and the first
prime's cells run from there to x^(1/2).

It writes `lib/pnt/SieveFill21650.lean` (the exponent, the strategies and the nodes),
`lib/pnt/SieveTree21650P<k>.lean` (the parts, each by `decide +kernel`) and `lib/pnt/Linnik21650.lean` (the route,
the bound from the parts, and the theorem). With `--check`, nothing is written: the files are regenerated in memory
and compared with `lib/pnt` (exit 1 on a difference). With `--stats`, the search's work and the parts' predicted
times are printed. With `--out DIR`, the files are written to `DIR`. With `--try`, only the search is run, with other parameters (and at another exponent, if given;
without the reversal, with `--norev`), and its cost is printed.

Values (11 November 2026): the search costs 0.95109 K on 3607561 boxes, with 8720 reversals taken of 18611 tried
(`--try 0.005 6 10 3 0.012 0.02`). The bound of the files costs 0.95053 K (eleven cells are cut in two): 2353 parts
in 62 files, 853 cells with their own Buchstab step and 431 dropped outright, which the kernel checks in 14472
seconds in all (82 to 405 a file, with at most 3.1 GB); the prediction of a part's time, calibrated on the search
with the window, is more than twice what the kernel takes here (34035 seconds in all), so the parts are shorter
than CAP says. `--try 0.006 6 10 3 0.012 0.02`: 1.05186, 2272818 boxes.

Needs Python 3 only. Five minutes.
"""
import os
import sys
import textwrap

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tree_cert as tc  # noqa: E402
import rev_cert as rc  # noqa: E402
from tree_cert import DEN, K, cdiv, tsub, loSum, hiSum, vanishOK, dropC, mSum, wrap, nat  # noqa: E402
from rev_cert import geoCuts, groups, cell, box, bool_, chain  # noqa: E402

PNT = tc.PNT
# the exponent and the strategy
TAG, LNUM, LDEN = '21650', 2165, 1000
HI, DEPTH, WMIN, FUEL = round(0.005 * DEN), 6, round(0.0005 * DEN), 200
KAPPA, HR, DEPTHR, HQ = 10, round(0.012 * DEN), 3, round(0.02 * DEN)
# the parts: at most CAP predicted seconds each (a cell that is not cut further may be longer), a file of at most
# PMAX parts and FCAP predicted seconds; a cell is cut by the next prime's cells down to the LEVELS-th prime
CAP, PMAX, FCAP, LEVELS = 22.0, 40, 600.0, 5
# a cell that the search drops after more than CAPD predicted seconds is dropped outright, without the search
CAPD = 6.0


class TestsF(tc.Tests):
    """`SieveAd.fillTests` at `IBPar ⟨Ln, Ld⟩` (SieveAdFillDefs.lean)."""

    def __init__(self, Ln, Ld):
        self.Ln, self.Ld = Ln, Ld
        self.U1 = self.U2 = self.V = 0
        self.fillLo = cdiv(Ld * DEN + 2000 * Ln, 2000 * Ln)

    def chkJ3(self, bl, f, s0, s1, e, u, v, t, r1, r2):
        D1 = mSum(1, bl, s1) + (t + r2 if e else 0)
        D2 = tsub(hiSum(bl), mSum(1, bl, s1)) + (0 if e else t + r2)
        return (0 < f and len(bl) <= 13 and all(f <= c[0] <= c[1] <= DEN for c in bl)
                and self.zone(r1, r2, u, v) and r1 + f < r2 and u + f < v and u <= t + mSum(0, bl, s0)
                and mSum(1, bl, s0) < v and self.leaves(D1, D2))

    def okJ3(self, bl, f, cfg):
        _, s0, _, s1, e = cfg
        r1, r2 = self.fillLo, self.fillLo + f + 1
        u, v = self.uOf(r1), self.vOf(r2)
        return self.chkJ3(bl, f, s0, s1, e, u, v, tsub(u, mSum(0, bl, s0)), r1, r2)

    def okI(self, bl, cfg):
        return self.chkI2(bl, cfg[1], cfg[2])

    def okJ(self, bl, f, cfg):
        return self.okJ3(bl, f, cfg) if cfg[0] == 2 else self.okJ2(bl, f, cfg)


class FillSearch(rc.RevSearch):
    """`SieveAd.solveG (opsR fillTests (stratKF κ hR depthR wmin) fuel (cutsQ hQ)) fillTests (stratGF κ hI depth wmin)`,
    with counts of its work (SieveAdFillSearchDefs.lean)."""

    def __init__(self, T, hI, depth, wmin, kappa, hR, depthR, hQ, fuel, rev=True):
        super().__init__(T, hI, depth, wmin, kappa, hR, depthR, hQ, fuel, rev)
        self.W.update(okJ3=0)
        self.u3 = self.uOfF(self.restLo)
        self.fmax3 = min(tsub(self.vA, self.restLo + 3 + self.u3) // 2,
                         tsub(self.vB, self.vC * (self.restLo + 2) + (self.u3 + 1) * self.uC) // (self.uC + self.vC))

    def anyI(self, bl):
        for cfg in self.propI2(bl, loSum(bl)):
            self.W['okI2'] += 1
            if self.T.okI(bl, cfg):
                return True
        return False

    def tryJ3(self, bl, ls, hs, f):
        r2 = self.restLo + f + 1
        b = self.bestSub(self.vOfF(r2), 0, bl, 1, 0, 0, 0, ls, (0, 0))
        sp = self.leavesOf(bl, hs, tsub(self.u3, b[0]) + r2)
        return None if sp is None else (f, (2, b[1], 0, sp[0], sp[1]))

    def propJ3(self, bl, ls, hs, n, f):
        for _ in range(n):
            r = self.tryJ3(bl, ls, hs, f)
            if r is not None:
                return r
            f = 3 * f // 4
        return None

    def propJ(self, bl):
        """`propJF bl`."""
        lomin, ls, hs = min([DEN] + [c[0] for c in bl]), loSum(bl), hiSum(bl)
        if self.T5 < hs:
            return []
        r = self.propJ2(bl, lomin, ls, hs)
        out = []
        if r[0] < lomin:
            r3 = self.propJ3(bl, ls, hs, 8, min(lomin, self.fmax3))
            if r3 is not None and r[0] < r3[0]:
                out.append(r3)
        if r[1] is not None:
            out.append(r)
        return out

    def firstJ(self, bl, lo0, ps):
        for f, cfg in ps:
            self.W['okJ3' if cfg[0] == 2 else 'okJ2'] += 1
            if 0 < f <= lo0 and self.T.okJ(bl, f, cfg):
                return f, cfg
        return None


def root_of(S):
    """The floor and the configuration of the root: the first proposal for the empty box."""
    fj = S.firstJ([], DEN, S.propJ([]))
    assert fj is not None and fj[0] <= DEN // 2 + 1
    return fj


def rowCuts(S, f0):
    """The ends of the cells of the first prime: steps of at most hI and at most the exponent over κ from the
    root's floor to DEN/2 + 1, and a thin cell at the top."""
    return sorted(set([f0] + geoCuts(S.kappa, S.hI, DEN // 2 + 1, 4096, f0)) | {DEN // 2 - S.wmin})


def search_only(h, depth, kappa, depthR, hR, hQ, ln, ld, rev=True):
    """The cost of the search with other parameters, the number of boxes searched and the reversals' counts; with
    `rev` false, the search without the reversal."""
    S = FillSearch(TestsF(ln, ld), round(h * DEN), depth, WMIN, kappa, round(hR * DEN), depthR, round(hQ * DEN),
                   FUEL, rev)
    sys.setrecursionlimit(100000)
    f0, _ = root_of(S)
    cuts = rowCuts(S, f0)
    return S.kidsR(DEN // 2 + 1, [], False, cuts[1:-1], cuts[0], 4 * K), S.W['calls'], S.stat, f0


def pred(w):
    """The kernel's time on a part, in seconds, from the search's work in it: `rev_cert.pred`, with the tests of the
    comparison with the rest among the tree's primes counted with the others."""
    return rc.pred(dict(w, okJ2=w['okJ2'] + w['okJ3']))


def plan():
    """The parts of the search and the bound's assembly, as `rev_cert.plan`:
    (T, f0, cfg0, searched, stat, parts, root, total)."""
    T = TestsF(LNUM, LDEN)
    S = FillSearch(T, HI, DEPTH, WMIN, KAPPA, HR, DEPTHR, HQ, FUEL)
    sys.setrecursionlimit(100000)
    f0, cfg0 = root_of(S)
    cuts = rowCuts(S, f0)
    assert cuts[0] == f0 and cuts[-1] == DEN // 2 + 1 and T.okJ([], f0, cfg0)
    parts = []
    count = dict.fromkeys(('buch', 'halved', 'long', 'drop'), 0)
    saved = [0.0]

    def cell_of(bl, par, s, e):
        c, w = S.work(lambda: S.solveR([(s, e)] + bl, par, K))
        return s, e, c, w

    def part(top, bl, par, cells):
        cs = [c[0] for c in cells[1:]]
        if len(cells) == 1:
            c, w = cells[0][2], cells[0][3]
        else:
            c, w = S.work(lambda: S.kidsR(top, bl, par, cs, cells[0][0], K))
        assert c < K
        count['long'] += pred(w) > 1.5 * CAP
        parts.append((top, bl, par, cs, cells[0][0], c, w))
        return len(parts) - 1

    def piece_cost(p):
        return parts[p[1]][5] if p[0] == 'part' else p[3] if p[0] == 'drop' else p[6]

    def decompose(bl, par, c):
        if vanishOK(bl) or S.anyI(bl) or len(bl) >= DEPTH:
            return None
        fj = S.firstJ(bl, bl[0][0], S.propJ(bl))
        if fj is None:
            return None
        f, cfg = fj
        ends = [f]
        for x in S.cutsOfG(bl, f):
            if ends[-1] < x < bl[0][1]:
                ends.append(x)
        ends.append(bl[0][1])
        cells = [cell_of(bl, not par, s, e) for s, e in zip(ends, ends[1:])]
        if sum(x[2] for x in cells) > c:
            return None
        ps = pieces(bl, not par, cells)
        count['buch'] += 1
        return ('buch', bl, par, f, cfg, ps, sum(piece_cost(p) for p in ps))

    def pieces(bl, par, cells):
        out, light = [], []

        def flush():
            for g in groups_f(light, CAP):
                out.append(('part', part(g[-1][1], bl, par, g)))
            light.clear()

        def handle(x):
            s, e, c, w = x
            if pred(w) > CAPD and dropC([(s, e)] + bl, par) == c:
                flush()
                out.append(('drop', [(s, e)] + bl, par, c))
                count['drop'] += 1
                saved[0] += pred(w)
                return
            if pred(w) <= CAP:
                light.append(x)
                return
            sub = decompose([(s, e)] + bl, par, c) if len(bl) + 1 < LEVELS else None
            if sub is not None:
                flush()
                out.append(sub)
                return
            mid = (s + e) // 2
            if s < mid < e:
                h1, h2 = cell_of(bl, par, s, mid), cell_of(bl, par, mid, e)
                if h1[2] + h2[2] <= c and max(pred(h1[3]), pred(h2[3])) <= 0.75 * pred(w):
                    count['halved'] += 1
                    handle(h1)
                    handle(h2)
                    return
            light.append(x)

        for x in cells:
            handle(x)
        flush()
        return out

    rows = [cell_of([], False, a, b) for a, b in zip(cuts, cuts[1:])]
    searched, stat = dict(S.W), dict(S.stat)
    root = pieces([], False, rows)
    assert S.minfuel > 100
    total = sum(piece_cost(p) for p in root)
    assert total < K
    stat.update(count)
    stat['saved'] = round(saved[0])
    return T, f0, cfg0, searched, stat, parts, root, total


def groups_f(cells, cap):
    """`rev_cert.groups` with this file's `pred`."""
    out, cur, w = [], [], None
    for c in cells:
        w2 = c[3] if w is None else rc.addw(w, c[3])
        if cur and pred(w2) > cap:
            out.append(cur)
            cur, w2 = [], c[3]
        cur.append(c)
        w = w2
    if cur:
        out.append(cur)
    return out


# the Lean files

def cfg_(cfg):
    return f'⟨{cfg[0]}, {cfg[1]}, {cfg[2]}, {cfg[3]}, {bool_(cfg[4])}⟩'


def part_stmt(k, p):
    top, bl, par, cs, a, c, _ = p
    return wrap(f'theorem tree{TAG}_{k} : kids (solveG ops{TAG} fillTests strat{TAG} {FUEL}) {nat(top)} {box(bl)} '
                f'{bool_(par)} [{", ".join(map(str, cs))}] {a} K ≤ {c} :=\xa0by\xa0decide\xa0+kernel').replace('\xa0', ' ')


def fill_file():
    return f"""/-
# The exponent, the strategies and the nodes of the search with no window at `L = {LNUM}/{LDEN}`

Generated by `tools/linnik/fill_cert.py`; do not edit by hand.

The bilinear Type I rule's exponent `{LNUM}/{LDEN}` (`ibPar{TAG}`), and:

* `strat{TAG}`, the strategy of the search: `SieveAd.stratGF` with cells of side at most `{HI}/DEN` (`0.005`) and at
  most the exponent over `{KAPPA}`, boxes of fewer than `{DEPTH}` primes decomposed, and cells wider than
  `{WMIN}/DEN` (`0.0005`) cut for want of a test;
* `stratK{TAG}`, the strategy of a reversal's trees: `SieveAd.stratKF` with chains of fewer than `{DEPTHR}` primes, in
  cells of side at most `{HR}/DEN` (`0.012`) and at most the exponent over `{KAPPA}`;
* `ops{TAG}`, the nodes of the search: `SieveAd.opsR` with the tests `SieveAd.fillTests` and those trees, searched
  with the fuel `{FUEL}`, and the smaller prime of a cofactor of two primes in cells of side at most `{HQ}/DEN`
  (`0.02`).

The file imports `SieveAdFillSearchDefs.lean`; so neither it nor the part files (`SieveTree{TAG}P1.lean` …) load
more of `Mathlib` than `Mathlib.Data.Nat.Notation`.
-/
import SieveAdFillSearchDefs

namespace SieveCert

/-- **The bilinear Type I rule's exponent** at `L = {LNUM}/{LDEN}`. -/
@[instance_reducible] def ibPar{TAG} : IBPar := ⟨{LNUM}, {LDEN}⟩

end SieveCert

namespace SieveAd

open SieveCert

/-- **The strategy of the search at `{LNUM}/{LDEN}`.** -/
def strat{TAG} : Strat := @stratGF ibPar{TAG} {KAPPA} {HI} {DEPTH} {WMIN}

/-- **The strategy of a reversal's trees at `{LNUM}/{LDEN}`.** -/
def stratK{TAG} : Cell → ℕ → Strat := @stratKF ibPar{TAG} {KAPPA} {HR} {DEPTHR} {WMIN}

/-- **The nodes of the search at `{LNUM}/{LDEN}`**: those of a tree, and role reversal. -/
def ops{TAG} : Ops := opsR (@fillTests ibPar{TAG}) stratK{TAG} {FUEL} (cutsQ {HQ})

end SieveAd
"""


def part_files(parts):
    """The parts in files: consecutive parts, at most PMAX of them and FCAP predicted seconds a file."""
    files, cur, t = [], [], 0.0
    for k, p in enumerate(parts):
        tp = pred(p[6])
        if cur and (len(cur) >= PMAX or t + tp > FCAP):
            files.append(cur)
            cur, t = [], 0.0
        cur.append(k)
        t += tp
    if cur:
        files.append(cur)
    out = {}
    for i, g in enumerate(files, 1):
        secs = sum(pred(parts[k][6]) for k in g)
        desc = textwrap.fill(
            f'File {i} of {len(files)}: the parts `tree{TAG}_{g[0]}` … `tree{TAG}_{g[-1]}` of the search with no '
            f'window at `L = {LNUM}/{LDEN}`, with the strategy `SieveAd.strat{TAG}` and the nodes `SieveAd.ops{TAG}` '
            f'({len(g)} parts, predicted {secs:.0f} s of the kernel). A part is a range of consecutive cells of one '
            f'prime: the sum of the costs that the search (`SieveAd.solveG`) returns on them, each searched with the '
            f'limit that the cells before it leave of `K`, is at most the part\'s bound, by `decide +kernel`, one at '
            f'a time (`Elab.async false`). `Linnik{TAG}.lean` makes the bound of the first term from the parts.',
            width=116)
        body = '\n\n'.join(part_stmt(k, parts[k]) for k in g)
        out[f'SieveTree{TAG}P{i}.lean'] = f"""/-
# The search with no window at `L = {LNUM}/{LDEN}`, parts {g[0]}–{g[-1]} of {len(parts)}

Generated by `tools/linnik/fill_cert.py`; do not edit by hand.

{desc}

The file imports `SieveFill{TAG}.lean`.
-/
import SieveFill{TAG}

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveAd

open SieveCert

section

attribute [local instance] ibPar{TAG}

{body}

end

end SieveAd

#print axioms SieveAd.tree{TAG}_{g[0]}
#print axioms SieveAd.tree{TAG}_{g[-1]}
"""
    return out


def final_file(f0, cfg0, parts, root, total, nfiles):
    LN = f'{LNUM} / {LDEN}'
    nodes = []

    def term(p):
        """The Lean term of a piece; a cell with its own Buchstab step becomes a theorem `node{TAG}_<i>` first."""
        if p[0] == 'part':
            return f'part{TAG} tree{TAG}_{p[1]} (by decide)'
        if p[0] == 'drop':
            return f'pr_drop sound{TAG} (bl := {box(p[1])}) (par := {bool_(p[2])}) (dc := {p[3]}) (by decide +kernel)'
        _, bl, par, f, cfg, ps, c = p
        items = [term(x) for x in ps]
        i = len(nodes)
        what = ('first', 'second', 'third', 'fourth', 'fifth')[len(bl) - 1]
        doc = wrap(f"/-- The cell `{cell(bl[0])}` of the {what} prime: Buchstab's identity at the floor `{f}`, and the "
                   f"pieces of the next prime's range. -/", '')
        nodes.append(f"""{doc}
theorem node{TAG}_{i} : PR {box(bl)} {bool_(par)} {c} :=
  pr_mono (pr_buch sound{TAG} (x := {cell(bl[0])}) (b := {box(bl[1:])}) (par := {bool_(par)}) (f := {f})
    (cfg := {cfg_(cfg)}) (by decide) (by decide +kernel) (
{chain(items)})) (by decide)""")
        return f'node{TAG}_{i}'

    items = [term(p) for p in root]

    def drops(ps):
        return sum(1 if p[0] == 'drop' else drops(p[5]) if p[0] == 'buch' else 0 for p in ps)

    ndrop = drops(root)
    imports = '\n'.join(f'import SieveTree{TAG}P{i}' for i in range(1, nfiles + 1))
    return f"""/-
# Linnik's theorem with exponent `{LN}`, by a search with no Type II window

Built against PrimeNumberTheoremAnd at commit 650d312 (`lib/vendor/pnt-plus`). Generated by
`tools/linnik/fill_cert.py`; do not edit by hand.

Plain statement (`linnik_{TAG}`): there is `K` such that for every `q ≥ 1` and every `a` prime to `q` there is a prime
`p ≡ a (mod q)` with `p ≤ K·q^{{{LN}}}`, with no hypothesis. The exponent is below `13/6`, where the Type II
estimate in one variable has no window: the route is at `L = {LN}` (`route{TAG}`) and its only estimate is the one
in two variables. The sieve's decomposition is chosen term by term, as a tree of Buchstab steps (`SieveAdDefs.lean`)
with role reversal (`SieveAdRevDefs.lean`), and the tests are `SieveAd.fillTests`: the estimate in two variables for
a box, and at a floor the comparison whose rest is a product of the box's primes or, for a box that has none of
that size, of the primes of the comparison's own tree (`SieveFillComp.prop6_fill`). Nothing is written out: the
kernel runs a search (`SieveAd.solveG`, with the strategy `SieveAd.strat{TAG}` and the nodes `SieveAd.ops{TAG}`) in
{len(parts)} parts, {nfiles} files (`SieveTree{TAG}P1.lean` … `SieveTree{TAG}P{nfiles}.lean`), and a cost that the search
returns below its limit bounds the term (`SieveAd.pr_of_kids`).

* `route{TAG}`, `routeOK{TAG}`, `ibFits{TAG}`: the route and its exponent.
* `sound{TAG}`, `soundX{TAG}`: the tests are sound, and sound under two more atoms (`SieveAd.fillTests_sound`,
  `SieveAd.fillTests_soundX`).
* `part{TAG}`: a part of the search bounds its term.
* `node{TAG}_0` … `node{TAG}_{len(nodes) - 1}`: the {len(nodes)} cells whose search is cut into parts by the cells of the next prime:
  the cell's own Buchstab step (`SieveAd.pr_buch`), and the pieces below it. A piece is a part, another such cell,
  or a cell dropped outright (`SieveAd.pr_drop`): one of the {ndrop} that the search drops after a long search for a
  tree that costs less.
* `tree{TAG}`: the term of the box of the first prime, of the sign `−`, is at most `(c/K + o(1))x/(φ(q) log x)` in
  `𝒜` minus the comparison set, with `c = {total}`, which is `{total / K:.5f}·K`.
* `linnik_{TAG}`: `SieveAd.linnik_pr` at them, with the root at the floor `{f0}/DEN`, by the comparison with the rest
  among the tree's primes.

The file imports `SieveAdRevSearch.lean`, `SieveAdFill.lean` and the part files.
-/
import SieveAdRevSearch
import SieveAdFill
{imports}

namespace Linnik{TAG}

open SieveCert SieveRoute SieveQ SieveAd

/-- **The route's parameters at `{LN}`**: `L = {LN}`; the window's ends, `1/3` and `1/2`, are not used. -/
@[instance_reducible] noncomputable def route{TAG} : Route := ⟨{LN}, 1 / 3, 1 / 2⟩

/-- `route{TAG}` is a route: `2 < L ≤ 5/2` and `0 < w₁ < w₂ < 1`. -/
theorem routeOK{TAG} : @RouteOK route{TAG} :=
  @RouteOK.mk route{TAG} (show (2 : ℝ) < {LN} by norm_num) (show (0 : ℝ) < 1 / 3 by norm_num)
    (show (1 / 3 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    (show ({LN} : ℝ) ≤ 5 / 2 by norm_num)

/-- `ibPar{TAG}`'s exponent `Lnum/Lden` is the route's `L = {LN}`. -/
theorem ibFits{TAG} : @IBFits route{TAG} ibPar{TAG} :=
  @IBFits.mk route{TAG} ibPar{TAG} (show (({LNUM} : ℕ) : ℝ) / (({LDEN} : ℕ) : ℝ) = {LN} by norm_num)

section

attribute [local instance] route{TAG} routeOK{TAG} ibPar{TAG} ibFits{TAG}

/-- The tests at `{LN}` are sound. -/
theorem sound{TAG} : (fillTests).Sound := fillTests_sound

/-- The tests at `{LN}` are sound under two more atoms. -/
theorem soundX{TAG} : (fillTests).SoundX := fillTests_soundX

/-- **A part of the search bounds its term**: `SieveAd.pr_of_kids` at the route. -/
theorem part{TAG} {{top : ℕ}} {{bl : List Cell}} {{par : Bool}} {{cs : List ℕ}} {{a c : ℕ}}
    (h : kids (solveG ops{TAG} fillTests strat{TAG} {FUEL}) top bl par cs a K ≤ c) (hc : c < K) :
    PR ((a, top) :: bl) par c :=
  pr_of_kids sound{TAG} soundX{TAG} stratK{TAG} {FUEL} (cutsQ {HQ}) strat{TAG} {FUEL} h hc

{chr(10).join(n + chr(10) for n in nodes)}
/-- **The first term at `{LN}`**: the term of the box of the first prime, with the cell `({f0}, DEN/2 + 1)`, of the
sign `−`, is at most `(c/K + o(1))x/(φ(q) log x)` in `𝒜` minus the comparison set, with `c = {total}`, below `K`. -/
theorem tree{TAG} : PR [({f0}, DEN / 2 + 1)] false {total} :=
  pr_mono (
{chain(items)}) (by decide)

/-- **Linnik's theorem with exponent `{LN}`, by a search with no Type II window**: there is `K` such that for every
`q ≥ 1` and every `a` prime to `q` there is a prime `p ≡ a (mod q)` with `p ≤ K·q^{{{LN}}}`. -/
theorem linnik_{TAG} : ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ ({LN} : ℝ) :=
  linnik_pr sound{TAG} {f0} {cfg_(cfg0)} (by decide) (by decide +kernel) tree{TAG} (by decide)

end

end Linnik{TAG}

#print axioms Linnik{TAG}.tree{TAG}
#print axioms Linnik{TAG}.linnik_{TAG}
"""


def generate():
    T, f0, cfg0, searched, stat, parts, root, total = plan()
    files = {f'SieveFill{TAG}.lean': fill_file()}
    pf = part_files(parts)
    files.update(pf)
    files[f'Linnik{TAG}.lean'] = final_file(f0, cfg0, parts, root, total, len(pf))
    return files, (searched, stat, parts, root, total)


def main():
    if '--try' in sys.argv:
        a = [x for x in sys.argv[sys.argv.index('--try') + 1:] if x != '--norev']
        ln, ld = map(int, a[6].split('/')) if len(a) >= 7 else (LNUM, LDEN)
        c, n, st, f0 = search_only(float(a[0]), int(a[1]), int(a[2]), int(a[3]), float(a[4]), float(a[5]), ln, ld,
                                   '--norev' not in sys.argv)
        print(f'L = {ln}/{ld}, no window, root floor {f0 / DEN:.5f}, cells of side {a[0]} and exponent/{a[2]}, '
              f'depth {a[1]}; reversals: chains below {a[3]} primes, cells {a[4]}, cofactor cells {a[5]}: '
              f'cost/K = {c / K:.5f}; {n} boxes searched; {st}')
        return 0
    files, (searched, stat, parts, root, total) = generate()
    times = [pred(p[6]) for p in parts]
    print(f'L = {LNUM}/{LDEN}, no window: cost/K = {total / K:.5f}; {searched["calls"]} boxes searched; '
          f'reversals tried {stat["revtry"]}, taken {stat["revwin"]}; {len(parts)} parts in {len(files) - 2} files, '
          f'{stat["buch"]} cells cut by the next prime, {stat["halved"]} in two and {stat["drop"]} dropped outright '
          f'(their search: {stat["saved"]} predicted seconds); predicted seconds of the kernel {sum(times):.0f}, a part '
          f'at most {max(times):.0f}, {stat["long"]} above {1.5 * CAP:.0f}')
    if '--stats' in sys.argv:
        print('work:', searched, stat)
        for k, p in enumerate(parts):
            print(f'part {k}: {times[k]:.1f} s; box of {len(p[1])} primes, {len(p[3]) + 1} cells', p[6])
    if '--check' in sys.argv:
        there = sorted(f for f in os.listdir(PNT)
                       if f.startswith(f'SieveTree{TAG}P') or f in (f'SieveFill{TAG}.lean', f'Linnik{TAG}.lean'))
        bad = [n for n, t in files.items()
               if not os.path.exists(os.path.join(PNT, n)) or open(os.path.join(PNT, n), encoding='utf-8').read() != t]
        bad += [n for n in there if n not in files]
        print('SEARCH', TAG, 'FAIL: ' + ', '.join(bad) if bad else 'PASS')
        return 1 if bad else 0
    out = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else PNT
    for n in os.listdir(out):
        if n.startswith(f'SieveTree{TAG}P') and n not in files:
            os.remove(os.path.join(out, n))
    for n, s in files.items():
        with open(os.path.join(out, n), 'w', encoding='utf-8') as fh:
            fh.write(s)
    print(f'wrote {len(files)} files to {out}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
