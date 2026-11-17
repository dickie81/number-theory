#!/usr/bin/env python3
"""Write the site's page on the zeros, `zeros.html`, from the Lean sources.

    python3 scripts/zeros_page.py [OUT]    # write the page (default `_site/zeros.html`)
    python3 scripts/zeros_page.py --check  # read and check everything, and write nothing
    python3 scripts/zeros_page.py --json   # the page's data, on standard output

The page, `site/zeros.html`, shows what the library's theorems say about the zeros of `ζ` and of Dirichlet
L-functions: where in the critical strip a zero can be, how many lie to the right of a line `Re s = σ`, and what that
gives for Linnik's exponent. Each of its numbers that a theorem of the library states is read from that theorem's
statement:
- the half-plane, the band of `ζ`'s zeros, the bounds for `Θ`, the Korobov–Vinogradov region and the range of
  `S(t) = O(log t)`;
- the shares of the zeros that are distinct, simple and on the line, and the constants of the local count
  (`ShortWeil.Kloc`), with `κ = Σ Λ(n)n^{−3/2}` (`Kaiser.kLam`) computed here;
- the density exponents of `ζ`;
- the curve `g*` (`SieveCurve7D.g7d`) and the curve `g_H` of the Type II estimate in two variables
  (`SieveCurveHx.ghx`: the trivial count, then Huxley's steps), each with the theorem that counts each of its pieces,
  read from the proofs of `counts_7d` and `counts_hx` and checked against the piece's range and exponent;
- the Linnik exponents: the density deduction's; Theorem 1.2 of the Linnik paper (`Linnik21500.linnik_21500`), the
  sieve with the Type II estimate in two variables for `g_H` (`SieveTwoZone7D.typeII_two_hx`), whose module must
  import it and which must lie below `1 + A/2` at Chen, Gupta and Li's `A`; and Theorem 1.1
  (`Linnik21000.linnik_21000`), with the resonant window (`SieveTypeIIHM.typeII_res`) and Chen, Gupta and Li's
  Proposition 3.1 (`LinnikCGLHB101.prop31`) as well, whose module must import both and which must lie below
  Theorem 1.2's.
Every theorem the page presents as a result must be printed by one of the check files `lib/check/Check.lean`,
`CheckAll.lean`, `CheckZeta23.lean` and `CheckDH.lean`, whose axioms CI checks. The line `L = 1 + A/2`, where a Type II
estimate in one variable on a window that sorts the characters by their zeros closes, is computed here, not read
from the Lean.
The numbers that are not theorems of the library (the literature's exponents) are read from the paper's sources. A
change to the Lean or to the paper that the page does not follow makes this script fail; CI runs it with `--check`,
and `scripts/build_site.py` runs it to write the page.
"""
import html
import json
import math
import os
import re
import subprocess
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import import_cone  # noqa: E402
import inventory  # noqa: E402

ROOT = import_cone.ROOT
sys.path.insert(0, os.path.join(ROOT, "tools", "linnik"))
import route_limits  # noqa: E402

TEMPLATE = os.path.join(ROOT, "site", "zeros.html")
OUT = os.path.join(ROOT, "_site", "zeros.html")
PAPER = os.path.join(ROOT, "papers", "linnik-exponent")
REPO = "https://github.com/dickie81/number-theory"
TRIVIAL = "SieveCurveGlue.rangeCounts_trivial"
AXIOMS = {"Classical.choice", "Quot.sound"}  # Lean's standard axioms, which the page names


class Fail(Exception):
    pass


def need(ok, msg):
    if not ok:
        raise Fail(msg)


def grab(pattern, text, what):
    m = re.search(pattern, text)
    need(m, f"cannot read {what}")
    return m


# ---- the Lean sources ----------------------------------------------------------------------------------------------

_index = {}


def index():
    """Every declaration of `lib/`, by full name: its file and the index of its line."""
    if not _index:
        mods, _ = import_cone.sources()
        for p in mods.values():
            path = os.path.join(ROOT, p)
            for full, _, _, line in inventory.declarations(path):
                _index.setdefault(full, (path, line))
    return _index


def lines_of(name):
    need(name in index(), f"no module of lib/ declares {name}")
    path, i = index()[name]
    return open(path, encoding="utf-8").read().split("\n"), i


def statement(name):
    """A declaration's statement, from its keyword to the `:=` that ends it, on one line."""
    lines, i = lines_of(name)
    text, depth = "\n".join(lines[i:i + 80]), 0
    for j, ch in enumerate(text):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and text.startswith(":=", j):
            return " ".join(text[:j].split())
    raise Fail(f"no `:=` ends the statement of {name}")


def definition(name):
    """A declaration's whole text, up to its first blank or unindented line, on one line."""
    lines, i = lines_of(name)
    out = [lines[i]]
    for line in lines[i + 1:]:
        if not line.strip() or not line.startswith(" "):
            break
        out.append(line)
    return " ".join(" ".join(out).split())


def printed():
    names = set()
    for f in inventory.CHECKS:
        text = open(os.path.join(ROOT, "lib", "check", f + ".lean"), encoding="utf-8").read()
        names |= set(re.findall(r"^#print axioms (\S+)", text, re.M))
    return names


def q(s):
    """A rational as the Lean writes it: `11 / 12`, `(5 / 7)`, `2`, `278 / 125 : ℝ`, `4 / 10 ^ 6`."""
    s = re.sub(r"\s*:\s*ℝ\s*", "", s.strip())
    while s.startswith("(") and s.endswith(")"):
        s = s[1:-1].strip()
    m = re.fullmatch(r"(\d+)(?: / (\d+)(?: \^ (\d+))?)?", s)
    need(m, f"not a rational: {s!r}")
    return F(int(m.group(1)), int(m.group(2) or 1) ** int(m.group(3) or 1))


def t(x):
    """A rational as the page writes it."""
    return "½" if x == F(1, 2) else f"{x.numerator}" if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def tp(x):
    """A rational as the page writes it as a factor: `(13/4)`, `½`, `2`."""
    return f"({t(x)})" if "/" in t(x) else t(x)


def dec(x, digits):
    """A number in decimals, without trailing zeros."""
    s = f"{float(x):.{digits}f}"
    return s.rstrip("0").rstrip(".") if "." in s else s


def cut(x, digits):
    """A number cut, not rounded, to `digits` decimals, as the paper gives an exact value followed by `…`."""
    return f"{int(x * 10 ** digits) / 10 ** digits:.{digits}f}"


def kappa(X=10 ** 5):
    """`κ = Σ_n Λ(n)n^{−3/2} = −ζ′(3/2)/ζ(3/2)`, the constant `Kaiser.kLam` of the local count: the sum to `X`, and for
    the rest `∫_X^∞ t^{−3/2} dt = 2/√X`, as `ψ(t) ~ t`. At `X = 10⁵` this is `1.5052371…`, against
    `κ = 1.5052353…`."""
    prime = bytearray([1]) * (X + 1)
    prime[0:2] = b"\0\0"
    for i in range(2, math.isqrt(X) + 1):
        if prime[i]:
            prime[i * i::i] = bytes(len(range(i * i, X + 1, i)))
    total = 0.0
    for p in range(2, X + 1):
        if prime[p]:
            pk = p
            while pk <= X:
                total += math.log(p) * pk ** -1.5
                pk *= p
    return total + 2 / math.sqrt(X)


def linnik(name):
    """The exponent of a Linnik theorem: (value, whether `+ η` follows, whether it assumes GRH)."""
    s = statement(name)
    e = grab(r"\(p : ℝ\) ≤ K \* \(q : ℝ\) \^ \((.+)\)$", s, f"the exponent of {name}").group(1)
    e = re.sub(r"\s*:\s*ℝ\s*$", "", e)
    plus = e.endswith(" + η")
    return q(e[:-4] if plus else e), plus, "PsiOmega.GRH χ" in s


# ---- the paper ---------------------------------------------------------------------------------------------------

def tex(name):
    return " ".join(open(os.path.join(PAPER, name), encoding="utf-8").read().split())


def says(pattern, text, what):
    return grab(pattern, text, f"the paper's {what} (it no longer says it in this form)")


def commit():
    try:
        sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True, check=True)
        day = subprocess.run(["git", "log", "-1", "--format=%cs"], cwd=ROOT, capture_output=True, text=True, check=True)
        return sha.stdout.strip(), day.stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return None, None


# ---- the page's data ---------------------------------------------------------------------------------------------

# The share of the zeros that J. B. Conrey proved simple and on the line (J. Reine Angew. Math. 399 (1989): "more than
# two fifths"), drawn for comparison with the library's shares.
CONREY = F(2, 5)

# The density estimates for ζ the page draws, with the method each comes from.
ZETA = [("ZetaGMDensity.densityXi_thirty_thirteenths", "Guth–Maynard"),
        ("ZetaHuxley.densityXi_twelve_fifths", "Huxley"),
        ("InghamDensity.densityXi_17_6", "Ingham's method"),
        ("DetectEM.density_unconditional", "zero detection")]

# The Linnik exponents of the density deduction, with what each adds to the half-plane.
DEDUCTION = [
    ("Linnik.linnik_twelve", "the half-plane alone"),
    ("LinnikDensity.linnik_four",
     "with |<i>L</i>(½ + <i>it</i>, χ)| ≤ 11(<i>q</i>(|<i>t</i>| + 2))<sup>1/2</sup>, by partial summation"),
    ("LinnikSubconvex.linnik_seventeen_sixths",
     "with |<i>L</i>(½ + <i>it</i>, χ)| ≪ (<i>q</i>(|<i>t</i>| + 2))<sup>5/24 + ε</sup>"),
    ("LinnikIngham.linnik_thirtysix_thirteenths", "with Ingham's estimate"),
    ("LinnikHuxley.linnik_eighty_seven_thirty_fifths", "with Ingham's, then large values on [23/29, 11/12]"),
    ("LinnikTwelve.linnik_twelve_fifths", "with Ingham's, then Huxley's on [3/4, 11/12]"),
    ("LinnikG7.linnik_g7d", "with the curve <i>g*</i>"),
]

# The sieve's two Linnik exponents. BEST, Theorem 1.2 of the Linnik paper, rests on the half-plane and Huxley's
# estimate alone, by the Type II estimate in two variables, TWO, for the curve g_H. RESBEST, Theorem 1.1, rests on TWO
# as well, and on the resonant window, RESW: a Type II estimate in one variable that sorts the characters by the sizes
# of the rest's own prime sums as well as by their zeros, which counts by Chen, Gupta and Li's Proposition 3.1, CGLP.
BEST = "Linnik21500.linnik_21500"
RESBEST = "Linnik21000.linnik_21000"
TWO = "SieveTwoZone7D.typeII_two_hx"
RESW = "SieveTypeIIHM.typeII_res"
CGLP = "LinnikCGLHB101.prop31"


def lt(x):
    """A Linnik exponent of the sieve as the page writes it: as a fraction if it is a simple one, else in decimals."""
    return t(x) if x.denominator <= 20 else dec(x, 4)

# The source of each piece of g* and of g_H, by the name of the theorem that counts it.
KINDS = [(r"^SieveCurveGlue\.rangeCounts_trivial$", "trivial"), (r"\.charDensity_in7_\d+$|\.charDensity_inT$", "ingham"),
         (r"\.charDensity_s\d+$", "cgl"), (r"\.charDensity_hx(?:7_\d+|T)$", "huxley"), (r"^LinnikStep\.charDensity_step$", "step")]


def extract():
    results, cited = set(), set()   # theorems the page presents as results, and other declarations it names

    def res(name):
        results.add(name)
        return name

    # Where a zero can be.
    hp = None
    for n in ("Eis.LFunction_ne_zero_of_re_gt", "Eis.ne_zero_of_re_gt_eleven_twelfths"):
        v = q(grab(r"\(hs : (.+?) < s\.re\)", statement(res(n)), f"the half-plane of {n}").group(1))
        need(hp in (None, v), f"{n} has the half-plane Re s > {v}, not {hp}")
        hp = v
    w = q(grab(r"\|2 \* s\.re - 1\| ≤ (.+)$", statement(res("HalfPlaneJoins.zeta_band_eleven_twelfths")),
               "the band of ζ's zeros").group(1))
    band = ((1 - w) / 2, (1 + w) / 2)
    need(band[1] == hp, "the band of ζ's zeros does not end at the half-plane")
    th_hi = q(grab(r"Theta ≤ (.+)$", statement(res("PsiExponent.Theta_le")), "the upper bound for Θ").group(1))
    th_lo = q(grab(r": (.+?) ≤ Theta$", statement(res("PsiExponent.half_le_Theta")), "the lower bound for Θ").group(1))
    kv = grab(r"Real\.log \|t\| \^ \(\((\d+) : ℝ\) / (\d+)\) \* Real\.log \(Real\.log \|t\|\) \^ \(\((\d+) : ℝ\) / (\d+)\)",
              statement(res("LandauKV.zeroFree_KV")), "the exponents of the Korobov–Vinogradov region")
    need(statement(res("BohrLandau.tendsto_NX_div_pos")) == "theorem tendsto_NX_div_pos {w : ℝ} (hw : 0 < w) : "
         "Tendsto (fun T => (NX w T : ℝ) / NX 0 T) atTop (𝓝 0)",
         "BohrLandau.tendsto_NX_div_pos no longer says, for every w > 0 and with no other hypothesis, that almost "
         "every zero is near the line")
    slog = grab(r"^theorem Slog_zeta : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, (\d+) ≤ t → \|Sz zetaOrd t\| ≤ C \* "
                r"Real\.log t$", statement(res("SlogZeta.Slog_zeta")), "the range of S(t) = O(log t)").group(1)
    need(statement(res("ZeroWindow.zero_in_window")) == "theorem zero_in_window : ∃ H T₀ : ℝ, 0 < H ∧ "
         "∀ t : ℝ, T₀ ≤ t → ∃ p : PosZeroIdx, t ≤ zetaOrd p ∧ zetaOrd p < t + H",
         "ZeroWindow.zero_in_window no longer says that the gaps between the ordinates of the zeros are bounded")
    need(statement(res("CriticalLine.infinite_zeros")) == "theorem infinite_zeros : {ρ : ℂ | riemannZeta ρ = 0 ∧ "
         "ρ.re = 1 / 2}.Infinite",
         "CriticalLine.infinite_zeros no longer says that infinitely many zeros of ζ lie on the critical line")
    sel = grab(r"^theorem ncard_zeros_ge : ∀ᶠ T : ℝ in atTop, T \* Real\.log T / \((\d+) \* π\) ≤ \(\(\{ρ : ℂ \| "
               r"riemannZeta ρ = 0 ∧ ρ\.re = 1 / 2\} ∩ \{ρ \| T < ρ\.im ∧ ρ\.im ≤ 2 \* T\}\)\.ncard : ℝ\)$",
               statement(res("CriticalLine.ncard_zeros_ge")), "the zeros on the line with T < Im ρ ≤ 2T").group(1)
    two = q(grab(r"^theorem two_thirds : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, \((.+?) - ε\) \* \(Ncount T \(2 \* T\) : ℝ\) "
                 r"≤ N0star T \(2 \* T\)$", statement(res("CriticalLine.two_thirds")),
                 "the share of the zeros on the critical line").group(1))

    # How many zeros, and how simple.
    need(statement(res("ZeroCount.riemann_von_mangoldt")) == "theorem riemann_von_mangoldt : ∃ C T₀ : ℝ, ∀ T ≥ T₀, "
         "|(Ncount T (2 * T) : ℝ) - T / (2 * π) * (Real.log (T / (2 * π)) + 2 * Real.log 2 - 1)| ≤ C * Real.log T",
         "ZeroCount.riemann_von_mangoldt no longer states the Riemann–von Mangoldt formula as the page gives it")
    need(statement(res("CountCompare.local_count_le")) == "theorem local_count_le {t : ℝ} (ht : 0 ≤ t) : "
         "(Zeta23.Ncount t (t + 1) : ℝ) ≤ Kloc (t + 1 / 2)",
         "CountCompare.local_count_le no longer bounds the zeros with t < Im ρ ≤ t + 1 by Kloc (t + 1/2)")
    need(statement(res("ZeroOrder.analyticOrderAt_le")) == "theorem analyticOrderAt_le {ρ : ℂ} (hρ : riemannZeta ρ = 0) "
         "(h0 : 0 < ρ.re) (h1 : ρ.re < 1) : analyticOrderAt riemannZeta ρ ≤ ⌊Kloc (|ρ.im| + 1 / 2)⌋₊",
         "ZeroOrder.analyticOrderAt_le no longer bounds the order of every nontrivial zero by Kloc (|Im ρ| + 1/2)")
    need(statement(res("ZeroOrder.im_ne_zero")) == "theorem im_ne_zero {ρ : ℂ} (hρ : Zeta23.IsNontrivialZero ρ) : "
         "ρ.im ≠ 0", "ZeroOrder.im_ne_zero no longer says that no nontrivial zero is real")
    kl = [int(g) for g in grab(r"^def Kloc \(x : ℝ\) : ℝ := (\d+) / (\d+) \* \((\d+) \+ kLam \+ Real\.log \(x \+ (\d+)\) / "
                               r"(\d+)\)$", definition("ShortWeil.Kloc"), "the constants of the local count").groups()]
    need(definition("Kaiser.kLam") == "def kLam : ℝ := ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n "
         ": ℂ)) (3 / 2 : ℂ) n‖", "Kaiser.kLam is no longer Σ Λ(n)n^{−3/2}")
    # Kloc (x + ½) = a(c + κ) + (a/e)log(x + ½ + d), with a = kl[0]/kl[1], c, d, e = kl[2:]
    kap = kappa()
    kloc = {"a": F(kl[0], kl[1]), "c": kl[2], "slope": F(kl[0], kl[1] * kl[4]), "shift": F(1, 2) + kl[3],
            "const": kl[0] / kl[1] * (kl[2] + kap), "kappa": kap}
    simple = grab(r"^theorem ncard_simple_zeros_ge : ∀ᶠ T : ℝ in atTop, T \* Real\.log T / \((\d+) \* π\) ≤ \(\(\{ρ : ℂ "
                  r"\| riemannZeta ρ = 0 ∧ ρ\.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1\} ∩ \{ρ \| T < ρ\.im ∧ "
                  r"ρ\.im ≤ 2 \* T\}\)\.ncard : ℝ\)$", statement(res("CriticalLine.ncard_simple_zeros_ge")),
                  "the simple zeros on the line with T < Im ρ ≤ 2T").group(1)
    need(statement(res("CriticalLine.infinite_simple_zeros")) == "theorem infinite_simple_zeros : {ρ : ℂ | "
         "riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ analyticOrderAt riemannZeta ρ = 1}.Infinite",
         "CriticalLine.infinite_simple_zeros no longer says that infinitely many simple zeros lie on the critical line")

    def share(name, count):
        return q(grab(r"^theorem " + name.split(".")[-1] + r" : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, \((.+?) - ε\) \* "
                      r"\(Ncount T \(2 \* T\) : ℝ\) ≤ " + count + r" T \(2 \* T\)$", statement(res(name)),
                      f"the share of the zeros in {name}").group(1))
    half, dist = share("CriticalLine.half_simple", "N0simple"), share("CriticalLine.three_quarters_distinct", "Ndist")

    # How many zeros of ζ lie right of σ.
    zeta = []
    for n, how in ZETA:
        s = statement(res(n))
        m = grab(r"DensityXi \((.+)\) (\d+)$", s, f"the exponent of {n}")
        e, dmax = m.group(1), None
        if e.endswith(" + ε"):
            A, shape = q(e[:-4]), "eps"
        else:
            A, shape = F(int(grab(r"^(\d+) \* \(1 \+ δ\)$", e, f"the exponent of {n}").group(1))), "delta"
            dmax = q(grab(r"\(hδ1 : δ ≤ (.+?)\)", s, f"the range of δ in {n}").group(1))
        zeta.append({"A": float(A), "f": t(A), "shape": shape, "B": int(m.group(2)),
                     "dmax": t(dmax) if dmax else None, "lean": n, "how": how})
    c524 = q(grab(r"ZetaCritBound \((.+?) \+ ε\)$", statement(res("Subconvexity.zetaCritBound_five_24")),
                  "the subconvexity exponent").group(1))
    need("Subconvexity.zetaCritBound_five_24" in definition("InghamDensity.densityXi_17_6"),
         "InghamDensity.densityXi_17_6 no longer uses Subconvexity.zetaCritBound_five_24")

    # The Linnik paper's curve, and the theorem that counts each piece.
    pieces = route_limits.parse("g7d")
    cited.add("SieveCurve7D.g7d")
    proof = definition(res("SieveCurve7D.counts_7d"))
    chain = [x or TRIVIAL for x in re.findall(r"rangeCounts_(?:trivial|of_density ([\w.']+))", proof)]
    need(len(chain) == len(pieces), f"counts_7d glues {len(chain)} counts, but g7d has {len(pieces)} pieces")
    gstar = []
    for i, ((lo, hi, A), n) in enumerate(zip(pieces, chain)):
        kind = next((k for pattern, k in KINDS if re.search(pattern, n)), None)
        need(kind, f"counts_7d glues in {n}, whose source the page does not know")
        cited.add(n)
        if A is None:
            need(n == TRIVIAL, f"piece {i} of g7d is the trivial count, but counts_7d glues {n} there")
        else:
            s = statement(n)
            r = grab(r"\(σ T : ℝ\), (.+?) ≤ σ → σ ≤ (.+?) → 2 ≤ T", s, f"the range of {n}")
            e = grab(r"\(\(q : ℝ\) \* T\) \^ \((.+?) \* \(1 - σ\)\)", s, f"the exponent of {n}")
            slo, shi, sA = q(r.group(1)), q(r.group(2)), q(e.group(1))
            last = i == len(pieces) - 1
            need(slo == lo and sA == A and (shi == hi or last and shi >= hi),
                 f"{n} counts on [{slo}, {shi}] with the exponent {sA}, but piece {i} of g7d is [{lo}, {hi}) with {A}")
        gstar.append({"lo": float(lo), "hi": float(hi), "loF": t(lo), "hiF": t(hi),
                      "A": None if A is None else float(A), "AF": None if A is None else t(A), "lean": n, "src": kind})
    peak = max((i for i, p in enumerate(pieces) if p[2] is not None), key=lambda i: pieces[i][2])
    gmax = pieces[peak][2]

    # The curve of the Type II estimate in two variables: the trivial count, then Huxley's steps only.
    hpieces = route_limits.parse("ghx")
    cited.add("SieveCurveHx.ghx")
    hchain = [(x if "." in x else "SieveCurveHx." + x) if x else TRIVIAL
              for x in re.findall(r"rangeCounts_(?:trivial|of_density ([\w.']+))",
                                  definition(res("SieveCurveHx.counts_hx")))]
    need(len(hchain) == len(hpieces), f"counts_hx glues {len(hchain)} counts, but ghx has {len(hpieces)} pieces")
    for i, ((lo, hi, A), n) in enumerate(zip(hpieces, hchain)):
        kind = next((k for pattern, k in KINDS if re.search(pattern, n)), None)
        need(kind in ("trivial", "huxley", "step"), f"counts_hx glues in {n}, which is not the trivial count or Huxley's")
        if A is None:
            need(i == 0 and n == TRIVIAL, f"piece {i} of ghx is the trivial count, but counts_hx glues {n} there")
        else:
            cited.add(n)
            s = statement(n)
            r = grab(r"\(σ T : ℝ\), (.+?) ≤ σ → σ ≤ (.+?) → 2 ≤ T", s, f"the range of {n}")
            e = grab(r"\(\(q : ℝ\) \* T\) \^ \((.+?) \* \(1 - σ\)\)", s, f"the exponent of {n}")
            slo, shi, sA = q(r.group(1)), q(r.group(2)), q(e.group(1))
            last = i == len(hpieces) - 1
            need(slo == lo and sA == A and (shi == hi or last and shi >= hi),
                 f"{n} counts on [{slo}, {shi}] with the exponent {sA}, but piece {i} of ghx is [{lo}, {hi}) with {A}")
    hthr, hA = hpieces[1][0], hpieces[1][2]
    need(all(p in pieces for p in hpieces[2:]), "ghx is not g* from its second Huxley step on")

    # Linnik's exponent: the deduction, the sieve and GRH.
    ded = statement(res("Linnik.linnik_of_charDensity"))
    need("(hD : CharDensity A B C)" in ded and "(q : ℝ) ^ (A + η)" in ded,
         "Linnik.linnik_of_charDensity no longer turns a density exponent A into every L > A")
    deduction = []
    for n, label in DEDUCTION:
        L, plus, grh = linnik(res(n))
        need(plus and not grh, f"{n} is not an exponent L + η without hypothesis")
        deduction.append((L, n, label))
    deduction.sort(key=lambda r: -r[0])
    gx = [L for L, n, _ in deduction if n == "LinnikG7.linnik_g7d"][0]
    need(gx == gmax, f"LinnikG7.linnik_g7d gives {gx}, not g*'s largest exponent {gmax}")
    need("counts_hx" in definition(res(TWO)), f"{TWO} is no longer the estimate for g_H, whose counts are counts_hx")
    _, imports = import_cone.sources()

    def module(n):
        need(n in index(), f"no module of lib/ declares {n}")
        return os.path.splitext(os.path.basename(index()[n][0]))[0]

    best, resbest = BEST, RESBEST
    Lbest, plus, grh = linnik(res(best))
    need(not plus and not grh, f"{best} is not an exponent without hypothesis")
    need(module(TWO) in import_cone.cone(imports, [module(best)]),
         f"{best}'s module does not import {module(TWO)}, the Type II estimate in two variables")
    # the modules of the resonant window and of Proposition 3.1, which Theorem 1.1's module must import
    cited.add(CGLP)
    Lres, plus, grh = linnik(res(resbest))
    need(not plus and not grh, f"{resbest} is not an exponent without hypothesis")
    cone = import_cone.cone(imports, [module(resbest)])
    for d in (TWO, res(RESW), CGLP):
        need(module(d) in cone, f"{resbest}'s module does not import {module(d)}, the module of {d}")
    need(Lres < Lbest, f"{resbest} is not below {best}")
    Lgrh, plus, grh = linnik(res("LinnikGRH.linnik_two_of_GRH"))
    need(plus and grh, "LinnikGRH.linnik_two_of_GRH no longer assumes GRH")
    Agrh = q(grab(r"Linnik\.CharDensity (\S+) \S+ \S+$", statement(res("LinnikGRH.charDensity_two_of_GRH")),
                  "the density exponent under GRH").group(1))
    need(Agrh == Lgrh, "GRH's density exponent is not its Linnik exponent")

    # The paper: the literature's numbers, which the page cites.
    main, bib = tex("main.tex"), tex("references.tex")
    hb = float(says(r"Heath-Brown \\cite\{heath-brown92\} reached \$L = ([\d.]+)\$", main, "Heath-Brown").group(1))
    xy = float(says(r"and then \$L = ([\d.]+)\$ \\cite\{xylouris11\}", main, "Xylouris").group(1))
    hb_src = says(r"\\bibitem\{heath-brown92\} .*?\\emph\{[^}]*\}, (.+?) \((\d{4})\),", bib, "reference for Heath-Brown")
    xy_src = says(r"\\bibitem\{xylouris11\} .*?\\emph\{[^}]*\}, (.+?), Bonn, (\d{4})\.", bib, "reference for Xylouris")
    m = says(r"prove \$A = (\d+)/(\d+)\$, uniformly in \$q\$ and \$T\$", main, "exponent of Chen, Gupta and Li")
    cgl = F(int(m.group(1)), int(m.group(2)))
    says(r"Chen--Gupta--Li's density estimate \\cite\[Theorem~1\.2\]\{cgl\} &\s+density deduction \(not formalised\) &",
         main, "row for 7/3")
    # The floor of a Type II estimate in one variable on a window that sorts the characters by their zeros,
    # L = 1 + A/2 at Chen, Gupta and Li's A: computed here, not read from the Lean.
    floor = 1 + cgl / 2
    need(Lbest < floor, f"{best} is not below 1 + A/2 = {t(floor)}, as the page says")

    ladder = [{"group": "Refereed results, without the half-plane"},
              {"label": "Heath-Brown (" + hb_src.group(2) + ")", "L": hb, "text": dec(hb, 2), "kind": "ref",
               "src": hb_src.group(1) + " (" + hb_src.group(2) + ")"},
              {"label": "Xylouris (" + xy_src.group(2) + ")", "L": xy, "text": dec(xy, 2), "kind": "ref",
               "src": xy_src.group(1) + " (" + xy_src.group(2) + ")"},
              {"group": "The density deduction: a density exponent A gives every L > A"}]
    rows = [{"label": label, "L": float(x), "text": (t(x) if x.denominator < 1000 else dec(x, 4)) + " + η",
             "dec": dec(x, 3) if x.denominator not in (1, 5000) else None, "kind": "lean", "src": n}
            for x, n, label in deduction]
    rows.append({"label": "with Chen, Gupta and Li's Theorem 1.2", "L": float(cgl), "text": t(cgl) + " + ε",
                 "dec": dec(cgl, 3), "kind": "other", "src": "not formalised as they state it"})
    ladder += sorted(rows, key=lambda r: -r["L"])
    sieve = [("Harman's sieve: below the density exponent, with a Type II estimate in two variables", Lbest, best,
              "from the half-plane and Huxley's estimate alone, with a term of three or five primes reversed through "
              "its largest prime: Theorem 1.2 of the Linnik paper"),
             ("With a Type II estimate in one variable over the sizes of a term's own prime sums as well, and Chen, "
              "Gupta and Li's Proposition 3.1", Lres, resbest,
              "with the resonant window, the leaves of a comparison cut in three and the terms of the sign + "
              "reversed as well, and the window's test at the two corners of a box: Theorem 1.1 of the Linnik paper")]
    for group, x, n, label in sieve:
        ladder += [{"group": group},
                   {"label": label, "L": float(x), "text": lt(x), "dec": dec(x, 3) if "/" in lt(x) else None,
                    "kind": "lean", "src": n, "main": True}]

    la = [{"A": float(Agrh), "L": float(Lgrh), "kind": "limit", "role": "dh", "text": t(Lgrh) + " + η",
           "label": f"the density hypothesis, A = {t(Agrh)}, which GRH implies",
           "src": "LinnikGRH.linnik_two_of_GRH, under GRH"}]
    for x, n, label in deduction:
        if x <= F(252, 100):
            la.append({"A": float(x), "L": float(x), "kind": "lean", "role": "ded",
                       "text": (t(x) if x.denominator < 1000 else dec(x, 4)) + " + η",
                       "label": "the deduction, " + re.sub(r"<[^>]+>", "", label), "src": n})
    Ahux = [x for x, n, _ in deduction if n == "LinnikTwelve.linnik_twelve_fifths"][0]
    la.append({"A": float(Ahux), "L": float(Lbest), "kind": "lean", "role": "main", "text": lt(Lbest),
               "label": "Theorem 1.2 of the Linnik paper: the sieve with the half-plane and Huxley's estimate, by the "
                        "Type II estimate in two variables, below 1 + A/2", "src": best})
    la.append({"A": float(gmax), "L": float(Lres), "kind": "lean", "role": "res", "text": lt(Lres),
               "label": "Theorem 1.1 of the Linnik paper: the sieve with the resonant window too, from the half-plane, "
                        "Chen, Gupta and Li's Proposition 3.1, and Ingham's and Huxley's estimates", "src": resbest})

    sha, day = commit()
    named, shown = results | cited, printed()
    missing = sorted(n for n in results if n not in shown)
    need(not missing, "the page presents as results theorems that no check file prints: " + ", ".join(missing))
    data = {
        "hp": {"x": float(hp), "t": t(hp)}, "band": [{"x": float(x), "t": t(x)} for x in band],
        "theta": [{"x": float(x), "t": t(x)} for x in (th_lo, th_hi)],
        "zeta": zeta, "g7d": gstar, "peak": peak,
        "gmax": {"x": float(gmax), "t": dec(gmax, 4), "lean": "LinnikG7.linnik_g7d"},
        "cgl": {"x": float(cgl), "t": t(cgl)}, "floor": {"x": float(floor), "t": t(floor)},
        "grh": {"x": float(Lgrh), "t": t(Lgrh)},
        "best": {"x": float(Lbest), "t": lt(Lbest), "lean": best, "two": TWO},
        "res": {"x": float(Lres), "t": lt(Lres), "lean": resbest, "win": RESW},
        "ladder": ladder, "la": la,
        "shares": [{"x": float(x), "t": t(x), "what": what, "lean": n} for x, what, n in (
            (half, "simple and on the line", "CriticalLine.half_simple"),
            (two, "distinct and on the line", "CriticalLine.two_thirds"),
            (dist, "distinct", "CriticalLine.three_quarters_distinct"))],
        "conrey": {"x": float(CONREY), "t": t(CONREY)},
    }
    texts = {
        "hp": t(hp), "hpWidth": t(1 - hp), "bandLo": t(band[0]), "bandHi": t(band[1]),
        "thetaLo": t(th_lo), "thetaHi": t(th_hi), "selberg": sel, "onLine": t(two),
        "klocA": tp(kloc["a"]), "klocC": str(kloc["c"]), "klocSlope": tp(kloc["slope"]), "klocShift": t(kloc["shift"]),
        "klocConst": cut(kloc["const"], 2), "kappa": cut(kloc["kappa"], 4), "simpleSel": simple,
        "halfSimple": t(half), "distinct": t(dist), "multiple": t(1 - dist), "conrey": t(CONREY),
        "kvA": f"{kv.group(1)}/{kv.group(2)}", "kvB": f"{kv.group(3)}/{kv.group(4)}",
        "nzeta": {1: "one", 2: "two", 3: "three", 4: "four", 5: "five"}.get(len(zeta), str(len(zeta))),
        "npieces": str(len(pieces)), "nhx": str(len(hpieces)), "hxLo": t(hthr), "hxA": dec(hA, 5), "hux": t(Ahux),
        "gmax": dec(gmax, 4), "gmaxLo": t(pieces[peak][0]), "gmaxHi": t(pieces[peak][1]),
        "cgl": t(cgl), "floor": t(floor), "grh": t(Lgrh),
        "Lbest": lt(Lbest), "Lbestdec": dec(Lbest, 4), "bestLean": best,
        "Lres": lt(Lres), "resLean": resbest, "resWin": RESW,
        "nresults": str(len(shown)),
        "commit": f'<a href="{REPO}/tree/{sha}">{sha[:7]}</a>' if sha else "the working tree",
        "date": html.escape(day or ""),
        "theorems": theorem_rows(hp, band, th_lo, th_hi, slog, sel, two, zeta, c524, Lbest, best, kloc, simple,
                                 half, dist, Lres, resbest),
    }
    for k in ("hp", "hpWidth", "bandLo", "bandHi", "thetaLo", "thetaHi", "selberg", "onLine", "kvA", "kvB", "nzeta",
              "klocA", "klocC", "klocSlope", "klocShift", "klocConst", "kappa", "simpleSel", "halfSimple", "distinct",
              "multiple", "conrey",
              "npieces", "nhx", "hxLo", "hxA", "hux", "gmax",
              "gmaxLo", "gmaxHi", "cgl", "floor", "grh", "nresults",
              "Lbest", "Lbestdec", "bestLean", "Lres", "resLean", "resWin"):
        texts[k] = html.escape(texts[k])
    return data, texts, named, results


def theorem_rows(hp, band, th_lo, th_hi, slog, sel, two, zeta, c524, Lbest, best, kloc, simple, half, dist,
                 Lres, resbest):
    """The rows of the page's table of theorems, as HTML."""
    m = lambda s: f'<span class="math">{s}</span>'  # noqa: E731
    rows = [
        (f"{m('ζ(s)')} ≠ 0 for {m('Re s')} &gt; {t(hp)}", ["Eis.ne_zero_of_re_gt_eleven_twelfths"]),
        (f"Every nontrivial zero {m('ρ')} of {m('ζ')} has {t(band[0])} ≤ {m('Re ρ')} ≤ {t(band[1])}",
         ["HalfPlaneJoins.zeta_band_eleven_twelfths"]),
        (f"{m('L(s, χ)')} ≠ 0 for {m('Re s')} &gt; {t(hp)}, for every Dirichlet character {m('χ')} (the pole at "
         f"{m('s')} = 1 aside)", ["Eis.LFunction_ne_zero_of_re_gt"]),
        (f"{t(th_lo)} ≤ {m('Θ')} ≤ {t(th_hi)}", ["PsiExponent.half_le_Theta", "PsiExponent.Theta_le"]),
        ("The Korobov–Vinogradov zero-free region", ["LandauKV.zeroFree_KV"]),
        (f"For every {m('w')} &gt; 0, almost every zero lies within {m('w')} of {m('Re s')} = ½",
         ["BohrLandau.tendsto_NX_div_pos"]),
        (f"{m('S(t) = O(log t)')} for {m('t')} ≥ {slog}", ["SlogZeta.Slog_zeta"]),
        (f"There is an {m('H')} such that, for large {m('t')}, every window {m('[t, t + H)')} contains the ordinate of "
         f"a zero of {m('ζ')}", ["ZeroWindow.zero_in_window"]),
        (f"Infinitely many zeros of {m('ζ')} lie on the critical line {m('Re s')} = ½",
         ["CriticalLine.infinite_zeros"]),
        (f"For large {m('T')}, at least {m('T log T')}/{sel}{m('π')} zeros on the critical line have "
         f"{m('T &lt; Im ρ ≤ 2T')}", ["CriticalLine.ncard_zeros_ge"]),
        (f"For every {m('ε')} &gt; 0 and large {m('T')}, at least ({t(two)} − {m('ε')}){m('N(T, 2T)')} distinct zeros "
         f"with {m('T &lt; Im ρ ≤ 2T')} lie on the critical line, {m('N(T, 2T)')} counting all of them with "
         f"multiplicity", ["CriticalLine.two_thirds"]),
        (f"{m('N(T, 2T)')} = ({m('T')}/2{m('π')})(log({m('T')}/2{m('π')}) + 2 log 2 − 1) + {m('O(log T)')}, the "
         f"Riemann–von Mangoldt formula", ["ZeroCount.riemann_von_mangoldt"]),
        (f"For every {m('t')} ≥ 0, at most {tp(kloc['a'])}({kloc['c']} + {m('κ')}) + {tp(kloc['slope'])} "
         f"log({m('t')} + {t(kloc['shift'])}) zeros, counted with multiplicity, have {m('t &lt; Im ρ ≤ t + 1')}, where "
         f"{m('κ')} = Σ {m('Λ(n)n')}<sup class=\"math\">−3/2</sup>", ["CountCompare.local_count_le"]),
        (f"Every nontrivial zero {m('ρ')} of {m('ζ')} has order at most {tp(kloc['a'])}({kloc['c']} + {m('κ')}) + "
         f"{tp(kloc['slope'])} log(|{m('Im ρ')}| + {t(kloc['shift'])}), and {m('Im ρ')} ≠ 0",
         ["ZeroOrder.analyticOrderAt_le", "ZeroOrder.im_ne_zero"]),
        (f"For every {m('ε')} &gt; 0 and large {m('T')}, at least ({t(half)} − {m('ε')}){m('N(T, 2T)')} simple zeros "
         f"with {m('T &lt; Im ρ ≤ 2T')} lie on the critical line", ["CriticalLine.half_simple"]),
        (f"For large {m('T')}, at least {m('T log T')}/{simple}{m('π')} simple zeros on the critical line have "
         f"{m('T &lt; Im ρ ≤ 2T')}, and infinitely many are simple in all",
         ["CriticalLine.ncard_simple_zeros_ge", "CriticalLine.infinite_simple_zeros"]),
        (f"For every {m('ε')} &gt; 0 and large {m('T')}, at least ({t(dist)} − {m('ε')}){m('N(T, 2T)')} distinct zeros "
         f"have {m('T &lt; Im ρ ≤ 2T')}", ["CriticalLine.three_quarters_distinct"]),
    ]
    for z in zeta:
        a = f"({z['f']} + ε)" if z["shape"] == "eps" else f"{z['f']}(1+δ)"
        tail = f", for 0 &lt; {m('δ')} ≤ {z['dmax']}" if z["dmax"] else ""
        if z["lean"] == "InghamDensity.densityXi_17_6":
            tail += f", by Ingham's method from {m('ζ(½ + it) ≪ t')}<sup class=\"math\">{t(c524)} + ε</sup>"
        rows.append((f"{m('N(σ, T) ≪ T')}<sup class=\"math\">{a}(1−σ)</sup>{m('(log T)')}<sup>{z['B']}</sup>{tail}",
                     [z["lean"]]))
    rows.append((f"At most {m('C(qT)')}<sup class=\"math\">g*(σ)</sup>{m('(1 + log qT)')}<sup>10</sup> characters mod "
                 f"{m('q')} have a zero with {m('β ≥ σ')}, {m('|γ| ≤ T')}", ["SieveCurve7D.counts_7d"]))
    rows.append((f"At most {m('C(qT)')}<sup class=\"math\">g<sub>H</sub>(σ)</sup>{m('(1 + log qT)')}<sup>10</sup> "
                 f"characters mod {m('q')} have a zero with {m('β ≥ σ')}, {m('|γ| ≤ T')}: the trivial count, then "
                 f"Huxley's steps", ["SieveCurveHx.counts_hx"]))
    rows.append((f"Every reduced residue class mod {m('q')} contains a prime {m('p ≤ Kq')}"
                 f"<sup class=\"math\">{lt(Lbest)}</sup>, by a Type II estimate in two variables for "
                 f"{m('g<sub>H</sub>')}, from the half-plane and Huxley's estimate: Theorem 1.2 of the Linnik paper",
                 [best, TWO]))
    rows.append((f"Every reduced residue class mod {m('q')} contains a prime {m('p ≤ Kq')}"
                 f"<sup class=\"math\">{lt(Lres)}</sup>, with the resonant window, the leaves of a comparison cut in "
                 f"three and the terms of the sign + reversed as well, from the half-plane, Chen, Gupta and Li's "
                 f"Proposition 3.1, and Ingham's and Huxley's estimates: Theorem 1.1 of the Linnik paper (the kernel's check of "
                 f"its certificate was not finished on 16 November 2026)", [resbest, RESW]))
    return "\n".join(f"          <tr><td>{a}</td>\n            <td>{', '.join(f'<code>{n}</code>' for n in ns)}</td></tr>"
                     for a, ns in rows)


# ---- the page ----------------------------------------------------------------------------------------------------

def render(data, texts, named):
    page = open(TEMPLATE, encoding="utf-8").read()
    keys = set(re.findall(r"\{\{(\w+)\}\}", page))
    need(keys == set(texts) | {"data"}, f"site/zeros.html's placeholders do not match this script's: missing "
         f"{sorted(keys - set(texts) - {'data'})}, unused {sorted(set(texts) - keys)}")
    page = page.replace("{{data}}", json.dumps(data, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/"))
    for k, v in texts.items():
        page = page.replace("{{" + k + "}}", v)
    # every Lean name the page shows is one this script read
    shown = set(re.findall(r"<code>([A-Z][\w']*(?:\.(?:<wbr>)?[\w'₀-₉]+)+)</code>", page))
    shown = {s.replace("<wbr>", "") for s in shown if not re.search(r"\.(?:lean|py|md)$", s)} - AXIOMS
    unknown = sorted(s for s in shown if s not in named)
    need(not unknown, "site/zeros.html names declarations that this script does not read: " + ", ".join(unknown))
    return page


def main(argv):
    try:
        data, texts, named, results = extract()
        page = render(data, texts, named)
    except Fail as e:
        print(f"zeros_page: {e}", file=sys.stderr)
        return 1
    if "--json" in argv:
        print(json.dumps(data, ensure_ascii=False, indent=1))
        return 0
    if "--check" in argv:
        print(f"zeros_page: the page agrees with the Lean and the paper: {len(results)} theorems named as results, all "
              f"printed by Check, CheckAll, CheckZeta23 or CheckDH; g*'s {len(data['g7d'])} pieces each counted by the "
              f"theorem counts_7d glues in, and g_H's {texts['nhx']} by the one counts_hx glues in; Linnik's exponents "
              f"{data['best']['t']} ({data['best']['lean']}) and {data['res']['t']} ({data['res']['lean']}), below "
              f"1 + A/2 = {data['floor']['t']}")
        return 0
    out = argv[0] if argv else OUT
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, "w", encoding="utf-8") as fh:
        fh.write(page)
    inside = os.path.abspath(out).startswith(ROOT + os.sep)
    print(f"zeros_page: wrote {os.path.relpath(out, ROOT) if inside else out}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
