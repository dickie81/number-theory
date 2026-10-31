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
- the density exponents of `ζ`;
- the curve `g*` of the Linnik paper (`SieveCurve7D.g7d`), with the theorem that counts each of its pieces, read
  from the proof of `counts_7d` and checked against the piece's range and exponent;
- the Linnik exponents;
- the sieve's window condition (`SieveCurveGlue.WindowOKHM`), with its constants, and the window and the exponent of
  `window_22000d`;
- the bound of the certificate (`SieveDeep.totalD_lt_22000E`).
Every theorem the page presents as a result must be printed by one of the check files `lib/check/Check.lean`,
`CheckAll.lean`, `CheckZeta23.lean` and `CheckDH.lean`, whose axioms CI checks. The window's exact ends, computed
here from the Lean's curve and condition, must contain the Lean's window.
The numbers that are not theorems of the library (the literature's exponents and the paper's computations) are read
from the paper's sources, and the numbers of the paper's sections and statements from its `.aux` files when it is
compiled. A change to the Lean or to the paper that the page does not follow makes this script fail; CI runs it with
`--check`, and `scripts/build_site.py` runs it to write the page.
"""
import html
import json
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


def dec(x, digits):
    """A number in decimals, without trailing zeros."""
    s = f"{float(x):.{digits}f}"
    return s.rstrip("0").rstrip(".") if "." in s else s


def cut(x, digits):
    """A number cut, not rounded, to `digits` decimals, as the paper gives an exact value followed by `…`."""
    return f"{int(x * 10 ** digits) / 10 ** digits:.{digits}f}"


def linnik(name):
    """The exponent of a Linnik theorem: (value, whether `+ η` follows, whether it assumes GRH)."""
    s = statement(name)
    e = grab(r"\(p : ℝ\) ≤ K \* \(q : ℝ\) \^ \((.+)\)$", s, f"the exponent of {name}").group(1)
    e = re.sub(r"\s*:\s*ℝ\s*$", "", e)
    plus = e.endswith(" + η")
    return q(e[:-4] if plus else e), plus, "PsiOmega.GRH χ" in s


# The forms of the window condition that site/zeros.html computes (`winEnds`), with the constants left open. If the
# Lean's condition changes, the page's computation must change with it.
WINDOW_FORMS = {
    "SieveCurveGlue.WindowOKHM":
        "def WindowOKHM (g : ℝ → ℝ) (L m₁ m₂ d e : ℝ) : Prop := ∀ β m w : ℝ, 1 / 2 ≤ β → β ≤ {TOP} → m₁ ≤ m → "
        "m ≤ m₂ → 0 ≤ w → w ≤ {W} → ((m ≤ 1 → (L - m) * (β + w) + g β / 2 + (1 + m) / 2 ≤ L - {M}) ∧ "
        "(1 ≤ m → (L - m) * (β + w) + g β / 2 + m ≤ L - {M})) ∨ (m ≤ 1 ∧ hmBound L d e (g β) β m w)",
    "SieveCurveGlue.hmBound":
        "def hmBound (L d e gβ β m w : ℝ) : Prop := (L - m) * (β + w) + gβ / 2 + m / 2 + m / 2 ≤ L - {M} ∧ "
        "(L - m) * (β + w) + gβ / 2 + m / 2 + (gβ + ({K0} + m / {K1} + d * (1 - m) + 2 * e)) / 2 ≤ L - {M}",
}


def form(name):
    """The constants of a definition of WINDOW_FORMS, which must have that form."""
    text, seen, pattern = definition(name), set(), ""
    for part in re.split(r"(\{\w+\})", WINDOW_FORMS[name]):
        m = re.fullmatch(r"\{(\w+)\}", part)
        if not m:
            pattern += re.escape(part)
        elif m.group(1) in seen:
            pattern += f"(?P={m.group(1)})"
        else:
            seen.add(m.group(1))
            pattern += rf"(?P<{m.group(1)}>\d+(?: / \d+(?: \^ \d+)?)?)"
    m = re.fullmatch(pattern, text)
    need(m, f"{name} is no longer of the form the page computes; update winEnds in site/zeros.html and WINDOW_FORMS "
            f"in this script. It reads: {text}")
    return {k: q(v) for k, v in m.groupdict().items()}


# ---- the paper ---------------------------------------------------------------------------------------------------

def tex(name):
    return " ".join(open(os.path.join(PAPER, name), encoding="utf-8").read().split())


def says(pattern, text, what):
    return grab(pattern, text, f"the paper's {what} (it no longer says it in this form)")


def refs():
    """The numbers of the paper's statements and sections that the page cites: from the compiled paper's `.aux`
    files, or, when it is not compiled, their numbers when this script was written."""
    cites = {"defWindow": ("main", "def:window", "Definition {}", "3.3"),
             "secComparison": ("main", "sec:comparison", "§{}", "8"),
             "supComputations": ("supplement", "sup:computations", "§{}", "S6")}
    out = {}
    for key, (doc, label, shape, last) in cites.items():
        need(f"\\label{{{label}}}" in open(os.path.join(PAPER, doc + ".tex"), encoding="utf-8").read(),
             f"the paper has no label {label}")
        aux = os.path.join(PAPER, doc + ".aux")
        m = re.search(r"\\newlabel\{" + re.escape(label) + r"\}\{\{([^}]*)\}", open(aux, encoding="utf-8").read()) \
            if os.path.exists(aux) else None
        out[key] = shape.format(m.group(1) if m else last)
    return out


def commit():
    try:
        sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True, check=True)
        day = subprocess.run(["git", "log", "-1", "--format=%cs"], cwd=ROOT, capture_output=True, text=True, check=True)
        return sha.stdout.strip(), day.stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return None, None


# ---- the page's data ---------------------------------------------------------------------------------------------

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

# The source of each piece of g*, by the name of the theorem that counts it.
KINDS = [(r"^SieveCurveGlue\.rangeCounts_trivial$", "trivial"), (r"\.charDensity_in7_\d+$|\.charDensity_inT$", "ingham"),
         (r"\.charDensity_s\d+$", "cgl"), (r"\.charDensity_hx7_\d+$", "huxley"), (r"^LinnikStep\.charDensity_step$", "step")]


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
    Lmain, plus, grh = linnik(res("Linnik22000E.linnik_22000e"))
    need(not plus and not grh, "Linnik22000E.linnik_22000e is not an exponent without hypothesis")
    Lgrh, plus, grh = linnik(res("LinnikGRH.linnik_two_of_GRH"))
    need(plus and grh, "LinnikGRH.linnik_two_of_GRH no longer assumes GRH")
    Agrh = q(grab(r"Linnik\.CharDensity (\S+) \S+ \S+$", statement(res("LinnikGRH.charDensity_two_of_GRH")),
                  "the density exponent under GRH").group(1))
    need(Agrh == Lgrh, "GRH's density exponent is not its Linnik exponent")

    # The window: the condition, its constants, the window of the Lean and the exponent.
    s = statement(res("SieveTypeIIU22000D.window_22000d"))
    m = grab(r"WindowOKHM g7d \((.+?)\) \((.+?) \* \((.+?)\)\) \((.+?) \* \((.+?)\)\) \((.+?)\) \((.+?)\)$", s,
             "the window of window_22000d")
    L, u1, La, u2, Lb, kd, ke = (q(x) for x in m.groups())
    need(L == La == Lb == Lmain, "window_22000d's exponent is not linnik_22000e's")
    route = grab(r"⟨(.+?), (.+?), (.+?)⟩", definition("Linnik22000E.route22000D"), "the route's parameters")
    cited.update({"Linnik22000E.route22000D", "SieveCurveGlue.WindowOKHM", "SieveCurveGlue.hmBound"})
    need((q(route.group(1)), q(route.group(2)), q(route.group(3))) == (L, u1, u2),
         "route22000D's parameters are not window_22000d's")
    c = {**form("SieveCurveGlue.WindowOKHM"), **form("SieveCurveGlue.hmBound")}
    need(c["TOP"] == hp, "the window condition does not stop at the half-plane")
    margin, varpi, k0, k1 = c["M"], c["W"], c["K0"], 1 / c["K1"]

    def ends(x, beta, g):
        """The window's ends allowed at β for the exponent x, as winEnds of site/zeros.html computes them, in exact
        arithmetic."""
        th, b = x - margin, beta + varpi
        lo = (x * b + g / 2 + F(1, 2) - th) / (b - F(1, 2))
        hi = (th - x * b - g / 2) / (1 - b)
        k = b - F(1, 2) - (k1 - kd) / 2
        if k > 0:
            lh = (x * b + g + (k0 + kd + 2 * ke) / 2 - th) / k
            if lh <= min(1, hi):
                lo = min(lo, lh)
        return lo, hi

    def exact(x):
        """The widest window at the exponent x, in units of x: on each piece of g* its ends move monotonically, so
        the piece's ends suffice."""
        out = [F(-10), F(10)]
        for lo, hi, A in pieces:
            for beta in (lo, hi):
                a, b = ends(x, beta, F(1) if A is None else A * (1 - beta))
                out = [max(out[0], a / x), min(out[1], b / x)]
        return out

    def fits(x):
        lo, hi = exact(x)
        return lo <= u1 and u2 <= hi

    exact_lo, exact_hi = exact(L)
    need(fits(L), "the Lean's window does not lie in the exact window computed here")
    # The least exponent at which the Lean's window still fits, by bisection: it fits at L, and not at 1 + A/2 for
    # g*'s largest exponent A, below which there is no window.
    x0, x1 = 1 + gmax / 2, L
    need(not fits(x0), f"the Lean's window fits at 1 + {t(gmax)}/2")
    for _ in range(40):
        x0, x1 = (x0, (x0 + x1) / 2) if fits((x0 + x1) / 2) else ((x0 + x1) / 2, x1)
    corners = x1

    # The certificate: the bound on its total that the kernel checks is less than K.
    cert = "SieveDeep.totalD_lt_22000E"
    need(statement(res(cert)) == "theorem totalD_lt_22000E : totalD < K", f"{cert} no longer says totalD < K")
    top = grab(r"rw \[totalD_eq_rowsJD\] exact lt_of_le_of_lt (\w+) \(by decide \+kernel\)$", definition(cert),
               f"the proof of {cert}").group(1)
    m = grab(r"rowsJD 0 (\d+) 0 \1 ≤ (\d+)$", statement("SieveDeep." + top), f"the bound of SieveDeep.{top}")
    k = int(grab(r"def K : ℕ := 2 \^ (\d+)$", definition("SieveCert.K"), "the certificate's K").group(1))
    bound = F(int(m.group(2)), 2 ** k)
    need(bound < 1, f"the bound of SieveDeep.{top} is not less than K")

    # The paper: its numbers, which the page cites.
    main, supp, bib, r = tex("main.tex"), tex("supplement.tex"), tex("references.tex"), refs()
    sup = "supplement " + r["supComputations"]
    hb = float(says(r"Heath-Brown \\cite\{heath-brown92\} reached \$L = ([\d.]+)\$", main, "Heath-Brown").group(1))
    xy = float(says(r"and then \$L = ([\d.]+)\$ \\cite\{xylouris11\}", main, "Xylouris").group(1))
    hb_src = says(r"\\bibitem\{heath-brown92\} .*?\\emph\{[^}]*\}, (.+?) \((\d{4})\),", bib, "reference for Heath-Brown")
    xy_src = says(r"\\bibitem\{xylouris11\} .*?\\emph\{[^}]*\}, (.+?), Bonn, (\d{4})\.", bib, "reference for Xylouris")
    m = says(r"prove \$A = (\d+)/(\d+)\$, uniformly in \$q\$ and \$T\$", main, "exponent of Chen, Gupta and Li")
    cgl = F(int(m.group(1)), int(m.group(2)))
    m = says(r"which is \$(\d+)/(\d+)\$ for \$A = (\d+)/(\d+)\$", main, "threshold 1 + A/2")
    floor = F(int(m.group(1)), int(m.group(2)))
    need(F(int(m.group(3)), int(m.group(4))) == cgl and floor == 1 + cgl / 2, "the paper's threshold is not 1 + A/2")
    says(r"Chen--Gupta--Li's estimate \\cite\{cgl\} & density deduction \(not formalised\) &", main, "row for 7/3")
    m = says(r"in steps & sieve, computed \(not formalised\) & \$(\d+)/(\d+) = ([\d.]+)\$", main, "row for the "
             "classical sieve")
    classic = F(int(m.group(1)), int(m.group(2)))
    excess = F(says(r"and the excess \$(\d+/\d+)\$ of the library's steps", supp, "classical steps").group(1))
    cpeak = F(says(r"The window is then set at \$3/4\$, where both exponents are \$(\d+/\d+)\$", supp,
                   "classical peak").group(1)) + excess

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
    ladder += [{"group": "Harman's sieve: below the density exponent"},
               {"label": "with Ingham's and Huxley's estimates in steps", "L": float(classic), "text": t(classic),
                "dec": dec(classic, 4), "kind": "other", "src": f"computed, not formalised ({sup})"},
               {"label": "with the curve <i>g*</i> and a bilinear Type I estimate", "L": float(Lmain), "text": t(Lmain),
                "dec": dec(Lmain, 3), "kind": "lean", "src": "Linnik22000E.linnik_22000e", "main": True}]

    la = [{"A": float(Agrh), "L": float(Lgrh), "kind": "limit", "role": "dh", "text": t(Lgrh) + " + η",
           "label": f"the density hypothesis, A = {t(Agrh)}, which GRH implies",
           "src": "LinnikGRH.linnik_two_of_GRH, under GRH"}]
    for x, n, label in deduction:
        if x <= F(252, 100):
            la.append({"A": float(x), "L": float(x), "kind": "lean", "role": "ded",
                       "text": (t(x) if x.denominator < 1000 else dec(x, 4)) + " + η",
                       "label": "the deduction, " + re.sub(r"<[^>]+>", "", label), "src": n})
    la.append({"A": float(cpeak), "L": float(classic), "kind": "other", "role": "classic", "text": t(classic),
               "label": f"the sieve, with Ingham's and Huxley's estimates in steps (peak {t(cpeak - excess)} + "
                        f"{t(excess)})", "src": f"computed, not formalised ({sup})"})
    la.append({"A": float(gmax), "L": float(Lmain), "kind": "lean", "role": "main", "text": t(Lmain),
               "label": "the sieve, with the curve g* and a bilinear Type I estimate",
               "src": "Linnik22000E.linnik_22000e"})

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
        "ladder": ladder, "la": la,
        "window": {"L": float(L), "Lt": t(L), "Ld": dec(L, 4), "u1": float(u1), "u2": float(u2), "u1t": dec(u1, 5),
                   "u2t": dec(u2, 5), "margin": float(margin), "varpi": float(varpi), "d": float(kd), "e": float(ke),
                   "k0": float(k0), "k1": float(k1)},
        "cert": {"corners": cut(corners, 7), "bound": cut(bound, 5), "lean": cert},
    }
    texts = {
        "hp": t(hp), "hpWidth": t(1 - hp), "bandLo": t(band[0]), "bandHi": t(band[1]),
        "thetaLo": t(th_lo), "thetaHi": t(th_hi), "selberg": sel, "onLine": t(two),
        "kvA": f"{kv.group(1)}/{kv.group(2)}", "kvB": f"{kv.group(3)}/{kv.group(4)}",
        "nzeta": {1: "one", 2: "two", 3: "three", 4: "four", 5: "five"}.get(len(zeta), str(len(zeta))),
        "npieces": str(len(pieces)), "gmax": dec(gmax, 4), "gmaxLo": t(pieces[peak][0]), "gmaxHi": t(pieces[peak][1]),
        "cgl": t(cgl), "floor": t(floor), "grh": t(Lgrh),
        "L": t(Lmain), "Ldec": dec(Lmain, 4), "u1": dec(u1, 5), "u2": dec(u2, 5),
        "exactLo": cut(exact_lo, 8), "exactHi": cut(exact_hi, 8),
        "nresults": str(len(shown)),
        "commit": f'<a href="{REPO}/tree/{sha}">{sha[:7]}</a>' if sha else "the working tree",
        "date": html.escape(day or ""),
        **{k: html.escape(v) for k, v in r.items()},
        "theorems": theorem_rows(hp, band, th_lo, th_hi, slog, sel, two, zeta, c524, Lmain),
    }
    for k in ("hp", "hpWidth", "bandLo", "bandHi", "thetaLo", "thetaHi", "selberg", "onLine", "kvA", "kvB", "nzeta",
              "npieces", "gmax",
              "gmaxLo", "gmaxHi", "cgl", "floor", "grh", "L", "Ldec", "u1", "u2", "exactLo", "exactHi", "nresults"):
        texts[k] = html.escape(texts[k])
    return data, texts, named, results


def theorem_rows(hp, band, th_lo, th_hi, slog, sel, two, zeta, c524, Lmain):
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
    rows.append((f"Every reduced residue class mod {m('q')} contains a prime {m('p ≤ Kq')}"
                 f"<sup class=\"math\">{t(Lmain)}</sup>", ["Linnik22000E.linnik_22000e"]))
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
              f"theorem counts_7d glues in; the exact window [{texts['exactLo']}…, {texts['exactHi']}…] contains the "
              f"Lean's, which fits down to L = {data['cert']['corners']}…")
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
