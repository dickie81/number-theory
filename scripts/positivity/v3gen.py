#!/usr/bin/env python3
"""Data for Weil positivity on Connes–Consani's subspace V' at support L* = log 3 / 2 (lib/core/V3*.lean).

In the rescaled picture of lib/core/V3Scale.lean (λ = log 3, modes on [−1/2, 1/2]) the Zhu-reduced matrix of each
parity is R = β*·I + C3 (+ the multiples μ_p p̃p̃ᵀ + μ₀e₀e₀ᵀ of the V' constraints), with

    C3 n m = (30λ/π) σₙσₘ √(2n+1)√(2m+1) ∫₀¹ wψ(30s) jₙ(15λs) jₘ(15λs) ds.

The weight side is the L = 1/2 one: the piecewise model of wψ(30s) and its moments `nuN` (lib/core/CmMomData.lean). This script
computes, in exact rational arithmetic, what the Lean side recomputes in the kernel:

* the Bessel polynomial coefficients of jₙ(X̂s), X̂ = 15·l3lo, rounded down to 2⁻¹²⁸ (`q3N`), and upper bounds for
  their error including the Lipschitz move from X̂ to 15λ (`eTN3`);
* the entry centres ĉ3 and the rational entry bound `R3e` of V3FinD (checked here, rechecked by the kernel);
* the pole vector centres p̃ₙ = √(2n+1)·iₙ(λ/4);
* LDLᵀ certificates of A − δI for the even (μ_p, μ₀) and odd (μ_p) centre matrices.

It writes lib/core/V3FinD.lean and lib/core/V3Data.lean. Run from the repository root: python3 scripts/positivity/v3gen.py
"""
import math, pathlib, re, sys
from fractions import Fraction as F
import mpmath as mp

ROOT = pathlib.Path(__file__).resolve().parents[2]
mp.mp.prec = 400


def lean_block(path, name):
    """The text between the brackets of `def name … := [ … ]` in a Lean file."""
    s = (ROOT / path).read_text()
    i = s.index(f"def {name} ")
    j = s.index("[", i)
    depth = 0
    for k in range(j, len(s)):
        if s[k] == "[":
            depth += 1
        elif s[k] == "]":
            depth -= 1
            if depth == 0:
                return s[j + 1:k]
    raise ValueError(name)


nuN = [int(x) for x in lean_block("lib/core/CmMomData.lean", "nuN").split(",")]
sqb = [(F(int(a), int(b)), F(int(c), int(d)))
       for a, b, c, d in re.findall(r"\((\d+)/(\d+), (\d+)/(\d+)\)", lean_block("lib/core/CmData.lean", "sqb"))]
_wh = (ROOT / "lib/core/WeilHead.lean").read_text()
_m = re.search(r"namespace EvenQ\ndef bq : ℚ := \((\d+)/(\d+)\)", _wh)
bq = F(int(_m.group(1)), int(_m.group(2)))
assert len(nuN) == 134 and len(sqb) >= 56

# ---------------------------------------------------------------------------------------------------------------
# constants (must match the Lean definitions)
P, KT, W = 128, 40, 96
l3lo = F(109861228866810969139, 10 ** 20)
l3hi = F(109861228866810969140, 10 ** 20)
plo = F(314159265358979323846, 10 ** 20)
phi = F(314159265358979323847, 10 ** 20)
Xh = 15 * l3lo
dX = 15 * (l3hi - l3lo)
X0 = F(33, 2)
eps_w = F(16, 10 ** 10)
fact = math.factorial
H = 28  # head size per parity: modes n = 2i + par, i < 28


def rowG():
    rows = [[F(2, 2 * k + 1) for k in range(W)]]
    for _ in range(55):
        r = rows[-1]
        rows.append([a - b for a, b in zip(r, r[1:])])
    return rows


rows = rowG()


def qx(n):
    return [Xh ** (n + 2 * k) * (-1) ** k * rows[n][k] / (2 ** (n + 1) * fact(n) * fact(2 * k)) for k in range(KT)]


def eTX(n):
    return (Xh ** n / (2 ** (n + 1) * fact(n)) * (2 * Xh ** (2 * KT) / fact(2 * KT) * rows[n][0])
            + F(KT, 2 ** P))


def Lip(n):
    return (2 * n * X0 ** max(n - 1, 0) + 2 * X0 ** n) / (2 ** (n + 1) * fact(n))


print("Bessel coefficients …", file=sys.stderr)
q3N = [[math.floor(c * 2 ** P) for c in qx(n)] for n in range(56)]
eTN3 = [math.ceil((eTX(n) + Lip(n) * dX) * 2 ** P) for n in range(56)]
eU3 = [F(e, 2 ** P) for e in eTN3]
BU3 = [F(33, 4) ** n / fact(n) for n in range(56)]
aq3 = [F(sum(abs(z) for z in q3N[n]), 2 ** P) for n in range(56)]


def sg(n):
    return 1 if (n // 2) % 2 == 0 else -1


def XN3(n, m):
    a, b, o = q3N[n], q3N[m], (n + m) // 2
    return sum(a[k] * sum(b[l] * nuN[o + k + l] for l in range(KT)) for k in range(KT))


def eJU3(n, m):
    return BU3[n] * eU3[m] + (BU3[m] + eU3[m]) * eU3[n]


def bracket(n, m):
    """The two ends K3lo·Z, K3hi·Z of the C3 bracket (before the signs) and the error term of `R3e`."""
    Z = F(XN3(n, m), 2 ** 384)
    a = 30 * l3lo * (1 / phi) * sqb[n][0] * sqb[m][0] * Z
    b = 30 * l3hi * (1 / plo) * sqb[n][1] * sqb[m][1] * Z
    err = 30 * l3hi * (1 / plo) * sqb[n][1] * sqb[m][1] * (56 * eJU3(n, m) + aq3[n] * aq3[m] * 128 / 2 ** 128) + eps_w
    return a, b, err


def R3e(n, m, c, br):
    a, b, err = br
    cc = sg(n) * sg(m) * c
    return max(abs(a - cc), abs(b - cc)) + err


def frnd(x, bits=64):
    return F(round(x * 2 ** bits), 2 ** bits)


print("C3 entries …", file=sys.stderr)
cq, worstR = {}, {}
for par in (0, 1):
    M = [[None] * H for _ in range(H)]
    w = F(0)
    for i in range(H):
        for j in range(H):
            n, m = 2 * i + par, 2 * j + par
            if j < i:
                M[i][j] = M[j][i]
                continue
            br = bracket(n, m)
            c = frnd(sg(n) * sg(m) * (br[0] + br[1]) / 2)
            M[i][j] = c
            w = max(w, R3e(n, m, c, br))
    cq[par], worstR[par] = M, w
    print(f"  par {par}: max R3e = {float(w):.3e}", file=sys.stderr)


# pole vector p̃ₙ = √(2n+1)·iₙ(λ/4)
def iP(n, x):
    x = mp.mpf(x)
    return mp.sqrt(mp.pi / (2 * x)) * mp.besseli(n + mp.mpf(1) / 2, x)


lam = mp.log(3)
pq = {par: [frnd(mp.sqrt(2 * (2 * i + par) + 1) * iP(2 * i + par, lam / 4)) for i in range(H)] for par in (0, 1)}


def mpf(q):
    return mp.mpf(q.numerator) / q.denominator


def centre(par, mu_p, mu_0):
    return [[(bq if i == j else 0) + mu_p * pq[par][i] * pq[par][j] + (mu_0 if i == j == 0 else 0)
             + cq[par][min(i, j)][max(i, j)] for j in range(H)] for i in range(H)]


def lam_min(A):
    return min(mp.eigsy(mp.matrix([[mpf(x) for x in r] for r in A]))[0])


def ldl(A, delta):
    n = len(A)
    B = mp.matrix([[mpf(A[i][j]) for j in range(n)] for i in range(n)]) - mpf(delta) * mp.eye(n)
    L, D = mp.eye(n), [mp.mpf(0)] * n
    for j in range(n):
        D[j] = B[j, j] - sum(L[j, k] ** 2 * D[k] for k in range(j))
        for i in range(j + 1, n):
            L[i, j] = (B[i, j] - sum(L[i, k] * L[j, k] * D[k] for k in range(j))) / D[j]
    Mq = [[frnd(L[j, k]) if j >= k else F(0) for j in range(n)] for k in range(n)]
    Dq = [frnd(v) for v in D]
    assert all(d >= 0 for d in Dq)
    worst = max(abs(A[i][j] - (sum(Mq[k][i] * Dq[k] * Mq[k][j] for k in range(n)) + (delta if i == j else 0)))
                for i in range(n) for j in range(n))
    return Mq, Dq, worst


# ---------------------------------------------------------------------------------------------------------------
# the certificate parameters (V3Cert, V3Main): entry tolerance, multipliers, shift, head tolerance, margin
EPS_C = F(3, 10 ** 9)
EPS_B = F(1, 10 ** 12)  # WeilConst.beta_enc_even
EPS_P = F(1, 10 ** 12)
MU = {0: (F(1000), F(1000)), 1: (F(0), F(0))}
DELTA = {0: F(1, 40), 1: F(45, 10 ** 5)}
RHO = {0: F(1, 10 ** 8), 1: F(1, 10 ** 8)}
MARGIN = {0: F(1, 50), 1: F(4, 10 ** 4)}
ROWS = [(0, 0, 8), (0, 8, 28), (1, 0, 8), (1, 8, 28)]  # (parity, first row, last row + 1) of each kernel-check module


def fr(x):
    return f"({x.numerator}/{x.denominator})" if x.denominator != 1 else f"({x.numerator})"


def flist(xs):
    return "[" + ", ".join(fr(x) for x in xs) + "]"


def fmat(M):
    return "[" + ",\n  ".join(flist(r) for r in M) + "]"


HEAVY = ("-- heavy: a kernel check that needs about 3 GiB of private memory; scripts/build.sh runs at most two heavy "
         "modules at once")


def emit():
    # 1. the entry checks
    for par in (0, 1):
        for i in range(H):
            for j in range(i, H):
                n, m = 2 * i + par, 2 * j + par
                assert R3e(n, m, cq[par][i][j], bracket(n, m)) <= EPS_C, (par, i, j)
    out = ["import CmFinD", "import V3Log", "",
           "/-! # Entry checks at `λ = log 3`: data and the rational entry bound (generated by "
           "`scripts/positivity/v3gen.py`)", "",
           "`q3N`: the coefficients of the polynomial of `jₙ(X̂ s)`, `X̂ = 15·l3lo`, as numerators over `2^128` "
           "(`V3Fin.qh3_chk`);",
           "`eTN3`: upper bounds for its error with the Lipschitz move to `15 λ`, over `2^128` (`V3Fin.eT3_chk`); "
           "`cqE`, `cqO`:",
           "the centres of the entries `C3(2i+par, 2j+par)`, read through `cs` (the upper triangle); `R3e n m c`: "
           "a rational",
           "bound for `|C3 n m − c|` (`V3Fin.entry3`). -/", "", "namespace V3Fin", "", "open CmMom CmData", ""]
    for n in range(56):
        out.append(f"def q3_{n} : List ℤ := [" + ", ".join(str(z) for z in q3N[n]) + "]")
    out.append("")
    out.append("def q3N : List (List ℤ) := [" + ", ".join(f"q3_{n}" for n in range(56)) + "]")
    out.append("")
    out.append("/-- upper bounds for `eTq3` (numerators over `2^128`) -/")
    out.append("def eTN3 : List ℤ := [" + ", ".join(str(z) for z in eTN3) + "]")
    out.append("")
    for par, name in ((0, "cqE"), (1, "cqO")):
        out.append(f"def {name} : List (List ℚ) := " + fmat(cq[par]))
        out.append("")
    out.append('''def qQ3 (n k : ℕ) : ℚ := ((q3N.getD n []).getD k 0 : ℚ) / 2 ^ 128
def eU3 (n : ℕ) : ℚ := (eTN3.getD n 0 : ℚ) / 2 ^ 128
def BU3 (n : ℕ) : ℚ := (33 / 4) ^ n / (n.factorial : ℚ)

def XN3 (n m : ℕ) : ℤ := ((List.range 40).map fun k => ((List.range 40).map fun l =>
  (q3N.getD n []).getD k 0 * (q3N.getD m []).getD l 0 * nuN.getD ((n + m) / 2 + k + l) 0).sum).sum

def aq3 (n : ℕ) : ℚ := ((List.range 40).map fun k => |qQ3 n k|).sum

def eJU3 (n m : ℕ) : ℚ := BU3 n * eU3 m + (BU3 m + eU3 m) * eU3 n

/-- The symmetric reading of a centre matrix: its upper triangle. -/
def cs (cq : List (List ℚ)) (i j : ℕ) : ℚ := WeilTail.getq cq (min i j) (max i j)

def R3e (n m : ℕ) (c : ℚ) : ℚ :=
  let Z : ℚ := (XN3 n m : ℚ) / 2 ^ 384
  let ulo : ℚ := 1 / WeilConst.phi
  let uhi : ℚ := 1 / WeilConst.plo
  let cl := fun k => (sqb.getD k (0, 0)).1
  let ch := fun k => (sqb.getD k (0, 0)).2
  let c' := CmFin.sg n * CmFin.sg m * c
  let a := 30 * V3Log.l3lo * ulo * cl n * cl m * Z
  let b := 30 * V3Log.l3hi * uhi * ch n * ch m * Z
  max |a - c'| |b - c'| + 30 * V3Log.l3hi * uhi * ch n * ch m * (56 * eJU3 n m + aq3 n * aq3 m * 128 / 2 ^ 128)
    + CmFin.εwq

/-- Row `i` of the upper triangle, `j = i, …, 27`. -/
def rowOK3 (par : ℕ) (cq : List (List ℚ)) (εc : ℚ) (i : ℕ) : Bool :=
  (List.range' i (28 - i)).all fun j => decide (R3e (2 * i + par) (2 * j + par) (cs cq i j) ≤ εc)

end V3Fin''')
    (ROOT / "lib/core/V3FinD.lean").write_text("\n".join(out) + "\n")
    ec = f"({EPS_C.numerator} / 10 ^ {len(str(EPS_C.denominator)) - 1})"
    assert EPS_C == F(3, 10 ** 9)
    for k, (par, a, b) in enumerate(ROWS):
        tag = "e" if par == 0 else "o"
        name = f"V3FinR{tag}{0 if a == 0 else 1}"
        sector = "even" if par == 0 else "odd"
        lines = ["import V3FinD", HEAVY, "",
                 f"/-! # Kernel checks of the entry bounds at `λ = log 3`, {sector} sector, rows {a}–{b - 1} "
                 "(upper triangle) -/", "", "namespace V3Fin", ""]
        for i in range(a, b):
            lines.append(f"theorem {tag}{i} : rowOK3 {par} {'cqE' if par == 0 else 'cqO'} {ec} {i} = true := "
                         "by decide +kernel")
        lines += ["", "end V3Fin"]
        (ROOT / f"lib/core/{name}.lean").write_text("\n".join(lines) + "\n")
    # 2. the certificates
    cert = {}
    for par in (0, 1):
        mu_p, mu_0 = MU[par]
        A = centre(par, mu_p, mu_0)
        lm = lam_min(A)
        Mq, Dq, worst = ldl(A, DELTA[par])
        r = RHO[par] - (EPS_B + mu_p * 5 * EPS_P + EPS_C)
        assert worst <= r, (par, float(worst), float(r))
        assert all(abs(x) <= 2 for x in pq[par])
        assert MARGIN[par] <= DELTA[par] - 28 * RHO[par]
        cert[par] = (Mq, Dq, r)
        print(f"par {par}: lam_min {mp.nstr(lm, 6)} delta {float(DELTA[par])} |A - cert| {float(worst):.2e} "
              f"r {float(r):.2e} margin {float(MARGIN[par])}", file=sys.stderr)
    out = ["import V3FinD", "", "/-! # LDLᵀ certificates of the centre matrices at `λ = log 3` (generated by "
           "`scripts/positivity/v3gen.py`)", "",
           "`Aq3 μp μ0 b p c = b·I + μp·p pᵀ + μ0·e₀e₀ᵀ + c`, the centre of the augmented Zhu matrix; "
           "`MqE`/`DqE` (even,",
           f"`μp = μ0 = {MU[0][0]}`, `δ = {DELTA[0]}`) and `MqO`/`DqO` (odd, no multiplier, `δ = {DELTA[1]}`) "
           "give `MᵀDM + δI`;",
           "`pqE` are the centres of the even pole vector `p̃₂ᵢ = √(4i+1)·i₂ᵢ(λ/4)`. -/", "",
           "namespace V3Cert", ""]
    for par, tag in ((0, "E"), (1, "O")):
        Mq, Dq, r = cert[par]
        out.append(f"def Mq{tag} : List (List ℚ) := " + fmat(Mq))
        out.append(f"def Dq{tag} : List ℚ := " + flist(Dq))
        out.append("")
    out.append("def pqE : List ℚ := " + flist(pq[0]))
    out.append("")
    out.append("end V3Cert")
    (ROOT / "lib/core/V3CertD.lean").write_text("\n".join(out) + "\n")
    print("wrote V3FinD, V3FinR*, V3CertD", file=sys.stderr)


if __name__ == "__main__":
    if "--emit" in sys.argv:
        emit()
    else:
        for par in (0, 1):
            for mu in (0, 10, 100, 1000):
                for mu0 in ((0, 1000) if par == 0 else (0,)):
                    print(f"par {par} mu_p {mu} mu_0 {mu0}: lam_min {mp.nstr(lam_min(centre(par, mu, mu0)), 6)}")
