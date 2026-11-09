#!/usr/bin/env python3
"""Attack 1(iii) deep dive: incidence formulation for sum_a H_a^2, hypothesis checks,
small/large split bookkeeping, numerical incidence counts for extremal f.

Discrete model over F_q (q prime), T=1 regime, M ~ q^{2/9} (CGL critical M~qT/N with N=q^{7/9}).

Setup (single b=1):
  Triples m=(m1,m2,m3) with m_i in {1,...,M} (positive; signs omitted — noted).
  Affine map alpha_m(u) = (m1*u + m3) * inv(m2)  in F_q  (u in F_q).
  For a in F_q^*: L_a = {m : a*m1 + b*m2 + m3 ≡ 0 mod q}.
  H_a(u) = sum_{m in L_a} f(alpha_m(u))   (f: F_q -> R>=0).

Then sum_a ||H_a||_ell2^2 = sum_a sum_u H_a(u)^2
  = sum_{m,m'} 1_{compatible(m,m')} sum_u f(alpha_m(u)) f(alpha_{m'}(u))
where compatible means exists a with both congruences.

Incidence dictionary (points/lines in F_q^2):
  Point set P_f subset F_q^2 associated to f:
    - sparse indicator: P = {(u, y_u)} a graph, OR for f=1_U: P = U x {0} unsuitable;
    - for counting affine incidences we use:
      P = {(x,z) in F_q^2 : f(x)>0 and we track z as a second coordinate from another copy}
  Cleaner counting used below (exact for indicator f=1_U):
    I_aff(U; M) = # { (u, m) : u in U, m in [1,M]^3, alpha_m(u) in U }
    which is the number of incidences between points U (embedded as a 1-D set) and the
    family of graphs of affine maps alpha_m — equivalently incidences between
    P = {(u, v) : u in U, v in U}  (Cartesian) and lines
    ell_m : v = (m1/m2) u + m3/m2.
  GCD-hit subfamily L_a: those ell_m with a m1 + m2 + m3 ≡ 0 (b=1).

Stevens-de Zeeuw (Cartesian): I(A×B, L) ≪ |A|^{3/4}|B|^{1/2}|L|^{3/4} + |A||B| + |L|
  under |A||L| < q^2 (one form); general: I ≪ (|P||L|)^{11/15}+|P|+|L| for |P|^{13}|L|^{-2}<q^{15}.

Vinh (any P,L): |I - |P||L|/q| ≤ sqrt(q |P||L|), so I ≤ |P||L|/q + sqrt(q|P||L|).

Rudnev point-plane in F^3: needs a lift; noted but not the primary dictionary here.

We check which hypotheses hold at critical M=q^{2/9}, |U| varying (random / rational-like).
Bookkeeping: feed the best available I-bound into sum_a ||H_a||^2 and through CGL (2.3)->(2.4)
to an explicit alpha at sigma=5/7.

Label: Numerical + Heuristic bookkeeping. No theorem claimed.
"""
from __future__ import annotations

import math
import sys
from dataclasses import dataclass

import numpy as np
from sympy import nextprime


def inv_mod(x: int, q: int) -> int:
    return pow(int(x) % q, -1, q)


def make_U_random(q: int, size: int, rng: np.random.Generator) -> np.ndarray:
    return np.sort(rng.choice(q, size=min(size, q), replace=False))


def make_U_rational(q: int, B: int) -> np.ndarray:
    """{ floor(r/s * q) mod q : 1<=r,s<=B } — discrete rational set in F_q."""
    S = set()
    for s in range(1, B + 1):
        for r in range(1, 2 * B + 1):
            # represent r/s in F_q as r * s^{-1} if s invertible
            if math.gcd(s, q) == 1:
                S.add((r * inv_mod(s, q)) % q)
            # also include floor embedding
            S.add(int(round(r / s * (q - 1) / 2)) % q)
    return np.array(sorted(S), dtype=np.int64)


@dataclass
class IncCount:
    q: int
    M: int
    kind: str
    Usize: int
    nlines: int
    I_all: int  # incidences of U×U with all affine lines from M-triples
    I_gcd: int  # incidences restricted to GCD-hit lines (union over a, counted with mult)
    # predicted bounds
    SdZ_cart: float
    SdZ_ok: bool
    Vinh: float
    trivial: float
    CGL_T2_scale: float  # q^2 M^4 |U| as rough stand-in for second Prop.8.1 term on 1_U


def count_incidences(q: int, M: int, U: np.ndarray, max_lines: int, rng: np.random.Generator) -> tuple[int, int, int]:
    """Count I(P,L) for P=U×U and lines v = s u + c with s=m1*m2^{-1}, c=m3*m2^{-1}.
    Returns (I_all, I_gcd_weighted, nlines_used).
    GCD-hit: for b=1, line is GCD-hit for a iff a*m1 + m2 + m3 ≡ 0, i.e. some a.
    Every line with m1≠0 is GCD-hit for exactly one a; so I_gcd_unweighted = I_all.
    The WEIGHT in Prop.8.1 is q on GCD-hit, so the contribution to sum_a H_a is
    counting each such incidence once per a-slot — already accounted by unique a.
    What matters numerically is the *overlap structure*: we also count
    double-incidences for sum_a H_a^2 via pair enumeration when cheap.
    """
    Uset = set(int(x) for x in U)
    ms = np.arange(1, M + 1, dtype=np.int64)
    n = len(ms)
    ntrip = n**3
    if ntrip <= max_lines:
        m1 = np.repeat(ms, n * n)
        m2 = np.tile(np.repeat(ms, n), n)
        m3 = np.tile(ms, n * n)
        scale = 1
    else:
        idx = rng.integers(0, n, size=(max_lines, 3))
        m1, m2, m3 = ms[idx[:, 0]], ms[idx[:, 1]], ms[idx[:, 2]]
        scale = ntrip / max_lines

    I = 0
    # For each line, count #u in U with alpha_m(u) in U
    for i in range(len(m1)):
        mm1, mm2, mm3 = int(m1[i]), int(m2[i]), int(m3[i])
        s = (mm1 * inv_mod(mm2, q)) % q
        c = (mm3 * inv_mod(mm2, q)) % q
        # count u in U with (s*u+c) mod q in U
        cnt = 0
        for u in U:
            v = (s * int(u) + c) % q
            if v in Uset:
                cnt += 1
        I += cnt
    I_est = int(round(I * scale))
    # As noted: every triple with m1 invertible is GCD-hit for unique a, so I_gcd ≈ I_all
    return I_est, I_est, int(ntrip)


def sdz_cartesian_bound(A: int, B: int, L: int) -> float:
    """Stevens–de Zeeuw Cartesian form (implied constant =1 for scale comparison)."""
    return A**0.75 * B**0.5 * L**0.75 + A * B + L


def sdz_hypothesis_ok(P: int, L: int, q: int) -> bool:
    """General SdZ: |P|^{13}|L|^{-2} < q^{15}."""
    if L == 0:
        return True
    return (P**13) / (L**2) < q**15


def vinh_bound(P: int, L: int, q: int) -> float:
    return P * L / q + math.sqrt(q * P * L)


def trivial_bound(P: int, L: int) -> float:
    return min(P * L, P * math.sqrt(L) + L, L * math.sqrt(P) + P)  # crude


def run_one(q: int, M: int, kind: str, Usize: int, max_lines: int, rng: np.random.Generator) -> IncCount:
    if kind == "random":
        U = make_U_random(q, Usize, rng)
    elif kind == "rational":
        B = max(3, int(round(Usize**0.5)))
        U = make_U_rational(q, B)
        # subsample if huge
        if len(U) > Usize:
            U = np.sort(rng.choice(U, size=Usize, replace=False))
    else:
        raise ValueError(kind)
    P = len(U) ** 2  # Cartesian U×U
    I_all, I_gcd, nlines = count_incidences(q, M, U, max_lines, rng)
    SdZ = sdz_cartesian_bound(len(U), len(U), nlines)
    SdZ_ok = sdz_hypothesis_ok(P, nlines, q)
    Vin = vinh_bound(P, nlines, q)
    triv = float(len(U) * nlines)  # each line hits <=|U| points of graph-like; for U×U <=|U| per line if functional
    # better trivial for U×U + functional graph lines: I <= |U| * nlines
    triv = float(len(U) * nlines)
    T2 = (q**2) * (M**4) * len(U)  # rough
    return IncCount(
        q=q,
        M=M,
        kind=kind,
        Usize=len(U),
        nlines=nlines,
        I_all=I_all,
        I_gcd=I_gcd,
        SdZ_cart=SdZ,
        SdZ_ok=SdZ_ok,
        Vinh=Vin,
        trivial=triv,
        CGL_T2_scale=T2,
    )


def bookkeeping_print() -> None:
    """Explicit exponent bookkeeping at sigma=5/7, y=7/9, T=1.
    CGL from Prop.8.1 -> (2.3): S3 ≲ (q)^2 |W|^{3/2} + q N |W|^{1/2} E^{1/2}
    First term from J's M^6 piece (M~q/N = q^{2/9}): gives |W| ≲ q^{4/3} N^{2-4σ} after SVD,
    i.e. alpha_S3 = 4/3 + y(2-4σ) = 2/3 at criticality.

    Incidence improvement scenarios on the SECOND Prop.8.1 term only
    (energy pathway / GCD-hit ∑H_a^2):
      replace q^2 M^4 by q^2 M^{4-θ} or by Vinh-scale.
    On the FIRST term (random pathway):
      replace q M^6 by something from incidences — typically NOT improved by SdZ
      (Cauchy-Schwarz / L1 saturation is combinatorial).

    Vinh on P=U×U, |L|=M^3: I ≤ |P||L|/q + sqrt(q|P||L|)
    At critical M=q^{2/9}, |L|=q^{2/3}.
    For |U|=q^β, |P|=q^{2β}:
      Vinh = q^{2β} q^{2/3}/q + sqrt(q * q^{2β} * q^{2/3}) = q^{2β-1/3} + q^{1/2+β+1/3}
            = q^{2β-1/3} + q^{β+5/6}
    Trivial functional: I ≤ |U||L| = q^{β+2/3}
    SdZ Cartesian: |U|^{5/4} |L|^{3/4} + |U|^2 + |L|
      = q^{5β/4} q^{1/2} + q^{2β} + q^{2/3} = q^{5β/4+1/2} + q^{2β} + q^{2/3}

    When does SdZ hypothesis hold? |P|^{13}|L|^{-2} < q^{15}
      q^{26β} / q^{4/3} < q^{15} => 26β - 4/3 < 15 => 26β < 15+4/3 = 49/3
      β < (49/3)/26 = 49/78 ≈ 0.628

    Rational extremiser: |U| ~ B^2 with B ~ M^{1/2} ~ q^{1/9}, so β ≈ 2/9 ≈ 0.222 < 0.628
    — SdZ hypothesis OK for rational.
    Random with β=1/2: 0.5 < 0.628 OK; β=2/3 fails.

    Feeding into J: the second CGL term is ~ q^2 M^4 ||f||_2^2 ~ q^2 M^4 |U| for 1_U
    = q^2 q^{8/9} q^β = q^{2+8/9+β} = q^{26/9+β}

    If ∑_a ||H_a||^2 ≲ (best I-bound)^2 / |U| or similar conversions...
    Honest stall: converting I(P,L) into ∑||H_a||^2 needs Cauchy-Schwarz on fibres;
    the conversion loses factors. We report the RAW incidence exponents vs trivial
    and vs CGL's second-term scale, without claiming a theorem.
    """
    print("=== Bookkeeping at σ=5/7, y=7/9, T=1, M=q^{2/9}, |L|=M^3=q^{2/3} ===\n")
    print("SdZ Cartesian hypothesis |P|^{13}|L|^{-2}<q^{15} with |P|=|U|^2=q^{2β}:")
    print("  <=> β < 49/78 ≈ 0.6282")
    print("  Rational extremiser β≈2/9≈0.222: HYPOTHESIS HOLDS")
    print("  Random β=1/2: HOLDS; β=2/3: FAILS; β=1 (flat-ish): FAILS\n")

    print("Incidence bound exponents (log_q I) for |U|=q^β:")
    print(f"  {'β':>6} {'triv':>8} {'SdZ':>8} {'Vinh':>8} {'SdZ_ok':>8} {'best':>8} {'vs_triv':>8}")
    for beta in [2 / 9, 0.3, 0.4, 0.5, 0.6, 2 / 3, 0.8, 1.0]:
        triv = beta + 2 / 3
        sdz = max(5 * beta / 4 + 0.5, 2 * beta, 2 / 3)
        vinh = max(2 * beta - 1 / 3, beta + 5 / 6)
        ok = beta < 49 / 78
        # small/large split: use SdZ if ok else Vinh
        if ok:
            best = min(triv, sdz, vinh)
            which = "SdZ-split"
        else:
            best = min(triv, vinh)
            which = "Vinh-only"
        # actually take min of applicable
        cands = [triv, vinh]
        if ok:
            cands.append(sdz)
        best = min(cands)
        print(
            f"  {beta:6.3f} {triv:8.3f} {sdz:8.3f} {vinh:8.3f} {str(ok):>8} {best:8.3f} {triv-best:8.3f}  ({which})"
        )

    print("\nConsequence for Prop.8.1 second term / S3 pathway (Heuristic):")
    print("  CGL second term scale ~ q^2 M^4 |U| = q^{26/9 + β} for 1_U.")
    print("  Even if I improves on trivial by Δ, converting I→∑||H_a||^2 via CS")
    print("  typically yields at most the SAME Δ/2 in the J-exponent, hence")
    print("  δ ≲ Δ/2 in S3's q^{2-δ}. At rational β=2/9:")
    beta = 2 / 9
    triv = beta + 2 / 3
    sdz = max(5 * beta / 4 + 0.5, 2 * beta, 2 / 3)
    vinh = max(2 * beta - 1 / 3, beta + 5 / 6)
    Delta = triv - min(triv, sdz, vinh)
    print(f"  Δ_I(rational) = triv-best = {triv:.3f}-{min(triv,sdz,vinh):.3f} = {Delta:.3f}")
    print(f"  Optimistic δ ≲ {Delta/2:.3f} in S3; then c=4/3-2δ/3, alpha=c+y(2-4σ), A=alpha/(1-σ)")
    delta = Delta / 2
    c = 4 / 3 - 2 * delta / 3
    y, s = 7 / 9, 5 / 7
    alpha = c + y * (2 - 4 * s)
    # also min with MVT=2/3
    alpha_eff = min(alpha, 2 / 3)
    A = alpha_eff / (1 - s)
    print(f"  optimistic δ={delta:.4f} => c={c:.4f} => S3-alpha={alpha:.4f}")
    print(f"  min(S3-alpha, MVT=2/3)={alpha_eff:.4f} => A={A:.4f}")
    if alpha >= 2 / 3:
        print("  => S3-alpha still ≥ MVT; NO improvement of A=7/3 from this alone.")
    else:
        print(f"  => would beat MVT-tie, A={A:.4f} < 7/3 (still Heuristic; conversion not proved).")

    print("\nVinh for LARGE β (where SdZ fails):")
    for beta in [2 / 3, 0.8, 1.0]:
        triv = beta + 2 / 3
        vinh = max(2 * beta - 1 / 3, beta + 5 / 6)
        print(f"  β={beta:.3f}: triv={triv:.3f}, Vinh={vinh:.3f}, saving={triv-vinh:.3f}")
        print(f"    Vinh beats trivial? {vinh < triv}. (For β=1: Vinh=max(5/3,11/6)=1.833, triv=5/3≈1.667 — Vinh WORSE)")


def main(argv: list[str]) -> None:
    bookkeeping_print()
    print("\n=== Numerical incidence counts ===\n")
    qs = [int(nextprime(n)) for n in (503, 1009, 2003, 3001)]
    if argv:
        qs = [int(nextprime(int(x) - 1)) for x in argv]
    rng = np.random.default_rng(0)
    max_lines = 2000
    results = []
    for q in qs:
        M = max(2, min(6, int(round(q ** (2 / 9)))))
        for kind, usize_mult in [("random", 1.0), ("rational", 1.0)]:
            # |U| ~ q^{2/9} for rational-scale; also try q^{1/3}
            for beta, tag in [(2 / 9, "β=2/9"), (1 / 3, "β=1/3")]:
                Usize = max(8, int(round(q**beta)))
                r = run_one(q, M, kind, Usize, max_lines, rng)
                results.append(r)
                print(
                    f"q={q:5d} M={M} {kind:8s} {tag} |U|={r.Usize:4d} |L|={r.nlines:6d}  "
                    f"I={r.I_all:.3e}  triv={r.trivial:.3e}  SdZ={r.SdZ_cart:.3e}(ok={r.SdZ_ok})  "
                    f"Vinh={r.Vinh:.3e}  I/triv={r.I_all/max(r.trivial,1):.3f}"
                )
    # fit log I vs log q for rational β=2/9
    print("\n=== Fit log I ~ a + b log q (rational, target |U|~q^{2/9}) ===")
    rat = [r for r in results if r.kind == "rational" and abs(np.log(r.Usize) / np.log(r.q) - 2 / 9) < 0.15]
    if len(rat) >= 3:
        qs_ = np.log([r.q for r in rat])
        Is = np.log([max(r.I_all, 1) for r in rat])
        trivs = np.log([max(r.trivial, 1) for r in rat])
        bI, aI = np.polyfit(qs_, Is, 1)
        bT, aT = np.polyfit(qs_, trivs, 1)
        seI = float(np.std(Is - (aI + bI * qs_)) / np.sqrt(np.sum((qs_ - qs_.mean()) ** 2)))
        seT = float(np.std(trivs - (aT + bT * qs_)) / np.sqrt(np.sum((qs_ - qs_.mean()) ** 2)))
        print(f"  slope_I={bI:.3f}±{seI:.3f}  slope_triv={bT:.3f}±{seT:.3f}  saving={bT-bI:.3f}±{(seI**2+seT**2)**0.5:.3f}")
        print(f"  theory triv=β+2/3={2/9+2/3:.3f}, SdZ={max(5*(2/9)/4+0.5, 4/9, 2/3):.3f}")


if __name__ == "__main__":
    main(sys.argv[1:])
