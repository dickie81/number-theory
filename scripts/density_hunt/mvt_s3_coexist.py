#!/usr/bin/env python3
"""MVT vs S3 extremiser coexistence at CGL critical point (sigma=5/7, y=7/9).

Setup (matches scripts/cgl_s3/probe.py): q prime, T=1, N=q^{7/9}, R=q^{2/3}.
Hybrid MVT (CGL (1.2) / LinnikHybrid.mean_value_chars at T=1):
  sum_chi |D(chi)|^2 << (q+N) ||c||_2^2
  => |W| << (q+N) ||c||_2^2 / V^2   for |D|>=V on W
  => alpha envelope max(y(2-2s), 1+y(1-2s)); at (5/7,7/9) both terms give
     y(2-2s)=4/9, 1+y(1-2s)=2/3, so MVT binds at alpha=2/3 via the qTN/V^2 term.

S3/LV extremisers: truncated power method W of size R maximising sum_W |D|^2
(same adversarial W as scripts/cgl_s3).

Honest reading of the numbers: an O(1) factor between |W| and the MVT cardinality
bound is NOT an exponent saving (log(C)/log q -> 0). A hybrid exponent < 2/3 would
need |W|/Wbound_mvt << q^{-eps} on S3-near-extremal samples, or a structural theorem.
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from sympy import nextprime

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "cgl_s3"))
from probe import Field, tpm  # noqa: E402


def mvt_stats(F: Field, b: np.ndarray, W: np.ndarray) -> dict:
    wb = F.w * b
    c2 = float(np.vdot(wb, wb).real)
    D = F.D(b)
    DW = D[W]
    sumW = float(np.vdot(DW, DW).real) if len(W) else 0.0
    Vmin = float(np.min(np.abs(DW))) if len(W) else 0.0
    q, N, R = F.q, F.N, len(W)
    mvt_rhs = (q + N) * c2
    sharp = sumW / mvt_rhs if mvt_rhs > 0 else 0.0
    Wbound = mvt_rhs / max(Vmin**2, 1e-300) if R else 0.0
    return dict(
        sumW=sumW,
        c2=c2,
        Vmin=Vmin,
        sharp_mvt=sharp,
        W=R,
        Wbound_mvt=Wbound,
        W_over_bound=(R / Wbound if Wbound > 0 else 0.0),
        alpha_W=(np.log(R) / np.log(q) if R else float("-inf")),
        alpha_mvt_emp=(np.log(max(Wbound, 1)) / np.log(q)),
    )


def s3_ratio(F: Field, W: np.ndarray) -> float:
    q = F.q
    A = np.zeros(q - 1, dtype=complex)
    A[F.jn] = F.w**2
    Kd = np.fft.fft(A)
    W = np.asarray(W)
    if len(W) == 0:
        return 0.0
    idx = (W[None, :] - W[:, None]) % (q - 1)
    G = Kd[idx]
    E = G - np.diag(np.diag(G))
    trE3 = float(np.sum(E * (E @ E).T).real)
    return trE3 / (q**2 * len(W) ** 1.5)


def short_interval_coeff(F: Field, L: int, rng: np.random.Generator) -> np.ndarray:
    b = np.zeros(len(F.ns), dtype=complex)
    if L >= len(F.ns):
        b[:] = 1
        return b
    start = int(rng.integers(0, len(F.ns) - L + 1))
    b[start : start + L] = 1
    return b


def critical_lv(F: Field, b: np.ndarray, sigma: float = 5 / 7) -> dict:
    D = F.D(b)
    V = F.N**sigma
    W = np.where(np.abs(D) >= V)[0]
    if len(W) == 0:
        return dict(
            R=0,
            alpha=float("-inf"),
            sharp_mvt=0.0,
            W_over_bound=0.0,
            s3=0.0,
            Vmin_over=0.0,
        )
    st = mvt_stats(F, b, W)
    return dict(
        R=len(W),
        alpha=st["alpha_W"],
        sharp_mvt=st["sharp_mvt"],
        W_over_bound=st["W_over_bound"],
        s3=s3_ratio(F, W),
        Vmin_over=st["Vmin"] / V,
    )


def run_q(q: int, seed: int = 0) -> None:
    rng = np.random.default_rng(seed)
    F = Field(q)
    R = max(1, int(round(q ** (2 / 3))))
    Nsig = F.N ** (5 / 7)
    print(
        f"q={q} N={F.N} (~q^(7/9)) R=q^(2/3)={R}  "
        f"V=N^(5/7)={Nsig:.3e}  target alpha=2/3"
    )

    _, Wt, b, it = tpm(F, np.ones(len(F.ns), dtype=complex), R, iters=40)
    st = mvt_stats(F, b, Wt)
    print(
        f"  ADV@R: iters={it} sharp_mvt={st['sharp_mvt']:.4f}  "
        f"|W|/Wbound_mvt={st['W_over_bound']:.4f}  S3/CGL={s3_ratio(F, Wt):.3e}  "
        f"Vmin/Nsig={st['Vmin']/Nsig:.4f}  alpha_mvt_emp={st['alpha_mvt_emp']:.4f}"
    )
    cr = critical_lv(F, b)
    print(
        f"  ADV V-crit: |W|={cr['R']} alpha={cr['alpha']:.4f}  "
        f"sharp_mvt={cr['sharp_mvt']:.4f} W/Wb={cr['W_over_bound']:.4f}  "
        f"S3/CGL={cr['s3']:.3e}"
    )

    for theta, label in [
        (0.1, "L=N^0.1"),
        (0.25, "L=N^0.25"),
        (0.5, "L=N^0.5"),
        (1.0, "L=N"),
    ]:
        L = max(1, int(round(F.N**theta)))
        b2 = short_interval_coeff(F, L, rng)
        st2 = mvt_stats(F, b2, np.argpartition(np.abs(F.D(b2)) ** 2, -R)[-R:])
        cr2 = critical_lv(F, b2)
        print(
            f"  MVT-ish {label:8s}@R: sharp_mvt={st2['sharp_mvt']:.4f}  "
            f"|W|/Wb={st2['W_over_bound']:.4f} S3/CGL={s3_ratio(F, np.argpartition(np.abs(F.D(b2))**2, -R)[-R:]):.3e}  "
            f"V-crit|W|={cr2['R']}"
        )

    Wr = rng.choice(q - 1, size=R, replace=False)
    b1 = np.ones(len(F.ns), dtype=complex)
    stR = mvt_stats(F, b1, Wr)
    print(
        f"  RAND W + flat: sharp_mvt={stR['sharp_mvt']:.4f}  "
        f"S3/CGL={s3_ratio(F, Wr):.3e}  V-crit|W|={critical_lv(F, b1)['R']}"
    )


def main(argv: list[str]) -> None:
    qs = [int(x) for x in argv] if argv else [1009, 10007]
    for q in qs:
        run_q(int(nextprime(q - 1)) if q > 2 else q)
        # If user passed an exact prime, use it; nextprime(q-1) recovers q when q prime.
        print()


if __name__ == "__main__":
    main(sys.argv[1:])
