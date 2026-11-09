"""Numerics for hypothesis (H): #chi with |S_I(chi)| >= V at x=q^{7/18}, V=x^{5/7}.

Also: fourth/sixth moments, multiplicative energy E4 of I, and a log-log fit of
count / q^{2/3} vs q (local exponent). FFT over characters via discrete log.
"""
from __future__ import annotations

import argparse
import math
import sys

import numpy as np
from sympy import nextprime, primitive_root


def dlog(q: int) -> np.ndarray:
    g = int(primitive_root(q))
    B = 4096
    pw = np.empty(q - 1, dtype=np.int64)
    a = 1
    for j in range(min(B, q - 1)):
        pw[j] = a
        a = a * g % q
    gB = pow(g, B, q)
    step = 1
    for i in range(1, (q - 1 + B - 1) // B):
        step = step * gB % q
        lo, hi = i * B, min((i + 1) * B, q - 1)
        pw[lo:hi] = pw[: hi - lo] * step % q
    ind = np.empty(q, dtype=np.int64)
    ind[pw] = np.arange(q - 1)
    return ind


def E4(lo: int, hi: int) -> int:
    n = np.arange(lo, hi + 1, dtype=np.int64)
    _, c = np.unique((n[:, None] * n[None, :]).ravel(), return_counts=True)
    return int((c.astype(np.int64) ** 2).sum())


def run_one(q: int, sig: float = 5 / 7):
    x = int(round(q ** (7 / 18)))
    V = x**sig
    R = q ** (2 / 3)
    ind = dlog(q)
    rows = []
    for name, lo, hi in [("[1,x]", 1, x), ("(x,2x]", x + 1, 2 * x)]:
        f = np.zeros(q - 1)
        f[ind[lo : hi + 1]] = 1.0
        a = np.abs(np.fft.fft(f))[1:]
        del f
        L = hi - lo + 1
        cnt = int((a >= V).sum())
        a2 = a * a
        M4 = float((a2**2).sum())
        M6 = float((a2**3).sum())
        e4 = E4(lo, hi)
        # multiplicative energy of the interval as a set in F_q^*
        # E_mult ~ #{a/b = c/d : a,b,c,d in I} = E4 when products < q
        rows.append(
            dict(
                name=name,
                q=q,
                x=x,
                L=L,
                V=V,
                R=R,
                count=cnt,
                ratio=cnt / R,
                M4=M4,
                M6=M6,
                M6_over_L6=M6 / L**6,
                E4=e4,
                M4_over_qE4=M4 / ((q - 1) * e4) if e4 else float("nan"),
            )
        )
    return rows


def fit_exponent(qs, ratios):
    """Local log-log: count ~ C q^alpha => ratio = count/q^{2/3} ~ C q^{alpha-2/3}.
    Fit log(ratio) = c + (alpha-2/3) log q over successive pairs and overall."""
    if len(qs) < 2:
        return None
    X = np.log(np.asarray(qs, float))
    Y = np.log(np.asarray(ratios, float))
    # overall least squares
    A = np.vstack([X, np.ones_like(X)]).T
    slope, intercept = np.linalg.lstsq(A, Y, rcond=None)[0]
    alpha = slope + 2 / 3
    # residual stderr
    pred = slope * X + intercept
    dof = max(len(X) - 2, 1)
    se = float(np.sqrt(np.sum((Y - pred) ** 2) / dof))
    # slope stderr
    sxx = float(np.sum((X - X.mean()) ** 2))
    slope_se = se / math.sqrt(sxx) if sxx > 0 else float("inf")
    alpha_se = slope_se
    return dict(alpha=alpha, alpha_se=alpha_se, slope=slope, n=len(X))


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "qs",
        nargs="*",
        help="prime sizes (nextprime of each); default ladder to ~1e5",
    )
    args = ap.parse_args(argv)
    sizes = [int(float(s)) for s in args.qs] or [
        503,
        1009,
        5003,
        10007,
        30011,
        100003,
    ]
    qs = [int(nextprime(s - 1)) for s in sizes]
    all_rows = { "[1,x]": [], "(x,2x]": [] }
    print(
        f"{'q':>8} {'x':>5} {'name':>7} {'count':>7} {'/q^{2/3}':>9} "
        f"{'M6/L^6':>8} {'E4':>10} {'M4/(qE4)':>9}"
    )
    for q in qs:
        for row in run_one(q):
            all_rows[row["name"]].append(row)
            print(
                f"{row['q']:8d} {row['x']:5d} {row['name']:>7} {row['count']:7d} "
                f"{row['ratio']:9.3f} {row['M6_over_L6']:8.2f} {row['E4']:10d} "
                f"{row['M4_over_qE4']:9.3f}"
            )
    print("\n=== log-log fit of count ~ q^alpha (vs 2/3) ===")
    for name, rows in all_rows.items():
        if len(rows) < 3:
            continue
        fit = fit_exponent([r["q"] for r in rows], [r["ratio"] for r in rows])
        print(
            f"{name}: alpha={fit['alpha']:.4f} ± {fit['alpha_se']:.4f} "
            f"(2/3={2/3:.4f}); n={fit['n']}"
        )
        # pairwise local exponents
        print("  pairwise local alpha:")
        for i in range(len(rows) - 1):
            q1, q2 = rows[i]["q"], rows[i + 1]["q"]
            c1, c2 = rows[i]["count"], rows[i + 1]["count"]
            if c1 == 0 or c2 == 0:
                continue
            loc = math.log(c2 / c1) / math.log(q2 / q1)
            print(f"    q={q1}→{q2}: alpha_loc={loc:.4f}")


if __name__ == "__main__":
    main()
