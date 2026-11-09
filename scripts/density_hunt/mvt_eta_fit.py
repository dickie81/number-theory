#!/usr/bin/env python3
"""MVT-beyond eta scan: fit growth of ADV ratio in q; estimate largest eta>0 consistent with data.

For each prime q and eta in a grid, at V = V_R (R-th largest |D| so |W|~R=q^{2/3}):
  bound(eta) = (q^{1-eta} + N) * c2 / V^2
  ratio(eta) = |W| / bound(eta)

A << statement with fixed eta requires ratio = O(q^eps) for every eps>0, i.e. the
growth exponent rho(eta) in ratio ~ C q^{rho} should satisfy rho(eta) <= 0.

We fit rho(eta) = slope of log(ratio) vs log(q) with a simple SE from residuals,
and report the largest eta with rho+1.96*SE <= 0 (conservative) and with rho<=0 (point estimate).

Finite-q ratio>1 is NOT a counterexample to << ; only a positive growth exponent is evidence against.

Label: Numerical.
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from sympy import nextprime

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "cgl_s3"))
from probe import Field, tpm  # noqa: E402


def adv_ratio_at_eta(q: int, etas: np.ndarray, iters: int = 25) -> dict:
    F = Field(q)
    R = max(1, int(round(q ** (2 / 3))))
    _, _, b, _ = tpm(F, np.ones(len(F.ns), dtype=complex), R, iters=iters)
    D = F.D(b)
    absD = np.abs(D)
    V = float(np.partition(absD, -R)[-R])
    W = np.where(absD >= V * 0.999)[0]
    c2 = float(np.vdot(F.w * b, F.w * b).real)
    N = F.N
    ratios = []
    for eta in etas:
        bound = (q ** (1 - eta) + N) * c2 / max(V**2, 1e-300)
        ratios.append(len(W) / bound if bound > 0 else np.nan)
    return dict(q=q, N=N, R=R, V=V, c2=c2, W=len(W), ratios=np.array(ratios))


def fit_rho(qs: list[int], ratio_matrix: np.ndarray, etas: np.ndarray) -> None:
    """ratio_matrix shape (n_q, n_eta)."""
    logq = np.log(qs)
    print("\n=== Fit ratio ~ C * q^rho  (rho = growth exponent) ===")
    print(f"{'eta':>6} {'rho':>8} {'SE':>8} {'rho+1.96SE':>12} {'point_ok':>9} {'cons_ok':>9}  ratios by q")
    best_point = 0.0
    best_cons = 0.0
    for j, eta in enumerate(etas):
        logs = np.log(np.maximum(ratio_matrix[:, j], 1e-300))
        rho, a = np.polyfit(logq, logs, 1)
        resid = logs - (a + rho * logq)
        se = float(np.std(resid) / np.sqrt(np.sum((logq - logq.mean()) ** 2)))
        cons = rho + 1.96 * se
        point_ok = rho <= 0
        cons_ok = cons <= 0
        if point_ok:
            best_point = float(eta)
        if cons_ok:
            best_cons = float(eta)
        rstr = " ".join(f"{r:.3f}" for r in ratio_matrix[:, j])
        print(
            f"{eta:6.3f} {rho:8.4f} {se:8.4f} {cons:12.4f} {str(point_ok):>9} {str(cons_ok):>9}  {rstr}"
        )
    print(f"\nLargest eta with point-estimate rho<=0: {best_point:.3f}")
    print(f"Largest eta with conservative rho+1.96SE<=0: {best_cons:.3f}")
    print(
        "Interpretation: if best_cons=0 and best_point>0, data mildly allow a small eta "
        "but not at 95%-slope confidence. If both 0, no positive eta supported."
    )


def main(argv: list[str]) -> None:
    # larger q as feasible — tpm at q~3e4 is fine; try up to ~5e4
    q0s = [503, 1009, 2003, 5003, 10007, 20011, 30011]
    if argv:
        q0s = [int(x) for x in argv]
    qs = [int(nextprime(q - 1)) for q in q0s]
    etas = np.round(np.arange(0.0, 0.21, 0.01), 2)
    print(f"etas = {etas.tolist()}")
    print(f"qs = {qs}")
    rows = []
    for q in qs:
        print(f"\nrunning q={q} ...", flush=True)
        row = adv_ratio_at_eta(q, etas, iters=25)
        print(
            f"  N={row['N']} R={row['R']} V={row['V']:.4f} |W|={row['W']}  "
            f"ratio(eta=0)={row['ratios'][0]:.4f} ratio(0.1)={row['ratios'][list(etas).index(0.1)]:.4f}"
        )
        rows.append(row)
    mat = np.vstack([r["ratios"] for r in rows])
    fit_rho(qs, mat, etas)

    # also flat control at same qs (quick)
    print("\n=== Flat control (should retain slack) ===")
    flat_mat = []
    for q in qs:
        F = Field(q)
        R = max(1, int(round(q ** (2 / 3))))
        b = np.ones(len(F.ns), dtype=complex)
        D = F.D(b)
        absD = np.abs(D)
        V = float(np.partition(absD, -R)[-R])
        W = np.where(absD >= V * 0.999)[0]
        c2 = float(np.vdot(F.w * b, F.w * b).real)
        rats = [(len(W) / ((q ** (1 - eta) + F.N) * c2 / V**2)) for eta in etas]
        flat_mat.append(rats)
        print(f"  q={q}: ratio(0)={rats[0]:.4f} ratio(0.1)={rats[10]:.4f} ratio(0.2)={rats[20]:.4f}")
    fit_rho(qs, np.array(flat_mat), etas)


if __name__ == "__main__":
    main(sys.argv[1:])
