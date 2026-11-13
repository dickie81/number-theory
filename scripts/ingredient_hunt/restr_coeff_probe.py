#!/usr/bin/env python3
"""Restricted-coefficient LV probe: does the interval/block detector saturate MVT?

CGL at T=1 reduces to S_I(chi)=sum_{n in I} chi(n) for |I|~q^{7/18}.
Test whether top-R large values of interval polynomials can force
|W| / (N^2/V^2 + q N/V^2) close to 1 (MVT saturation), or whether there is
slack that a restricted LV theorem could exploit.

Also: linear-in-k barrier as a W-set — can interval coeffs make |D| large on a
linear-phase-aligned character set? (bridge to signed barrier)
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from sympy import nextprime, isprime

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "cgl_s3"))
from probe import Field, tpm  # noqa: E402

SIGMA = 5 / 7


def eta_ratio(F, b, W, eta: float) -> float:
    """|W| / (N^2/V^2 + q^{1-eta} N/V^2) at V = min_|D| on W (top-R threshold)."""
    wb = F.w * b
    c2 = float(np.vdot(wb, wb).real)
    D = F.D(b)
    DW = D[W]
    V2 = float(np.min(np.abs(DW)) ** 2) if len(W) else 1.0
    # MVT form uses sum_W |D|^2 <= (q+N) c2, so |W| <= (q+N)c2 / V^2
    # Proposed: |W| <= C (N^2/V^2 * c2/N?); match mvt_beyond_attack scaling:
    # |W| << N^2/V^2 + q^{1-eta} N/V^2  for |b|~1 unit energy.
    # Normalise: use V relative to unit, c2 ~ ||w||^2
    N, q = F.N, F.q
    # Empirically: bound = (N**2 / V2 + (q ** (1-eta)) * N / V2) * (c2 / max(np.sum(F.w**2),1))
    # Simpler honest: compare |W| to classical MVT bound with q -> q^{1-eta}
    bound = (N + q ** (1 - eta)) * c2 / max(V2, 1e-300)
    return len(W) / bound if bound > 0 else 0.0


def run(q0: int) -> None:
    q = q0 if isprime(q0) else int(nextprime(q0))
    F = Field(q)
    R = max(1, int(round(q ** (2 / 3))))
    print(f"q={q} N={F.N} R={R}")

    # interval
    b = np.ones(len(F.ns), dtype=complex)
    D = F.D(b)
    W = np.argpartition(np.abs(D) ** 2, -R)[-R:]
    print("  interval top-R eta-ratios:")
    for eta in [0.0, 0.02, 0.05, 0.1, 0.15]:
        r = eta_ratio(F, b, W, eta)
        print(f"    eta={eta:.2f}: |W|/bound={r:.4f}  {'OK' if r<=1 else 'FAIL'}")

    # ADV
    _, Wa, ba, _ = tpm(F, b.copy(), R, iters=30)
    print("  ADV top-R eta-ratios:")
    for eta in [0.0, 0.02, 0.05, 0.1, 0.15]:
        r = eta_ratio(F, ba, Wa, eta)
        print(f"    eta={eta:.2f}: |W|/bound={r:.4f}  {'OK' if r<=1 else 'FAIL'}")

    # Linear-in-k W: characters k=1..R (as indices); measure |D| on that W for interval b
    Wlin = np.arange(1, R + 1)
    Dabs = np.abs(D[Wlin])
    Vmed = float(np.median(np.abs(D)))
    print(f"  interval |D| on linear W[1..R]: median={float(np.median(Dabs)):.3e}  "
          f"max={float(Dabs.max()):.3e}  global_median={Vmed:.3e}  "
          f"frac_above_global_med={float(np.mean(Dabs>=Vmed)):.3f}")


def main():
    for q in ([int(a) for a in sys.argv[1:]] or [1009, 2003, 5003]):
        run(q)
        print()


if __name__ == "__main__":
    main()
