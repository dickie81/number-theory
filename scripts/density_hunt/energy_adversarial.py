#!/usr/bin/env python3
"""Additive energy of near-extremal large-value sets W vs random sets.

W lives in Z/(q-1)Z via discrete logs (scripts/cgl_s3/probe.py). Additive energy
  E+(W) = |{(a,b,c,d) in W^4 : a+b ≡ c+d (mod q-1)}| = sum_r r_W(r)^2
with r_W = 1_W * 1_W. Random set of size R in Z/M expects E+ ~ R^3 + M R^2 (order).
Normalise as E+ / R^3 (structured ~ R or larger relative to R^3 when R^2 >> M;
for R = q^{2/3}, M = q-1, R^2/M = q^{1/3}, so random E+/R^3 ~ 1 + M/R ~ q^{1/3}/R^0...
Actually E+_random ≈ R^3 + 3 R^2 (M-1)/M * R? Standard: E+ = sum |hat 1_W|^4 / M
  = M^{-1} sum_k |sum_{w in W} e(kw/M)|^4.
For random W, E+ ∼ R^3 + M R^2 (leading). Ratio E+/R^3 ∼ 1 + M/R.

At critical R = round(q^{2/3}), M/R ∼ q^{1/3}, so E+/R^3 ∼ q^{1/3}.
A Bohr/arithmetic-progression set of size R has E+ ≍ R^3 * R = R^4 if AP, ratio R;
or for subgroup, even larger. We report E+/R^3 and E+/(R^3 + M R^2).

Does NOT claim anything about S3; supports or kills combinatorial_energy (#06).
"""
from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

# import probe from cgl_s3
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "cgl_s3"))
from probe import Field, tpm  # noqa: E402
from sympy import nextprime  # noqa: E402


def additive_energy(W: np.ndarray, M: int) -> float:
    """E+(W) for W subset of Z/M via FFT of indicator."""
    ind = np.zeros(M, dtype=np.float64)
    ind[np.asarray(W) % M] = 1.0
    r = np.fft.ifft(np.fft.fft(ind) ** 2).real  # r[s] = |{(a,b): a+b≡s}|
    # E+ = sum_s r[s]^2
    return float(np.dot(r, r))


def stats(W, M, R, label):
    E = additive_energy(W, M)
    # Random baseline in Z/M is E+ ~ R^4/M (plus lower-order R^3).
    rand_lead = (R**4) / M
    print(
        f"  {label:28s} |W|={len(W):5d}  E+={E:12.4e}  E+/R^3={E/R**3:8.3f}  "
        f"E+/(R^4/M)={E/rand_lead:7.3f}  M/R={M/R:7.3f}"
    )
    return E


def run_q(q: int, iters: int = 40, n_random: int = 5, seed: int = 0) -> None:
    rng = np.random.default_rng(seed)
    F = Field(q)
    R = max(1, int(round(q ** (2 / 3))))
    M = q - 1
    print(f"q={q} N={F.N} R=q^(2/3)~{R} M={M}")
    # adversarial via truncated power method
    val, Wt, b, it = tpm(F, np.ones(len(F.ns), dtype=complex), R, iters=iters)
    print(f"  tpm objective sum_top|D|^2={val:.4e} after {it+1} iters")
    stats(Wt, M, R, "adversarial (tpm)")
    # also top-R of |K| alone (unweighted flat) as another near-extremiser candidate
    # reuse Field.D with b=1
    D1 = F.D(np.ones(len(F.ns), dtype=complex))
    Wflat = np.argpartition(np.abs(D1) ** 2, -R)[-R:]
    stats(Wflat, M, R, "top-|D| of b=1")
    for t in range(n_random):
        Wr = rng.choice(M, size=R, replace=False)
        stats(Wr, M, R, f"random #{t}")
    # arithmetic progression of length R
    step = max(1, M // R)
    Wap = (np.arange(R) * step) % M
    stats(Wap, M, R, "AP (step M/R)")
    # short interval
    Wint = np.arange(R) % M
    stats(Wint, M, R, "interval [0,R)")


def main(argv: list[str]) -> None:
    qs = [nextprime(10**3), nextprime(10**4), nextprime(3 * 10**4)]
    if argv:
        qs = [int(x) for x in argv]
    for q in qs:
        run_q(q)
        print()


if __name__ == "__main__":
    main(sys.argv[1:])
