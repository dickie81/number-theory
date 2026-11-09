#!/usr/bin/env python3
"""Attack 2 numerics: MVT-beyond at (y,V)=(7/9, N^{5/7}), prime q, T=1.

Tests:
  (H1) Amplification of the O(1) coexistence slack: take ADV b from tpm, form
       k-fold 'tensor' / power of the Dirichlet polynomial (coefficients of D^k as
       Dirichlet convolution on the multiplicative group), remeasure |W|/Wbound at
       V_k = N^{k*5/7} renormalised — does the slack become q^{-eps(k)}?
  (H2) Multiplicative-subgroup subdivision: partition characters by cosets of a
       subgroup H < (Z/q)* of size ~ q^alpha, measure S3 and MVT on each piece —
       does any piece beat alpha=2/3 while covering W?
  (H3) Direct check of proposed inequality
       |W| <= C ( N^2/V^2 + q^{1-eta} N / V^2 ) on ADV and random large-value sets
       for eta in {0, 0.05, 0.1, 0.2}; report the smallest eta that holds empirically.

Label: Numerical. No theorem claimed.
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from sympy import nextprime

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "cgl_s3"))
from probe import Field, tpm  # noqa: E402


def mvt_bound(q: int, N: int, c2: float, V: float) -> float:
    return (q + N) * c2 / max(V**2, 1e-300)


def large_value_set(F: Field, b: np.ndarray, V: float) -> np.ndarray:
    D = F.D(b)
    return np.where(np.abs(D) >= V)[0]


def s3_ratio(F: Field, W: np.ndarray) -> float:
    if len(W) == 0:
        return 0.0
    A = np.zeros(F.q - 1, dtype=complex)
    A[F.jn] = F.w**2
    Kd = np.fft.fft(A)
    W = np.asarray(W)
    idx = (W[None, :] - W[:, None]) % (F.q - 1)
    G = Kd[idx]
    E = G - np.diag(np.diag(G))
    trE3 = float(np.sum(E * (E @ E).T).real)
    return trE3 / (F.q**2 * len(W) ** 1.5)


def test_eta(F: Field, b: np.ndarray, sigma: float, etas: list[float]) -> None:
    """Empirical check of |W| <= N^2/V^2 + q^{1-eta} N/V^2 (c2~N for |a|<=1)."""
    V = F.N**sigma
    W = large_value_set(F, b, V)
    wb = F.w * b
    c2 = float(np.vdot(wb, wb).real)
    # Normalise to |a|~1 scale: use c2 as is
    N, q = F.N, F.q
    print(f"    |W_crit|={len(W)}  V=N^{sigma}={V:.3e}  c2={c2:.3e}")
    for eta in etas:
        bound = N**2 / V**2 * c2 / N + (q ** (1 - eta)) * N / V**2 * c2 / N
        # standard MVT uses (q+N)*c2/V^2; proposed replaces q by q^{1-eta}
        # with ||a||_2^2 = c2, number of terms ~N so if |a|<=1, c2<=N
        bound_std = (q + N) * c2 / V**2
        bound_eta = (q ** (1 - eta) + N) * c2 / V**2
        ok = len(W) <= bound_eta
        print(
            f"      eta={eta:.2f}: |W|={len(W)}  bound_eta={bound_eta:.2e}  "
            f"bound_MVT={bound_std:.2e}  holds={ok}"
        )


def amplify_slack(F: Field, b: np.ndarray, R: int, ks: list[int]) -> None:
    """Power amplification: replace b by the coeff of (sum b_n n^{it})^k via
    repeated multiplicative convolution on the support (approx on Z/(q-1)).
    Measure |W|/Wbound for top-R after each power.
    """
    # Work in FFT domain: D = F.D(b); powering D^k is NOT the Dirichlet power
    # (that would be coeff convolution). True Dirichlet power:
    # coeffs live on ns; k-fold additive convolution on log-side = mult. on n-side.
    # On discrete log group: if A[j]=w*b at jn, then k-fold convolution of A
    # corresponds to product of n's (Dirichlet mult.).
    A = np.zeros(F.q - 1, dtype=complex)
    A[F.jn] = F.w * b
    print("  (H1) Dirichlet-power amplification on discrete-log group:")
    cur = A.copy()
    for k in ks:
        if k > 1:
            # convolve (k-fold): FFT multiply
            # rebuild from previous: cur is already k-fold for previous; one more conv with A
            pass
        # compute k-fold convolution of A
        FA = np.fft.fft(A)
        cur = np.fft.ifft(FA**k) * ((F.q - 1) ** (k - 1) if False else 1)
        # actually ifft(FA^k) = A^{*k} without extra factors in numpy
        cur = np.fft.ifft(FA**k)
        # evaluate D on characters = FFT of cur (with weight already in A)
        D = np.fft.fft(cur)
        # top R
        W = np.argpartition(np.abs(D) ** 2, -R)[-R:]
        c2 = float(np.vdot(cur[F.jn], cur[F.jn]).real) if False else float(np.vdot(cur, cur).real)
        # c2 of coeffs on full group
        Vmin = float(np.min(np.abs(D[W])))
        Wb = (F.q + F.N) * max(c2, 1e-300) / max(Vmin**2, 1e-300)
        ratio = R / Wb if Wb > 0 else 0.0
        print(
            f"    k={k}: |W|/Wbound={ratio:.4f}  Vmin={Vmin:.3e}  c2={c2:.3e}  "
            f"alpha_mvt_emp={np.log(max(Wb,1))/np.log(F.q):.4f}"
        )


def subgroup_split(F: Field, b: np.ndarray, R: int, alphas: list[float], rng: np.random.Generator) -> None:
    """(H2) Partition Z/(q-1) into cosets of a subgroup of size ~ q^alpha.
    On the circle group Z/(q-1), subgroups are unique of each order dividing q-1.
    """
    q = F.q
    qm1 = q - 1
    D = F.D(b)
    W0 = np.argpartition(np.abs(D) ** 2, -R)[-R:]
    print(f"  (H2) subgroup split of ADV top-R (R={R}):")
    # factor q-1 to find subgroup orders
    from sympy import divisors

    divs = [d for d in divisors(qm1) if d > 1]
    for alpha in alphas:
        target = max(2, int(round(q**alpha)))
        # pick divisor closest to target
        Hsize = min(divs, key=lambda d: abs(d - target))
        # subgroup H = (qm1/Hsize) * Z/Hsize  i.e. multiples of qm1/Hsize
        step = qm1 // Hsize
        # cosets: residue classes mod step? Subgroup of order Hsize is
        # {0, step, 2*step, ...} with step=qm1/Hsize, order Hsize.
        # Cosets: r + H for r=0..step-1 — there are index = step = qm1/Hsize cosets.
        ncosets = step
        # Restrict: for each coset, take W0 ∩ coset
        sizes = []
        s3s = []
        for r in range(min(ncosets, 64)):  # cap for speed
            Wc = W0[(W0 - r) % step == 0]
            if len(Wc) >= 4:
                sizes.append(len(Wc))
                s3s.append(s3_ratio(F, Wc))
        if not sizes:
            print(f"    alpha~{alpha:.2f} |H|={Hsize}: no nonempty pieces among first cosets")
            continue
        alpha_piece = np.log(np.mean(sizes)) / np.log(q)
        print(
            f"    alpha~{alpha:.2f} |H|={Hsize} ncosets={ncosets}: "
            f"mean|W∩coset|={np.mean(sizes):.1f} (of {min(ncosets,64)} nonempty-ish) "
            f"alpha_piece={alpha_piece:.3f}  mean S3/CGL={np.mean(s3s):.3e}  "
            f"max S3/CGL={np.max(s3s):.3e}"
        )
        # Covering: sum of piece sizes should = R if we took all cosets
        # Would the union bound on |W| give better than q^{2/3}?
        # If each piece has |W_i| << q^{2/3 - eps} and #pieces = q^{1-alpha},
        # total |W| << q^{1-alpha} * q^{2/3 - eps} — need 1-alpha+2/3-eps < 2/3 i.e. alpha > 1-eps: only trivial.


def run_q(q: int) -> None:
    rng = np.random.default_rng(0)
    F = Field(q)
    R = max(1, int(round(q ** (2 / 3))))
    print(f"\n=== q={q} N={F.N} R={R} ===")
    _, Wt, b, _ = tpm(F, np.ones(len(F.ns), dtype=complex), R, iters=30)

    print("  (H3) proposed MVT-beyond eta-test on ADV and flat at V=N^{5/7}:")
    print("    ADV b:")
    test_eta(F, b, 5 / 7, [0.0, 0.05, 0.1, 0.2, 0.5])
    print("    flat b:")
    test_eta(F, np.ones(len(F.ns), dtype=complex), 5 / 7, [0.0, 0.05, 0.1, 0.2, 0.5])

    # Also at a LOWER threshold where |W_crit| is nontrivial, to test eta meaningfully
    # Choose V so that ~R characters exceed it for ADV
    D = F.D(b)
    absD = np.abs(D)
    V_R = float(np.partition(absD, -R)[-R])
    print(f"  (H3b) same eta-test at V=V_(R)={V_R:.3e} (so |W|~R by construction) on ADV:")
    W = np.where(absD >= V_R * 0.999)[0]
    wb = F.w * b
    c2 = float(np.vdot(wb, wb).real)
    for eta in [0.0, 0.05, 0.1, 0.2, 0.5]:
        bound_eta = (q ** (1 - eta) + F.N) * c2 / V_R**2
        print(
            f"      eta={eta:.2f}: |W|={len(W)}  bound={bound_eta:.2e}  "
            f"|W|/bound={len(W)/bound_eta:.4f}  holds={len(W)<=bound_eta}"
        )

    amplify_slack(F, b, R, [1, 2, 3])
    subgroup_split(F, b, R, [1 / 3, 1 / 2, 2 / 3], rng)


def main(argv: list[str]) -> None:
    qs = [1009, 10007]
    if argv:
        qs = [int(x) for x in argv]
    for q0 in qs:
        run_q(int(nextprime(q0 - 1)))


if __name__ == "__main__":
    main(sys.argv[1:])
