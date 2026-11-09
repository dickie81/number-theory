#!/usr/bin/env python3
"""Discrete probe of CGL Prop. 8.1 J(f) at prime q, with exact GCD-weight expansion.

At prime q, (L,q)∈{1,q}. For fixed b (single channel; multi-b noted as extra φ(q)):
  S_a(u) = sum_m f((m1 u+m3)/m2) * (a m1 + b m2 + m3, q)
         = A(u) + (q-1) H_a(u)
  where A = sum_all_m f(affine), H_a = sum_{m: a m1+b m2+m3 ≡ 0 (mod q)} f(affine).

For M < q (so m1 ≠ 0 mod q always) there is exactly one a per triple with the congruence,
hence sum_a H_a = A, and
  sum_{a=1}^{q-1} S_a(u)^2 = 3(q-1) A(u)^2 + (q-1)^2 sum_a H_a(u)^2.

J_disc = int sum_a S_a^2 du   (sup over M_i absorbed by fixing M_i=M).

CGL Prop. 8.1 bound (one b-channel, φ(q)~q):
  T1 = q M^6 (int f)^2 ,  T2 = q^2 M^4 int f^2.

Extremisers tested: random sparse, rational bumps r/s, flat.
Also report the split: J_A = int 3(q-1)A^2 , J_H = int (q-1)^2 sum_a H_a^2.

Label: Numerical. Proxy limitations documented in the Batch-5 writeup.
"""
from __future__ import annotations

import sys
from collections import defaultdict
from dataclasses import dataclass

import numpy as np
from sympy import nextprime


@dataclass
class Result:
    q: int
    M: int
    kind: str
    J: float
    J_A: float
    J_H: float
    T1: float
    T2: float
    ratio: float
    mass: float
    mass2: float
    ntrip: int


def grid_u(G: int) -> np.ndarray:
    return np.linspace(0.5, 2.0, G)


def make_f(kind: str, u: np.ndarray, G: int, M: int, rng: np.random.Generator) -> np.ndarray:
    if kind == "random":
        mu = min(0.25, 80.0 / G)
        return (rng.random(G) < mu).astype(float)
    if kind == "rational":
        B = max(3, int(round(M**0.5)) + 2)
        width = max(1.5 / G * 2, 0.01)
        f = np.zeros(G)
        for s in range(1, B + 1):
            for r in range(1, 2 * B + 1):
                x = r / s
                if 0.5 <= x <= 2.0:
                    f += np.exp(-0.5 * ((u - x) / width) ** 2)
        return f
    if kind == "flat":
        return np.ones(G)
    raise ValueError(kind)


def triples(M: int, max_triples: int, rng: np.random.Generator):
    ms = np.arange(M, 2 * M, dtype=np.int64)
    n = len(ms)
    ntrip = n**3
    if ntrip <= max_triples:
        m1 = np.repeat(ms, n * n)
        m2 = np.tile(np.repeat(ms, n), n)
        m3 = np.tile(ms, n * n)
        scale = 1.0
    else:
        idx = rng.integers(0, n, size=(max_triples, 3))
        m1, m2, m3 = ms[idx[:, 0]], ms[idx[:, 1]], ms[idx[:, 2]]
        scale = ntrip / max_triples
        ntrip = max_triples  # sampled count; scale restores full
    return m1, m2, m3, scale, int(n**3)


def compute_J(
    q: int,
    M: int,
    f: np.ndarray,
    u: np.ndarray,
    b: int,
    max_triples: int,
    rng: np.random.Generator,
) -> tuple[float, float, float, int]:
    """Return (J, J_A, J_H, ntrip_full)."""
    m1, m2, m3, scale, ntrip_full = triples(M, max_triples, rng)
    G = len(u)
    du = 1.5 / G
    # A(u) = scale * sum_sampled f((m1 u+m3)/m2)
    A = np.zeros(G)
    # For H: group triples by the unique a = -m1^{-1}(b m2 + m3) mod q
    # Accumulate H_a on the grid for each a that appears.
    # Memory: store dict a -> accumulator, or one big array of size q.
    H = np.zeros((q, G))  # H[a] for a=0..q-1; a=0 unused for m1 invertible
    for i in range(len(m1)):
        mm1, mm2, mm3 = int(m1[i]), int(m2[i]), int(m3[i])
        target = (mm1 * u + mm3) / mm2
        vals = np.interp(target, u, f, left=0.0, right=0.0)
        A += vals
        # a * mm1 + b * mm2 + mm3 ≡ 0 mod q  => a ≡ -mm1^{-1}(b*mm2+mm3) mod q
        inv = pow(mm1 % q, -1, q)
        a = (-inv * ((b * mm2 + mm3) % q)) % q
        if a != 0:
            H[a] += vals
    A *= scale
    H *= scale
    # sum_a H_a should ≈ A (check)
    # J pieces
    JA = float(np.sum(3 * (q - 1) * A**2) * du)
    # sum over a=1..q-1 of H_a^2
    H2 = np.sum(H[1:] ** 2, axis=0)
    JH = float(np.sum((q - 1) ** 2 * H2) * du)
    return JA + JH, JA, JH, ntrip_full


def run_one(q, M, kind, G, max_triples, rng) -> Result:
    u = grid_u(G)
    f = make_f(kind, u, G, M, rng)
    du = 1.5 / G
    mass = float(np.sum(f) * du)
    mass2 = float(np.sum(f**2) * du)
    b = 1  # single channel
    J, JA, JH, ntrip = compute_J(q, M, f, u, b, max_triples, rng)
    T1 = q * (M**6) * mass**2
    T2 = (q**2) * (M**4) * mass2
    ratio = J / (T1 + T2) if (T1 + T2) > 0 else float("nan")
    return Result(q, M, kind, J, JA, JH, T1, T2, ratio, mass, mass2, ntrip)


def fit(results: list[Result]) -> None:
    by = defaultdict(list)
    for r in results:
        by[r.kind].append(r)
    print("\n=== fit log(J)~a+b log q ; log(T1+T2)~c+d log q ; saving=d-b ===")
    for kind, rs in sorted(by.items()):
        if len(rs) < 3:
            continue
        qs = np.log([r.q for r in rs])
        Js = np.log([max(r.J, 1e-300) for r in rs])
        Ts = np.log([max(r.T1 + r.T2, 1e-300) for r in rs])
        bJ, aJ = np.polyfit(qs, Js, 1)
        bT, aT = np.polyfit(qs, Ts, 1)
        seJ = float(np.std(Js - (aJ + bJ * qs)) / np.sqrt(np.sum((qs - qs.mean()) ** 2)))
        seT = float(np.std(Ts - (aT + bT * qs)) / np.sqrt(np.sum((qs - qs.mean()) ** 2)))
        saving = bT - bJ
        se = (seJ**2 + seT**2) ** 0.5
        print(
            f"  {kind:8s}: slope_J={bJ:.3f}±{seJ:.3f}  slope_bound={bT:.3f}±{seT:.3f}  "
            f"apparent_saving={saving:.3f}±{se:.3f}"
        )
        print(
            "           ratios: "
            + ", ".join(f"q={r.q}:{r.ratio:.3e}(JA/J={r.J_A/r.J:.2f})" for r in rs)
        )


def main(argv: list[str]) -> None:
    qs = [int(nextprime(n)) for n in (101, 211, 503, 1009, 2003, 3001)]
    if argv:
        qs = [int(nextprime(int(x) - 1)) for x in argv]
    rng = np.random.default_rng(1)
    G = 128
    max_triples = 4000  # MC when M^3 larger
    results = []
    print(f"G={G} max_triples={max_triples}  exact prime-q GCD expansion, single b=1")
    print("CGL T1=q M^6 mass^2, T2=q^2 M^4 mass2. Label: Numerical.\n")
    for q in qs:
        M = max(2, min(8, int(round(q ** (2 / 9)))))
        for kind in ("random", "rational", "flat"):
            r = run_one(q, M, kind, G, max_triples, rng)
            results.append(r)
            print(
                f"q={q:5d} M={M} {kind:8s}  J={r.J:.3e} JA={r.J_A:.3e} JH={r.J_H:.3e}  "
                f"T1+T2={r.T1+r.T2:.3e}  J/(T1+T2)={r.ratio:.3e}  "
                f"JH/JA={r.J_H/max(r.J_A,1e-300):.2f}  ntrip={r.ntrip}"
            )
    fit(results)


if __name__ == "__main__":
    main(sys.argv[1:])
