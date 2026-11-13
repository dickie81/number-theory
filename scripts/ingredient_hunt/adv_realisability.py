#!/usr/bin/env python3
"""ADV realisability vs detector-structured coefficients (Ingredient I loophole).

Compare, at prime q with N=q^{7/9}, R=q^{2/3}, V_crit=N^{5/7}:
  (1) unrestricted tpm-ADV (complex b, no |b_n|<=1)
  (2) tpm projected to |b_n|<=1 (renormalised)
  (3) detector-like b:
        - interval / block (b=1 on [N,2N] with smooth weight)  [CGL T=1 reduction]
        - mobius on [N,2N]
        - liouville
        - zero-detector a_n = sum_{d|n, d<=X} mu(d) with X=N^eps or X=sqrt(N)
        - primes indicator
  For each: sharp_mvt = sum_W |D|^2 / ((q+N)||wb||_2^2) at top-R,
             |W|/Wbound_mvt, |W_crit| at V=N^{5/7},
             and correlation of b_ADV with structured families (max |<b,b_struct>|).

If (3) never approaches ADV's MVT-saturation while (1) does, ADV is NOT a
realisable saturator for the zero-detection LV problem — loophole toward
restricted-coefficient LV.

Reuses scripts/cgl_s3/probe.Field and tpm.
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from sympy import factorint, mobius, nextprime

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "cgl_s3"))
from probe import Field, tpm  # noqa: E402

SIGMA = 5 / 7


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
        sumW=sumW, c2=c2, Vmin=Vmin, sharp_mvt=sharp, W=R,
        Wbound_mvt=Wbound,
        W_over_bound=(R / Wbound if Wbound > 0 else 0.0),
    )


def W_crit(F: Field, b: np.ndarray, sigma: float = SIGMA) -> int:
    D = F.D(b)
    V = F.N ** sigma
    # scale: compare |D| to V * ||w b||_2 / something? Use absolute: |D| >= V * ||wb||_2 / sqrt(N)
    # Honest: CGL large value is |sum b_n chi(n)| >= V with ||b|| roughly controlled.
    # Match density_hunt/mvt_s3_coexist: V = N^sigma relative to unit-coeff scale.
    wb_norm = np.linalg.norm(F.w * b)
    if wb_norm <= 0:
        return 0
    # Normalise so ||w b||_2 = sqrt(sum w^2) ~ as for b=1; then threshold V
    scale = np.linalg.norm(F.w) / wb_norm
    return int(np.sum(np.abs(D) * scale >= V))


def structured_b(F: Field, kind: str, X: int | None = None) -> np.ndarray:
    ns = F.ns
    if kind == "interval":
        return np.ones(len(ns), dtype=complex)
    if kind == "mobius":
        return np.array([complex(mobius(int(n))) for n in ns])
    if kind == "liouville":
        out = []
        for n in ns:
            Om = sum(factorint(int(n)).values())
            out.append(complex((-1) ** Om))
        return np.array(out)
    if kind == "primes":
        out = []
        for n in ns:
            fac = factorint(int(n))
            out.append(1.0 + 0j if len(fac) == 1 and list(fac.values())[0] == 1 else 0.0)
        return np.array(out)
    if kind == "detector":
        # a_n = sum_{d|n, d<=X} mu(d)
        if X is None:
            X = max(2, int(F.N ** 0.05))  # CGL-like short X=(qT)^eps proxy
        out = np.zeros(len(ns), dtype=complex)
        for i, n in enumerate(ns):
            s = 0
            nn = int(n)
            # divisors up to X
            d = 1
            while d * d <= nn:
                if nn % d == 0:
                    if d <= X:
                        s += mobius(d)
                    other = nn // d
                    if other != d and other <= X:
                        s += mobius(other)
                d += 1
            out[i] = complex(s)
        return out
    if kind == "detector_sqrt":
        return structured_b(F, "detector", X=max(2, int(F.N ** 0.5)))
    raise ValueError(kind)


def corr(b, b2) -> float:
    b = b / (np.linalg.norm(b) + 1e-300)
    b2 = b2 / (np.linalg.norm(b2) + 1e-300)
    return float(abs(np.vdot(b2, b)))


def run_q(q0: int, tpm_iters: int = 40) -> None:
    q = int(nextprime(q0 - 1)) if q0 > 2 else 3
    # ensure prime
    from sympy import isprime
    if not isprime(q0):
        q = int(nextprime(q0))
    else:
        q = q0
    F = Field(q)
    R = max(1, int(round(q ** (2 / 3))))
    print(f"\n=== q={q} N={F.N} R={R} V_crit=N^{{5/7}}={F.N**SIGMA:.4e} ===")

    # ADV tpm from flat start
    val, Wadv, badv, it = tpm(F, np.ones(len(F.ns), dtype=complex), R, iters=tpm_iters)
    st = mvt_stats(F, badv, Wadv)
    wc = W_crit(F, badv)
    print(f"  ADV(tpm)     sharp={st['sharp_mvt']:.4f}  W/Wb={st['W_over_bound']:.4f}  "
          f"|W_crit|={wc:5d}  s1^2/q={val/q:.4f}  iters={it}")

    # Project ADV to |b_n|<=1 then renorm
    bproj = badv / (np.max(np.abs(badv)) + 1e-300)
    # re-select W as top-R of D(bproj)
    D = F.D(bproj)
    Wp = np.argpartition(np.abs(D) ** 2, -R)[-R:]
    st = mvt_stats(F, bproj, Wp)
    wc = W_crit(F, bproj)
    print(f"  ADV|b|<=1    sharp={st['sharp_mvt']:.4f}  W/Wb={st['W_over_bound']:.4f}  "
          f"|W_crit|={wc:5d}  corr(ADV)={corr(badv,bproj):.4f}")

    kinds = [
        ("interval", None),
        ("mobius", None),
        ("liouville", None),
        ("primes", None),
        ("detector", max(2, int(F.N ** 0.05))),
        ("detector_sqrt", None),
    ]
    for kind, X in kinds:
        if kind == "detector":
            b = structured_b(F, "detector", X=X)
            label = f"det X=N^0.05"
        elif kind == "detector_sqrt":
            b = structured_b(F, "detector_sqrt")
            label = "det X=N^1/2"
        else:
            b = structured_b(F, kind)
            label = kind
        if np.linalg.norm(b) < 1e-12:
            print(f"  {label:14s} ZERO vector — skip")
            continue
        D = F.D(b)
        W = np.argpartition(np.abs(D) ** 2, -R)[-R:]
        st = mvt_stats(F, b, W)
        wc = W_crit(F, b)
        print(f"  {label:14s} sharp={st['sharp_mvt']:.4f}  W/Wb={st['W_over_bound']:.4f}  "
              f"|W_crit|={wc:5d}  corr(ADV)={corr(badv,b):.4f}")


def main():
    qs = [503, 1009, 2003, 5003]
    if len(sys.argv) > 1:
        qs = [int(a) for a in sys.argv[1:]]
    for q in qs:
        run_q(q)


if __name__ == "__main__":
    main()
