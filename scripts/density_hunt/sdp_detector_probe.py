#!/usr/bin/env python3
"""Batch 7 sdp_detector cheap probe: nonnegative short weights vs flat max|D|.

Not a real SDP certificate. Label: Numerical. Null result (opt does not beat flat).
"""
import numpy as np
from sympy import nextprime, primitive_root


def probe(q: int, K: int = 7, steps: int = 300) -> tuple[float, float, float]:
    g = int(primitive_root(q))
    ind = {}
    a = 1
    for j in range(q - 1):
        ind[a] = j
        a = a * g % q
    ns, jn = [], []
    for n in range(1, K + 1):
        if np.gcd(n, q) == 1:
            ns.append(n)
            jn.append(ind[n])
    jn = np.array(jn)
    N = len(jn)
    A = np.zeros(q - 1, dtype=complex)
    A[jn] = 1.0
    D = np.abs(np.fft.fft(A))
    D[0] = 0.0
    flat = float(D.max() / N)
    w = np.ones(N, dtype=float)
    for _ in range(steps):
        A = np.zeros(q - 1, dtype=complex)
        A[jn] = w
        Df = np.fft.fft(A)
        absD = np.abs(Df)
        absD[0] = 0.0
        i = int(np.argmax(absD))
        phase = Df[i] / max(absD[i], 1e-300)
        chi = np.exp(-2j * np.pi * i * jn / (q - 1))
        grad = np.real(np.conjugate(phase) * chi)
        w = np.maximum(w - 0.1 * grad, 0.0)
        s = float(w.sum())
        if s <= 0:
            w[:] = 1.0
            s = float(N)
        w *= N / s
    A = np.zeros(q - 1, dtype=complex)
    A[jn] = w
    D = np.abs(np.fft.fft(A))
    D[0] = 0.0
    opt = float(D.max() / N)
    return flat, opt, opt / flat


if __name__ == "__main__":
    for q0 in [100, 500, 1000, 3000]:
        q = int(nextprime(q0))
        flat, opt, r = probe(q)
        print(f"q={q}: flat={flat:.4f} opt={opt:.4f} opt/flat={r:.4f}")
