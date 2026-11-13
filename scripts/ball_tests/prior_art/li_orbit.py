"""Check the Li-orbit pivots: Gram matrix <G_n, G_m>_W = lam_n + lam_m - lam_{|n-m|} (Lagarias Thm 3.1, zeta case),
with Li coefficients from the Taylor coefficients of log xi at s = 1 (Cauchy integral on a circle)."""
import mpmath as mp

mp.mp.dps = 80

def xi(s):
    return mp.mpf(1) / 2 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)

M = 256
r = mp.mpf(1) / 2
vals = []
for j in range(M):
    th = 2 * mp.pi * j / M
    s = 1 + r * mp.e ** (1j * th)
    vals.append(mp.log(xi(s)))

K = 12
a = []
for k in range(K + 1):
    acc = mp.mpc(0)
    for j in range(M):
        th = 2 * mp.pi * j / M
        acc += vals[j] * mp.e ** (-1j * k * th)
    a.append((acc / M / r ** k).real)

def lam(n):
    if n == 0:
        return mp.mpf(0)
    return n * sum(mp.binomial(n - 1, j) * a[n - j] for j in range(n))

L = [lam(n) for n in range(0, 9)]
for n in range(1, 9):
    print("lambda_%d = %s" % (n, mp.nstr(L[n], 15)))
print("2*lambda_1 =", mp.nstr(2 * L[1], 20), " vs 2+gamma-log(4pi) =", mp.nstr(2 + mp.euler - mp.log(4 * mp.pi), 20))

N = 8
G = mp.matrix(N, N)
for i in range(1, N + 1):
    for j in range(1, N + 1):
        G[i - 1, j - 1] = L[i] + L[j] - L[abs(i - j)]

# LDL^T pivots
A = G.copy()
piv = []
for k in range(N):
    d = A[k, k]
    piv.append(d)
    for i in range(k + 1, N):
        f = A[i, k] / d
        for j in range(k + 1, N):
            A[i, j] -= f * A[k, j]
print("Li-orbit pivots:", [mp.nstr(p, 4) for p in piv])
print("pivot_2/pivot_1 =", mp.nstr(piv[1] / piv[0], 6))

# Hallouin-Perret style 2x2 check: d2 >= d1 iff |a| <= 2g sqrt(q-1)
for (g, q, a) in [(1, 4, -4), (1, 4, 4), (1, 9, 6), (1, 5, 4), (1, 5, 3)]:
    d1 = 2 * g
    d2 = 2 * g * q - a * a / (2 * g)
    print("g=%d q=%d trace=%d: d2/d1=%.4f, criterion |a|<=2g*sqrt(q-1): %s" % (g, q, a, d2 / d1, abs(a) <= 2 * g * (q - 1) ** 0.5))
