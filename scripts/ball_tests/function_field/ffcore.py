"""Function-field analogue of the orbit-lattice Gram matrix of docs/ball-conjecture.md.

Curve C/F_q, genus g, L-poly P(T)=prod_j (1-alpha_j T), alpha_j = sqrt(q) e^{i theta_j}.
Zeros of zeta_C(s)=Z(C,q^-s) on Re s=1/2: rho = 1/2 + i gamma, gamma = (theta_j + 2 pi k)/log q, k in Z (infinitely many).
Faithful kernel:  K(r) = sum_rho r^{rho-1/2} / (rho(1-rho)),  rho(1-rho) = 1/4 + gamma^2.
Poisson summation gives the exact closed form (u = log r, L = log q, s_m = sum_j alpha_j^m, s_0 = 2g, s_{-m}=q^{-m}s_m):
  K(r) = L * sum_{m in Z} (s_m / q^{m/2}) e^{-|u - mL|/2}.
Gram G(m,n) = sqrt(mn) K(m/n); for m >= n with j0 = max{j : q^j <= m/n}:
  G(m,n)/L = n*(T + sum_{j=0}^{j0} s_j) + m*(T - sum_{j=1}^{j0} s_j/q^j),  T = sum_{m>=1} s_m/q^m = -(x P'(x)/P(x))|_{x=1/q}.
All entries are rational multiples of L, so d_k/d_1 is independent of L. With no zeros except the j=0 'density' term,
G = 2gL*min(m,n): the flat model (sqrt(mn) e^{-|log(m/n)|/2} = min(m,n)).
"""
from fractions import Fraction as F
import mpmath as mp
import numpy as np

def power_sums(Pc, q, M):
    """Pc: integer coeffs [1,c1,...,c2g] of P(T)=prod(1-a_j T). returns s_0..s_M (s_m = sum a_j^m) exact ints."""
    deg = len(Pc)-1
    # e_k = (-1)^k c_k ; Newton: s_m = sum_{k=1}^{m-1}(-1)^{k-1} e_k s_{m-k} + (-1)^{m-1} m e_m
    e = [(-1)**k*Pc[k] for k in range(deg+1)]
    s = [deg]
    for m in range(1, M+1):
        v = sum((-1)**(k-1)*e[k]*s[m-k] for k in range(1, min(m, deg+1)) if k <= deg)
        if m <= deg: v += (-1)**(m-1)*m*e[m]
        s.append(v)
    return s

def Tval(Pc, q):
    x = F(1, q)
    P = sum(F(c)*x**i for i, c in enumerate(Pc))
    dP = sum(F(i*c)*x**(i-1) for i, c in enumerate(Pc) if i)
    return -x*dP/P

def gram(Pc, q, N, ctx=mp):
    """G/L as mp matrix (object ndarray of mpf), N x N, indices n=1..N."""
    T = Tval(Pc, q)
    J = 0
    while q**(J+1) <= N: J += 1
    s = power_sums(Pc, q, J)
    A = [T + sum(s[:j+1]) for j in range(J+1)]
    B = [T - sum(F(s[i], q**i) for i in range(1, j+1)) for j in range(J+1)]
    Am = [mp.mpf(a.numerator)/a.denominator for a in A]; Bm = [mp.mpf(b.numerator)/b.denominator for b in B]
    G = np.empty((N, N), dtype=object)
    for m in range(1, N+1):
        for n in range(1, m+1):
            j0 = 0
            while q**(j0+1)*n <= m: j0 += 1
            G[m-1, n-1] = G[n-1, m-1] = n*Am[j0] + m*Bm[j0]
    return G

def pivots(G):
    """LDL pivots d_k (Gram-Schmidt squared norms) of a real symmetric or complex Hermitian object-array mp matrix.
    The one LDL routine of scripts/ball_tests: dirichlet/dcore.py and zeta_mp.py import it."""
    A = G.copy(); N = A.shape[0]; d = []
    for k in range(N):
        p = mp.re(A[k, k]); d.append(p)
        if p <= 0:
            d += [mp.mpf('nan')]*(N-k-1); break
        col = A[k+1:, k] / p
        A[k+1:, k+1:] = A[k+1:, k+1:] - np.outer(col, A[k, k+1:])
    return d
