# Uncertified: the de Sitter tower from the prime side. (i) signature of the glued Lorentzian form -selfInt with
# cosh(k log 2) block scaling; (ii) time evolution u = log x of the prime-side kernel K_H(e^u): matrix-pencil modes
# e^{s u}, s = (beta - 1/2) + i gamma; Re s measures beta - 1/2 from primes alone.
import sys, numpy as np
sys.path.insert(0, 'scripts'); import ball_orbit as bo
out = open('scripts/positivity/desitter_results.txt', 'w')
def P(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()
Z = np.array([14.1347, 21.0220, 25.0109, 30.4249, 32.9351, 37.5862, 40.9187, 43.3271, 48.0052, 49.7738])
G = np.array(bo.gram(2047), dtype=float)
P("(i) glued form -selfInt on (a,b,c), blocks scaled by cosh(k log2) (a congruence)")
for M in (255, 511, 1023, 2047):
    n = np.arange(1, M+1, dtype=float); F = np.zeros((M+2, M+2)); F[0, 1] = F[1, 0] = 1
    F[0, 2:] = F[2:, 0] = 1; F[1, 2:] = F[2:, 1] = n; F[2:, 2:] = n[:, None] + n[None, :] - G[:M, :M]; F = -F
    k = np.floor(np.log2(n)); D = np.diag(np.r_[1, 1, np.cosh(k*np.log(2))]); w = np.linalg.eigvalsh(D @ F @ D)
    P(f" M={M}: negative {int((w<0).sum())}, positive {int((w>0).sum())}, smallest |eig| {abs(w).min():.2e}, eig nearest 0 from above {w[w>0].min():.2e}")
P("\n(ii) matrix pencil on K_H(e^u), u in [u0, log X]")
for X in (10**4, 10**5, 10**6):
    A, B = bo.tables(X+2); u = np.linspace(np.log(20), np.log(X), 1200); x = np.exp(u)
    K = np.sqrt(x) * bo.kernel_over_sqrt(x, A, B); du = u[1]-u[0]
    L = 500; H = np.lib.stride_tricks.sliding_window_view(K, L+1)  # Hankel rows
    Y0, Y1 = H[:, :-1].T, H[:, 1:].T
    U, s, Vt = np.linalg.svd(Y0, full_matrices=False); r = 40
    Ur, sr, Vr = U[:, :r], s[:r], Vt[:r].T
    z = np.linalg.eigvals(np.diag(1/sr) @ Ur.T @ Y1 @ Vr); S = np.log(z.astype(complex))/du
    S = S[(S.imag > 5) & (S.imag < 52)]; S = S[np.argsort(S.imag)]
    P(f" X={X:.0e}: resolution 2pi/(log X - log 20) = {2*np.pi/(np.log(X)-np.log(20)):.2f}")
    for sj in S:
        zj = Z[np.argmin(abs(Z - sj.imag))]
        P(f"   gamma={sj.imag:7.3f} (nearest zero {zj:.4f}, diff {sj.imag-zj:+.3f})   Re s = beta-1/2 = {sj.real:+.4f}")
