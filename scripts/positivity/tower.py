# Uncertified: excess positivity eps_N = -lambda_min(G_N) of the orbit Gram, and normalised variants.
import sys, numpy as np
sys.path.insert(0, 'scripts')
import ball_orbit as bo
Ns = [10, 25, 50, 100, 200, 300, 400]
G = np.array(bo.gram(max(Ns)), dtype=float)
for N in Ns:
    ev = np.linalg.eigvalsh(G[:N, :N])
    eps = -ev[0]
    tr = ev.sum() / N
    print(f"N={N:4d} eps_N={eps:+.3e} eps_N*N={eps*N:+.3e} eps/trace={eps/tr:+.3e} "
          f"neg_frac={np.mean(ev < -1e-9):.3f} lam_max={ev[-1]:.3e}")
# Non-nested dyadic blocks [N, 2N): per-block excess, and the gluing cross-term norm against block minima.
for N in [8, 16, 32, 64, 128]:
    B1 = G[N-1:2*N-1, N-1:2*N-1]; B2 = G[2*N-1:4*N-1, 2*N-1:4*N-1]; C = G[N-1:2*N-1, 2*N-1:4*N-1]
    e1, e2 = np.linalg.eigvalsh(B1)[0], np.linalg.eigvalsh(B2)[0]
    print(f"block N={N:4d} eps=[{-e1:+.3e},{-e2:+.3e}] cross_norm={np.linalg.norm(C,2):.3e} "
          f"glue_ok={np.linalg.norm(C,2)**2 <= e1*e2}")
