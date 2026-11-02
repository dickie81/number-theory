# Uncertified: rank of cross-term blocks between dyadic blocks of the orbit Gram, and a common 4-dim junction.
import sys, numpy as np
sys.path.insert(0, 'scripts')
import ball_orbit as bo
G = np.array(bo.gram(511), dtype=float)
blocks = [np.arange(2**j, 2**(j+1)) - 1 for j in range(3, 9)]  # [8,16) ... [256,512)
def cand(idx):
    n = (idx + 1).astype(float)
    return np.stack([np.ones_like(n), n, np.sqrt(n), np.sqrt(n) * np.log(n), 1/np.sqrt(n), np.log(n)], 1)
U = {}
for a in range(len(blocks)):
    for b in range(a+1, len(blocks)):
        S, T = blocks[a], blocks[b]
        C = G[np.ix_(S, T)]
        s = np.linalg.svd(C, compute_uv=False)
        tail = np.sqrt((s[4:]**2).sum() / (s**2).sum())
        u = np.linalg.svd(C)[0][:, :4]
        U.setdefault(a, []).append(u)
        # residual after projecting out candidate directions on both sides (e1,e2 ~ 1,n; plus sqrt n, sqrt n log n)
        P = cand(S)[:, [0, 1, 2, 3]]; Q = cand(T)[:, [0, 1, 2, 3]]
        PS = P @ np.linalg.pinv(P); PT = Q @ np.linalg.pinv(Q)
        R = C - PS @ C @ PT
        print(f"[{S[0]+1},{S[-1]+2})x[{T[0]+1},{T[-1]+2}) s1={s[0]:.2e} s5/s1={s[4]/s[0]:.1e} "
              f"rank(1e-10)={np.sum(s > 1e-10*s[0])} tail4={tail:.1e} cand_resid={np.linalg.norm(R)/np.linalg.norm(C):.1e}")
# common subspace: principal angles between top-4 left subspaces of block 0 against different partners
us = U[0]
for i in range(1, len(us)):
    ang = np.degrees(np.arccos(np.clip(np.linalg.svd(us[0].T @ us[i], compute_uv=False), -1, 1)))
    print("block [8,16) top-4 vs partner", i, "max principal angle", f"{ang.max():.2e} deg")
