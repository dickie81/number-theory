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

# ---- Different hyperplanes: joint best common junction over all pairs (uncertified) ----
def primefactors(x):
    out, d = [], 2
    while d * d <= x:
        if x % d == 0:
            out.append(d)
            while x % d == 0: x //= d
        d += 1
    if x > 1: out.append(x)
    return out
def J_capture(H, labels, ks=(1, 4, 8, 16)):
    """Off-block-diagonal part J of H; fraction of ‖J‖_F² captured by its best rank-k (common) junction."""
    same = labels[:, None] == labels[None, :]
    J = np.where(same, 0.0, H)
    s = np.linalg.svd(J, compute_uv=False)
    f = np.cumsum(s**2) / (s**2).sum()
    k95 = int(np.searchsorted(f, 0.95) + 1)
    return [f[k-1] for k in ks], k95, len(set(labels))
def families(M):
    n = np.arange(1, M + 1)
    P = np.array([max(primefactors(int(x))) if x > 1 else 1 for x in n])
    v2 = np.array([(int(x) & -int(x)).bit_length() - 1 for x in n])
    return {
        "dyadic": np.floor(np.log2(n)).astype(int),
        "triadic": np.floor(np.log(n) / np.log(3) + 1e-12).astype(int),
        "largest prime P(n)": np.where(P <= 13, P, 100 + np.floor(np.log2(np.maximum(P, 1))).astype(int)),
        "residue n mod 5": n % 5,
        "2-adic n=2^v·odd": v2,
        "7-smooth / rough": (P <= 7).astype(int),
    }
def mellin(M):
    t = np.log(np.arange(1, M + 1)); L = t[-1]
    F = np.stack([np.cos(np.pi * f * t / L) for f in range(M)], 1)
    Q, _ = np.linalg.qr(F)
    return Q
print("\nfamily | basis | capture k=1,4,8,16 | k for 95% | #blocks")
for M in (255, 511):
    H0 = G[:M, :M]
    bases = {"orbit Gram": H0, "dual G^-1": np.linalg.inv(H0)}
    Q = mellin(M); bases["Mellin (freq. blocks)"] = Q.T @ H0 @ Q
    for fam, lab in families(M).items():
        for bn, H in bases.items():
            if bn.startswith("Mellin"):
                if fam != "dyadic": continue
                lab2 = np.floor(np.log2(np.arange(1, M + 1))).astype(int)  # dyadic frequency bands
            else:
                lab2 = lab
            cap, k95, nb = J_capture(H, lab2)
            print(f"M={M} | {fam} | {bn} | " + ", ".join(f"{c:.3f}" for c in cap) + f" | {k95} | {nb}")
