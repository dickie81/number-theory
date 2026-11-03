# Uncertified: two spheres S+ / S- for the indefinite intersection form of BallWeil.selfInt.
# Coordinates (a, b, c_1..c_M); selfInt = 2ab + 2a Σc + 2b Σ n c_n + c^T I c, I_mn = m + n - G_mn (BallWeil.inter),
# G = ball_orbit.gram (prime side). Lean (BallPole.selfInt_decomp): selfInt = 2(D·e1)(D·e2) - Q(c_perp), so
# RH <=> full form has exactly ONE positive direction (the pole). S+ = positive eigenspace, S- = negative.
import sys, time, numpy as np
sys.path.insert(0, 'scripts'); import ball_orbit as bo
Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4095
Z = np.array([14.1347, 21.0220, 25.0109, 30.4249, 32.9351, 37.5862, 40.9187, 43.3271])
out = open('scripts/positivity/junction_twosphere_results.txt', 'a')
def P(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()
t0 = time.time(); G = np.array(bo.gram(Mmax), dtype=float); P(f"gram {Mmax} {time.time()-t0:.0f}s")
def inertia(H, tol=1e-9):
    w = np.linalg.eigvalsh(H); t = tol * abs(w).max()
    return int((w > t).sum()), int((w < -t).sum()), int((abs(w) <= t).sum()), w
def full(M):
    n = np.arange(1, M+1, dtype=float); I = n[:, None] + n[None, :] - G[:M, :M]
    F = np.zeros((M+2, M+2)); F[0, 1] = F[1, 0] = 1; F[0, 2:] = F[2:, 0] = 1; F[1, 2:] = F[2:, 1] = n; F[2:, 2:] = I
    return I, F
gs = np.arange(2, 60, 0.02)
def bestg(x, n):
    ln = np.log(n); one = np.ones_like(ln); best = (9, 0)
    for g in gs:
        B = np.stack([one, np.cos(g*ln), np.sin(g*ln)], 1)
        r = np.linalg.norm(x - B @ np.linalg.lstsq(B, x, rcond=None)[0]) / np.linalg.norm(x)
        if r < best[0]: best = (r, g)
    return best[1], best[0]
M = 255
while M <= Mmax:
    I, F = full(M); K = int(np.log2(M+1))
    blocks = [np.arange(2**a, min(2**(a+1), M+1)) for a in range(K)]
    P(f"\n=== M={M} ===")
    pF = inertia(F); pI = inertia(I); pG = inertia(G[:M, :M])
    P(f" full form (pole plane + c): (+,-,0)={pF[:3]}  max eig={pF[3].max():.3e}  2nd eig={np.sort(pF[3])[-2]:.3e}")
    P(f" c-only I=m+n-G: (+,-,0)={pI[:3]}   G: (+,-,0)={pG[:3]} min eig G={pG[3].min():.3e}")
    sp = sn = 0; V = []
    row = []
    for a, bl in enumerate(blocks):
        w, U = np.linalg.eigh(I[np.ix_(bl-1, bl-1)]); t = 1e-9*abs(w).max()
        Vp, Vn = U[:, w > t], U[:, w < -t]; V.append((Vp, Vn, w)); sp += Vp.shape[1]; sn += Vn.shape[1]
        row.append(f"[{bl[0]},{bl[-1]}]:+{Vp.shape[1]}/-{Vn.shape[1]}")
    P(" block inertia of I: " + " ".join(row))
    P(f" sum of block (+) = {sp}  vs global I (+) = {pI[0]}  -> junction changes + index by {pI[0]-sp}")
    # junction S+ of block a against S- of block a+1 (and S- of a vs S+ of a+1), top two blocks
    a, b = K-2, K-1; A, B = blocks[a], blocks[b]; Iab = I[np.ix_(A-1, B-1)]
    for lab, L, R in (("S+(a) x S-(a+1)", V[a][0], V[b][1]), ("S-(a) x S+(a+1)", V[a][1], V[b][0]), ("S-(a) x S-(a+1)", V[a][1], V[b][1])):
        if L.shape[1] == 0 or R.shape[1] == 0: P(f" {lab}: empty"); continue
        C = L.T @ Iab @ R; u, s, vt = np.linalg.svd(C); f = np.cumsum(s**2)/(s**2).sum()
        P(f" {lab} dims {C.shape}: ||C||={np.linalg.norm(C):.3e} k95={int(np.searchsorted(f,.95)+1)} k99={int(np.searchsorted(f,.99)+1)} s/s1: " + " ".join(f"{x:.3f}" for x in s[:10]/s[0]))
        for i in range(min(4, len(s))):
            gl, rl = bestg(L @ u[:, i], A.astype(float)); gr, rr = bestg(R @ vt[i], B.astype(float))
            P(f"    dir{i+1}: left g={gl:.2f} r={rl:.2f} | right g={gr:.2f} r={rr:.2f}")
    # 45-degree null-cone test: top S+ of block a with top-|eig| S- of block b, w = (v+ ± v-)/sqrt2
    wa, wb = V[a][2], V[b][2]
    if V[a][0].shape[1]:
        vp = np.zeros(M); vp[A-1] = V[a][0][:, -1]
        for j in (0, 1, 2):
            vn = np.zeros(M); vn[B-1] = V[b][1][:, j]
            qp, qn, x = vp@I@vp, vn@I@vn, vp@I@vn
            for sg in (1, -1):
                w = (vp + sg*vn)/np.sqrt(2); P(f" null cone S+top(a)±S-[{j}](a+1) sign {sg:+d}: Q+={qp:.3e} Q-={qn:.3e} cross={x:.3e} Q(w)={w@I@w:.3e}")
    M = 2*M + 1
