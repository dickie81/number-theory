import math, sys
import numpy as np
HERE = sys.path[0]
gam = np.load(f"{HERE}/zeros_3000.npy")
G1, G2 = gam[0], gam[1]
# Q6: room in 3D
p = lambda n: math.sqrt(2 * n) * np.array([math.cos(G1 * math.log(n)) / math.hypot(.5, G1),
                                            math.sin(G1 * math.log(n)) / math.hypot(.5, G1),
                                            math.cos(G2 * math.log(n)) / math.hypot(.5, G2)])
P3 = np.array([p(1), p(2), p(3)])
print(f"Q6: det[p1, p2, p3] = {np.linalg.det(P3):.4f} (nonzero: the first three integers already fill the slice)")
# Q5: prime visibility vs dimensions
N = 1000
isp = np.ones(N + 1, bool); isp[:2] = False
for q in range(2, 32):
    if isp[q]: isp[q * q::q] = False
pp = np.zeros(N + 1, bool)
for q in np.nonzero(isp)[0]:
    r = q
    while r <= N: pp[r] = True; r *= q
def auc(score, lab):
    a, b = score[lab], score[~lab]
    return (np.sum(a[:, None] > b[None, :]) + 0.5 * np.sum(a[:, None] == b[None, :])) / (len(a) * len(b))
m = np.arange(2, N + 1); lm = np.log(m)
print(f"\nQ5: AUC for picking out prime powers, by the number of zeros K seen (2K real dimensions)")
print(f"{'K':>5} {'dims':>5} {'height':>7} {'M=30':>6} {'M=100':>6} {'M=1000':>7}")
for K in (1, 2, 3, 5, 10, 20, 50, 100, 300, 1000, 2999):
    g = gam[:K]; w = 1 - g / gam[K]
    S = -(w[None, :] * np.cos(np.outer(lm, g))).sum(1)
    row = [auc(S[m <= M], pp[2:][m <= M]) for M in (30, 100, 1000)]
    print(f"{K:5d} {2 * K:5d} {g[-1]:7.1f} " + " ".join(f"{a:6.3f}" for a in row))
