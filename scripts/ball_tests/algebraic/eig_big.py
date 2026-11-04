import sys, json, numpy as np, scipy.linalg as sl
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', '..')); import ball_orbit as bo
NM = int(sys.argv[1]); Ns = [n for n in [300,500,700,1000,1400,2000,2800,4000,5600,8000] if n <= NM]
G = bo.gram(NM); out = {}
for N in Ns:
    g = G[:N, :N]; w, V = sl.eigh(g, subset_by_index=[0, 1]); v = V[:, 0]; v = v/v[0]
    r = np.linalg.norm(g@V[:, 0]-w[0]*V[:, 0]); gap = w[1]-w[0]
    out[N] = dict(lam=w[0], lam2=w[1], resid=r, angle_bound=r/gap, f=(v*np.arange(1, N+1))[:400].tolist())
    print(N, 'lam %.4e gap %.3e resid %.2e angle<=%.1e f2..5' % (w[0], gap, r, r/gap), np.round(out[N]['f'][1:5], 5), flush=True)
json.dump(out, open('eig_big.json', 'w'))
