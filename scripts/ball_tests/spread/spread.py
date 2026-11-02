import sys, json, numpy as np, scipy.linalg as sl
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', '..')); import ball_orbit as bo
NMAX = int(sys.argv[1]); Ns = [n for n in [100,200,300,500,700,1000,1500,2000,3000,4000,6000] if n <= NMAX]
G = bo.gram(NMAX); d1 = G[0, 0]
def blocks(w, N):  # w indexed n=1..N
    J = int(np.log2(N))+1; return [float(w[2**j-1:min(2**(j+1)-1, N)].sum()) for j in range(J)]
res = {}
for N in Ns:
    g = G[:N, :N]; n = np.arange(1, N+1)
    wa, Va = sl.eigh(g, subset_by_index=[0, 4])
    M = d1*np.minimum.outer(n, n).astype(float)
    wb, Vb = sl.eigh(g, M, subset_by_index=[0, 4])
    A, B = [], []
    for i in range(5):
        v = Va[:, i]/np.linalg.norm(Va[:, i]); A.append(dict(lam=float(wa[i]), blocks=blocks(v**2, N), v=v.tolist()))
        u = np.cumsum(Vb[::-1, i])[::-1]; u = u/np.linalg.norm(u)  # u_k = sum_{n>=k} v_n, M-norm (up to d1)
        B.append(dict(lam=float(wb[i]), blocks=blocks(u**2, N), u=u.tolist()))
    res[N] = dict(a=A, b=B); print(N, 'done', flush=True)
json.dump(res, open(f'spread_{NMAX}.json', 'w'))
