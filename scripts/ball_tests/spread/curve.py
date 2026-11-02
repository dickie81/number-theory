import sys, json, numpy as np, scipy.linalg as sl, mpmath as mp
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'function_field')); import ffcore
Gc = np.array(ffcore.gram([1, 2, 13], 13, 400), dtype=float); d1 = Gc[0, 0]; out = {}
def blocks(w, N):
    J = int(np.log2(N))+1; return [float(w[2**j-1:min(2**(j+1)-1, N)].sum()) for j in range(J)]
for N in [100, 150, 168, 169, 200, 300, 400]:
    g = Gc[:N, :N]; n = np.arange(1, N+1)
    w, V = np.linalg.eigh(g); v = V[:, 0]
    M = d1*np.minimum.outer(n, n).astype(float); wb, Vb = sl.eigh(g, M, subset_by_index=[0, 0])
    u = np.cumsum(Vb[::-1, 0])[::-1]; u /= np.linalg.norm(u)
    out[N] = dict(lam=float(w[0]), blocks_a=blocks(v**2, N), top=(np.argsort(-abs(v))[:5]+1).tolist(), v=v.tolist(), blocks_b=blocks(u**2, N), u=u.tolist())
    print(N, '%.2e' % w[0], 'top n', out[N]['top'], 'blocks_a', np.round(out[N]['blocks_a'], 3).tolist())
json.dump(out, open('curve.json', 'w'))
