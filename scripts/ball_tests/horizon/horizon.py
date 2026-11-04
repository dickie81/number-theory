import sys, json, numpy as np, scipy.linalg as sl
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', '..')); import ball_orbit as bo
Ns = [10,20,50,100,200,300,500,700,1000,1500,2000,2500,3000]
G3 = bo.gram(3000); out = []
for N in Ns:
    G = G3[:N,:N]; d1 = G[0,0]
    w, V = np.linalg.eigh(G)
    Dm = 1/np.sqrt(np.diag(G)); C = G*Dm[:,None]*Dm[None,:]
    wc = np.linalg.eigvalsh(C)[0]
    m = np.arange(1, N+1); F = d1*np.minimum.outer(m, m).astype(float)
    wg, Vg = sl.eigh(G, F, subset_by_index=[0,0])
    out.append(dict(N=N, lam=w[0], lam_d1=w[0]/d1, lam_max=w[-1], corr=wc, gen=wg[0], v=V[:,0].tolist(), vg=Vg[:,0].tolist()))
    print(N, '%.4e %.4e %.4e corr %.4e gen %.5f' % (w[0], w[0]/d1, w[-1], wc, wg[0]))
json.dump(out, open('zeta_eigs.json','w'))
