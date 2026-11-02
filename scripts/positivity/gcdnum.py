import numpy as np, math
for N in [50,100,200,400,800]:
    i=np.arange(1,N+1); G=np.gcd.outer(i,i)/np.sqrt(np.outer(i,i))
    e=np.linalg.eigvalsh(G); print(N, f"lam_min={e[0]:.4g} lam_max={e[-1]:.4g} lam_max/logN={e[-1]/math.log(N):.3f} lam_min*N={e[0]*N:.3g}")
