import sys, numpy as np, math
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', '..')); import ball_orbit as bo
G = bo.gram(6000); d1 = G[0, 0]
import mpmath as mp
S4 = None
print('d1 =', d1, ' 2+gamma-log4pi =', 2+0.5772156649015329-math.log(4*math.pi))
for N in [100, 300, 1000, 3000, 6000]:
    g = G[:N, :N]; n = np.arange(1, N+1)
    alt = (-1.0)**(n-1)/n; harm = 1.0/n
    ra = alt@g@alt/(alt@alt); rh = harm@g@harm/(harm@harm)
    lam = np.linalg.eigvalsh(g)[0]
    # dist^2(w_1, span(w_2..w_N)) = 1/(G^-1)_{11}
    e = np.zeros(N); e[0] = 1; dist = 1/np.linalg.solve(g, e)[0]
    print(N, 'lam_min %.3e  Rayleigh alt %.3e (x N/log^2N = %.3f, x N = %.3f)  Rayleigh 1/n %.3e (/N = %.4e)  dist2(w1,rest)=%.4e  x logN/d1 = %.3f' %
          (lam, ra, ra*N/math.log(N)**2, ra*N, rh, rh/N, dist, dist*math.log(N)/d1))
