"""lambda_min of the even-sector Weil form (Zhu convention, K=48, dps 47) at L=0.8 and 1.0 for Cramer random prime sets,
versus their max prime-comb alignment on [1,T*]. Tests whether alignment tracks positivity."""
import mpmath as mp, math, pickle, numpy as np
from multiprocessing import Pool
import hpcore as h, hp3
def run(a):
    L,seed=a; mp.mp.dps=47 if L<0.9 else 60
    s=hp3.fakeset(L,seed,"cramer") if seed>=0 else hp3.realset(L)
    M,_=h.form(L,48 if L<0.9 else 81,extra=[(mp.mpf(y),mp.mpf(w)) for y,w in s]); E,_=h.eig(M)
    return L,seed,float(E[0]),hp3.align(s,L)[0],sorted(set(round(math.exp(y)) for y,_ in s))[:8]
if __name__=="__main__":
    with Pool(5) as P: R=P.map(run,[(0.8,s) for s in range(-1,15)]+[(1.0,s) for s in range(-1,10)])
    pickle.dump(R,open("/workspace/hp3b.pkl","wb"))
    for r in R: print("L=%.1f seed %2d lam_min %+.3e  maxalign %.3f  n:%s"%r)
