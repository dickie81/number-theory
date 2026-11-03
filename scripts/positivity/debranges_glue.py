"""Inverse spectral 'glue': Jacobi chain (discrete Krein string / de Branges chain of 2x2 shells)
whose spectral measure has atoms at +-gamma_n. UNCERTIFIED (mpmath Stieltjes, dps 80).
CIRCULAR by construction: zeros in, coefficients out."""
import mpmath as mp, numpy as np, math
mp.mp.dps=80
N=100; out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
G=[mp.im(mp.zetazero(n)) for n in range(1,N+1)]
Nbar=lambda T: T/(2*mp.pi)*mp.log(T/(2*mp.pi*mp.e))+mp.mpf(7)/8
def invN(u):
    return mp.findroot(lambda T: Nbar(T)-u, 2*mp.pi*u/mp.log(u+3)+15)
# orthonormal Stieltjes (clean)
def jac(nodes,w,M):
    x=np.concatenate([nodes,-np.asarray(nodes)]); ww=np.concatenate([w,w]); ww=ww/ww.sum()
    x=[mp.mpf(v) for v in x]; ww=[mp.mpf(v) for v in ww]
    qm=[mp.mpf(0)]*len(x); q=[mp.mpf(1)]*len(x); bprev=mp.mpf(0); b=[]
    for k in range(M):
        r=[xi*qi-bprev*qmi for xi,qi,qmi in zip(x,q,qm)]
        bk=mp.sqrt(sum(wi*ri*ri for wi,ri in zip(ww,r)))
        qm,q,bprev=q,[ri/bk for ri in r],bk; b.append(float(bk))
    return np.array(b)
rng=np.random.default_rng(1)
def gue_levels(n):
    H=rng.normal(size=(4*n,4*n))+1j*rng.normal(size=(4*n,4*n)); H=(H+H.conj().T)/2
    e=np.sort(np.linalg.eigvalsh(H)); m=len(e)//2; e=e[m-n//2-n//2:m+n-n//2]  # central n levels
    e=e[:n]; sp=np.diff(e); u=np.concatenate([[0],np.cumsum(sp/sp.mean())])+1
    return u
g=np.array([float(v) for v in G]); M=40
def unfold_back(u): return np.array([float(invN(mp.mpf(v))) for v in u])
ctrl_gue=unfold_back(gue_levels(N)); ctrl_poi=unfold_back(np.cumsum(rng.exponential(size=N))+0.5)
weights={"equal":lambda x: np.ones_like(x),"Weil 1/(1/4+g^2)":lambda x: 1/(0.25+x*x)}
def rough(b): d=np.diff(b,2); return float(np.std(d)/np.mean(b))
for wn,wf in weights.items():
    P("== weights: %s, N=%d zeros (+-gamma), first %d Jacobi off-diagonals b_n =="%(wn,N,M))
    rows={}
    for name,nodes in (("zeta",g),("GUE",ctrl_gue),("Poisson",ctrl_poi)):
        b=jac(nodes,wf(nodes),M); rows[name]=b
        P("%-8s b_1..b_8: %s"%(name," ".join("%.3f"%v for v in b[:8])))
        P("%-8s roughness std(Delta^2 b)/mean b over n<=%d: %.4f; b_n/log(n+1) at n=10,20,40: %s"%(name,M,rough(b)," ".join("%.2f"%(b[k-1]/math.log(k+1)) for k in (10,20,40))))
    P("max |b_zeta - b_GUE| / mean b = %.3f"%(np.max(np.abs(rows['zeta']-rows['GUE']))/rows['zeta'].mean()))
P("\nSphere-area 'glue' for comparison: A_{d+1}/A_d for d=2..9:",
  " ".join("%.3f"%((2*math.pi**((d+1)/2)/math.gamma((d+1)/2))/(2*math.pi**(d/2)/math.gamma(d/2))) for d in range(2,10)))
P("Verdict: the Jacobi/Krein glue for the zeros looks like the glue for GUE (and Poisson) controls with")
P("the same smooth density: the smooth part is fixed by Nbar(T) (the Gamma factor), the fluctuations")
P("by the individual zeros. Nothing in b_n is recognisably geometric, and it is defined only FROM the zeros.")
open("debranges_glue_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
