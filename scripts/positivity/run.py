import numpy as np, mpmath as mp, math
from fractions import Fraction
import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..")); import ball_orbit as bo, dcore as dc
mp.mp.dps=20
X=20000
A,B=bo.tables(X)
def Kz(x):
    x=float(x); xx=max(x,1/x)
    return float(bo.kernel_over_sqrt(np.array([xx]),A,B)[0])*math.sqrt(xx)
def mkchi(c):
    K=dc.Kernel(c,X)
    def f(x):
        x=Fraction(x).limit_denominator(10**9)
        if x>=1: return complex(K(x))
        return complex(K(1/x)).conjugate()
    return f
def gramM(f,idx):
    N=len(idx);G=np.zeros((N,N),complex)
    for i,m in enumerate(idx):
        for j,n in enumerate(idx): G[i,j]=math.sqrt(m*n)*f(Fraction(m,n))
    return (G+G.conj().T)/2
def pivots(G):
    L=np.linalg.cholesky(G); d=np.abs(np.diag(L))**2; return d/d[0]
def report(name,f):
    K1=f(1).real
    sl=min((f(Fraction(2)**a*Fraction(3)**b).real+K1)/K1 for a in range(-6,7) for b in range(-4,5))
    piv=pivots(gramM(f,list(range(1,31))))
    T=np.array([[f(Fraction(2)**(i-j)).real if i>=j else f(Fraction(2)**(i-j)).real for j in range(10)] for i in range(10)])
    Tc=np.array([[f(Fraction(2)**(i-j)) for j in range(10)] for i in range(10)]);Tc=(Tc+Tc.conj().T)/2
    print(f"{name}: K1={K1:.4f} slice_min={sl:.4f} d2/d1={piv[1]:.4f} min_dk/d1(k<=30)={piv.min():.4f} argmin={piv.argmin()+1} toeplitz_h=log2 lam_min/K1={np.linalg.eigvalsh(Tc).min()/K1:.4f}")
if __name__=="__main__":
    report("zeta",Kz)
    for kk in range(1,18):
        report(f"chi19 k={kk}",mkchi(dc.char_prime(19,kk)))
    report("chi_-163",mkchi(dc.char_kron(-163)))
