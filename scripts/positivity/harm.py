import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
import numpy as np, math, ball_orbit as bo
from fractions import Fraction
X=400; A,B=bo.tables(X)
lam=np.zeros(X+1)
for p in range(2,X+1):
    if all(p%d for d in range(2,int(p**.5)+1)):
        q=p
        while q<=X: lam[q]=math.log(p); q*=p
def KH(x): return float(bo.kernel_over_sqrt(np.array([x]),A,B)[0])*math.sqrt(x)
HMAX=2048
hs=np.arange(1,HMAX+1)
cache={}
def data(f):  # f Fraction >=1: returns K_int, C exact, cumulative harmonic corrections array over H
    if f in cache: return cache[f]
    x=f.numerator/f.denominator; js=np.arange(1,int(math.floor(x+1e-12))+1)
    L=lam[js]; y=f.numerator/(f.denominator*js)
    Cex=float((L*(y%1)).sum())
    jump=sum(lam[j] for j in js if f.numerator % (f.denominator*j)==0)/2   # Fourier gives 1/2 at integers
    terms=(L[:,None]*np.sin(2*np.pi*np.outer(y,hs))/(np.pi*hs)).sum(0)   # sum_j L sin(2πhy)/(πh), per h
    CH=L.sum()/2-np.cumsum(terms)-jump   # truncated C with jump fixed
    r=(KH(x)-Cex/math.sqrt(x), Cex, CH)
    cache[f]=r; return r
def mineig(N,H):
    G=np.zeros((N,N))
    for i in range(1,N+1):
        for j in range(1,i+1):
            f=Fraction(i,j); Ki,Ce,CH=data(f); x=i/j
            c = Ce if H is None else (L0 if False else (CH[H-1] if H>0 else (data(f)[2][0]*0+ (sum(lam[1:int(x)+1])/2 - (sum(lam[jj] for jj in range(1,int(x)+1) if f.numerator%(f.denominator*jj)==0)/2)))))
            G[i-1,j-1]=G[j-1,i-1]=math.sqrt(i*j)*(Ki+c/math.sqrt(x))
    e=np.linalg.eigvalsh(G); return e.min(), int((e<0).sum())
for N in [25,50,100,200]:
    full=mineig(N,None); row=[f"full {full[0]:.3g}"]
    need=None
    for H in [0,1,2,4,8,16,32,64,128,256,512,1024,2048]:
        m,neg=mineig(N,H); row.append(f"H{H}:{neg}")
        if neg==0 and need is None: need=H
    print(N,"need H=",need," ".join(row),flush=True)
