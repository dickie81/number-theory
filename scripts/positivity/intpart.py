import sys, os; sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
import numpy as np, math, ball_orbit as bo
X=300
A,B=bo.tables(X)
lam=np.zeros(X+1)
for p in range(2,X+1):
    if all(p%d for d in range(2,int(p**.5)+1)):
        q=p
        while q<=X: lam[q]=math.log(p); q*=p
def KH(x):
    xx=max(x,1/x); return float(bo.kernel_over_sqrt(np.array([xx]),A,B)[0])*math.sqrt(xx)
def C(x):
    xx=max(x,1/x); return sum(lam[j]*((xx/j)%1) for j in range(1,int(xx+1e-12)+1))
g=0.5772156649015329
def gram(N,mode):
    G=np.zeros((N,N))
    for i in range(1,N+1):
        for j in range(1,N+1):
            x=i/j; xx=max(x,1/x); k=KH(x)
            if mode=="int": k-=C(x)/math.sqrt(xx)
            if mode=="smooth": k-=(C(x)-(1-g)*xx)/math.sqrt(xx)
            G[i-1,j-1]=math.sqrt(i*j)*k
    return G
for N in [10,25,50,100,200]:
    out=[]
    for mode in ["full","int","smooth"]:
        e=np.linalg.eigvalsh(gram(N,mode)); out.append(f"{mode}: min={e.min():.4g} neg={int((e<-1e-9).sum())}")
    print(N," | ".join(out),flush=True)
