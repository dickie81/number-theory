"""Idea 4: flow of the Weil form W_L in L (pole-orth, support [-L,L], 40-sine basis). UNCERTIFIED float64.
Exact fact (no numerics): test spaces are nested in L, so the true lambda_min(L) is NON-INCREASING in L."""
import numpy as np, math
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
import place_margin as pm
M=pm.M; out=[]; P=lambda *a: (out.append(" ".join(str(x) for x in a)), print(*a, flush=True))
def low(L, jit=None, flip=()):
    arch,prim,a,b,_=pm.forms(L)
    if jit is not None or flip:
        x=np.linspace(-L,L,4001); dx=x[1]-x[0]; B=pm.basis_vals(x,L); prim=np.zeros((M,M))
        for n in range(2,len(pm.LAM)):
            if pm.LAM[n]==0: continue
            y=math.log(n)+(jit.get(n,0) if jit else 0)
            if y<=0 or y>=2*L: continue
            C=B@pm.basis_vals(x-y,L).T*dx; prim+=(-1 if n in flip else 1)*pm.LAM[n]/math.sqrt(n)*(C+C.T)
    W=arch-prim; Q,_=np.linalg.qr(np.stack([a,b],1)); U=np.linalg.svd(np.eye(M)-Q@Q.T)[0][:,:M-2]
    ev,V=np.linalg.eigh(U.T@((W+W.T)/2)@U); c=U@V[:,0]
    xb=np.array([-L+1e-3*L,L-1e-3*L]); fb=c@pm.basis_vals(xb,L)   # edge values ~ slope*eps
    return ev[:4], np.abs(fb).max()/(1e-3*L)
Ls=np.round(np.arange(0.3,3.001,0.05),3)
rng=np.random.default_rng(3); jit={n:0.05*rng.normal() for n in range(2,len(pm.LAM))}
R={k:[] for k in ("real","jit","flip")}; edge=[]
for L in Ls:
    e,s=low(L); R["real"].append(e); edge.append(s)
    R["jit"].append(low(L,jit=jit)[0]); R["flip"].append(low(L,flip=(3,))[0])
for k in R: R[k]=np.array(R[k])
lm=R["real"][:,0]; d=np.gradient(lm,Ls)
P("1. real primes: L, lambda_1..4, d lambda_1/dL (finite diff), |f'(+-L)| proxy of bottom eigvec, new prime powers with log n/2 in (L-0.05,L]")
for i,L in enumerate(Ls):
    new=[n for n in range(2,len(pm.LAM)) if pm.LAM[n] and L-0.05<math.log(n)/2<=L]
    P("%.2f  %s  d=%+.2e  edge=%.2e  %s"%(L," ".join("%+.3e"%v for v in R["real"][i]),d[i],edge[i],new if new else ""))
P("\n2. summary")
P(" max lambda_min increase between grid points (true lambda_min is non-increasing; 40-mode basis is NOT nested):",
  "%.2e"%np.max(np.diff(lm)))
for k in ("jit","flip"):
    m=R[k][:,0]; br=Ls[np.argmax(m<-1e-4)] if np.any(m<-1e-4) else None
    P(" %s: first L with lambda_min<-1e-4: %s ; min over grid %.3e"%(k,br,m.min()))
P(" real: min over grid %.3e (all within float noise of 0 = near-null)"%lm.min())
fig,ax=plt.subplots(1,2,figsize=(12,4.5))
for k,c in (("real","C0"),("jit","C1"),("flip","C3")):
    ax[0].plot(Ls,R[k][:,0],'-',color=c,label=k+" lambda_1"); ax[0].plot(Ls,R[k][:,1],':',color=c)
for n in range(2,len(pm.LAM)):
    if pm.LAM[n] and math.log(n)/2<=3: ax[0].axvline(math.log(n)/2,color='k',lw=.3)
ax[0].set_yscale('symlog',linthresh=1e-6); ax[0].set_xlabel("L"); ax[0].legend(); ax[0].set_title("low eigenvalues vs L (lines: log n/2)")
ax[1].semilogy(Ls,np.maximum(R["real"][:,:4],1e-12)); ax[1].set_title("real primes, lambda_1..4 (clipped 1e-12)"); ax[1].set_xlabel("L")
plt.tight_layout(); plt.savefig("flow.png",dpi=110); plt.savefig("/workspace/flow.png",dpi=110)
open("flow_results.txt","w").write("\n".join(out)+"\n")
