"""Idea 3: structured sum-of-squares certificates for the truncated Weil form (pole-orth, support [-L,L],
40-sine basis of place_margin). UNCERTIFIED float64 + SCS/Clarabel SDP.
Certificate families (all in pole-orth coords, t = certified slack = guaranteed lower bound on min eig):
 (C0) unstructured:  W - tI PSD                          -> t = min eig (eigen-decomposition, no structure)
 (C1) per-prime scalar: arch = R + sum_n w_n arch, w_n arch - P_n PSD, R - tI PSD
 (C2) per-prime local (AM-GM type): P_n <= D_n where D_n = sum_k phi_{n,k} M_k (M_k = position-bin
      multiplication Grams, phi free), and arch - sum_n D_n - tI PSD
 (C3) C2 + one shared frequency-side multiplier of arch (D_n += w_n arch)
Controls: jittered log n (sigma), Davenport-Heilbronn-style sign flip of some prime weights."""
import numpy as np, math, cvxpy as cp
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
import place_margin as pm
M=pm.M; out=[]; P=lambda *a: (out.append(" ".join(str(x) for x in a)), print(*a, flush=True))
NB=16
def pieces(L, jit=0.0, flip=(), rng=None):
    arch,_,a,b,_=pm.forms(L)
    x=np.linspace(-L,L,4001); dx=x[1]-x[0]; B=pm.basis_vals(x,L); Pn=[]
    for n in range(2,len(pm.LAM)):
        y=math.log(n)
        if pm.LAM[n]==0 or y>=2*L: continue
        if jit: y=y+jit*rng.normal()
        if y<=0 or y>=2*L: continue
        s=-1.0 if n in flip else 1.0
        C=B@pm.basis_vals(x-y,L).T*dx; Pn.append(s*pm.LAM[n]/math.sqrt(n)*(C+C.T))
    Q,_=np.linalg.qr(np.stack([a,b],1)); U=np.linalg.svd(np.eye(M)-Q@Q.T)[0][:,:M-2]
    S=lambda X: U.T@((X+X.T)/2)@U
    edges=np.linspace(-L,L,NB+1); Mk=[]
    for k in range(NB):
        m=(x>=edges[k])&(x<edges[k+1]); Mk.append(S((B[:,m]*dx)@B[:,m].T))
    return S(arch),[S(p) for p in Pn],Mk
def solve(A,Ps,Mk,fam):
    d=A.shape[0]; t=cp.Variable(); cons=[]; tot=0; extra={}
    if fam==1:
        w=cp.Variable(len(Ps)); cons+=[w>=0]
        for i,p in enumerate(Ps): cons.append(w[i]*A-p>>0)
        tot=cp.sum(w)*A; extra['w']=w
    else:
        phi=cp.Variable((len(Ps),NB)); extra['phi']=phi
        if fam==3: w=cp.Variable(len(Ps)); cons+=[w>=0]; extra['w']=w
        for i,p in enumerate(Ps):
            D=sum(phi[i,k]*Mk[k] for k in range(NB))
            if fam==3: D=D+w[i]*A
            cons.append(D-p>>0); tot=tot+D
    R=A-tot-t*np.eye(d); cons.append((R+R.T)/2>>0)
    pr=cp.Problem(cp.Maximize(t),cons)
    try: pr.solve(solver="CLARABEL")
    except Exception: pr.solve(solver="SCS",eps=1e-7,max_iters=50000)
    return (t.value if t.value is not None else float('-inf')), {k:v.value for k,v in extra.items()}, pr.status
Ls=(0.7,1.0,1.5,2.0,2.5); res={f:[] for f in (0,1,2,3)}
P("1. certified slack t by family (larger = better; t<0 means family cannot certify positivity)")
P("  L   #prime-powers   C0=mineig    C1 scalar     C2 local      C3 local+arch   | C3 complexity: #phi>1e-6*max / total")
cert={}
for L in Ls:
    A,Ps,Mk=pieces(L); e0=np.linalg.eigvalsh(A-sum(Ps))[0]; res[0].append(e0); row=[e0]
    for f in (1,2,3):
        tv,ex,st=solve(A,Ps,Mk,f); res[f].append(tv); row.append(tv)
        if f==3: cert[L]=ex
    ph=np.abs(cert[L]['phi']); nz=np.sum(ph>1e-6*ph.max())
    P("%.1f   %3d          %+.3e   %+.3e   %+.3e   %+.3e     | %d/%d"%(L,len(Ps),*row,nz,ph.size))
P("\n2. C3 certificate structure at L=2.0: per-prime-power arch weight w_n and phi profile (bins left->right)")
L=2.0; ex=cert[L]; ns=[n for n in range(2,len(pm.LAM)) if pm.LAM[n] and math.log(n)<2*L]
for i,n in enumerate(ns[:10]):
    P(" n=%3d Lam/sqrt n=%.3f  w=%.3f  phi="%(n,pm.LAM[n]/math.sqrt(n),ex['w'][i]),np.round(ex['phi'][i],2))
P("  shared-profile test: rank of phi matrix (singular values / s1):",np.round(np.linalg.svd(ex['phi'],compute_uv=False)[:6]/np.linalg.svd(ex['phi'],compute_uv=False)[0],3))
P("\n3. controls at L=1.5 and 2.0 (C0 min eig and C3 slack): real primes vs jittered log n vs sign-flipped (DH-style)")
rng=np.random.default_rng(7); ctrl=[]
for L in (1.5,2.0):
    A,Ps,Mk=pieces(L); r=(np.linalg.eigvalsh(A-sum(Ps))[0],solve(A,Ps,Mk,3)[0])
    P("L=%.1f real        C0 %+.3e  C3 %+.3e"%(L,*r))
    for sig in (0.02,0.05,0.1):
        A,Ps,Mk=pieces(L,jit=sig,rng=rng); r=(np.linalg.eigvalsh(A-sum(Ps))[0],solve(A,Ps,Mk,3)[0])
        P("L=%.1f jitter %.2f C0 %+.3e  C3 %+.3e"%(L,sig,*r)); ctrl.append((L,sig,*r))
    for fl in ((3,),(5,7)):
        A,Ps,Mk=pieces(L,flip=fl); r=(np.linalg.eigvalsh(A-sum(Ps))[0],solve(A,Ps,Mk,3)[0])
        P("L=%.1f flip %-6s  C0 %+.3e  C3 %+.3e"%(L,str(fl),*r))
fig,ax=plt.subplots(1,2,figsize=(12,4.5))
for f,lab in ((0,"C0 min eig (unstructured)"),(1,"C1 per-prime scalar"),(2,"C2 per-prime local"),(3,"C3 local+arch")):
    ax[0].plot(Ls,res[f],'o-',label=lab)
ax[0].axhline(0,color='k',lw=.5); ax[0].set_xlabel("L"); ax[0].set_ylabel("certified slack t"); ax[0].legend(); ax[0].set_title("SOS certificate slack vs L (uncertified)")
im=ax[1].imshow(cert[2.0]['phi'],aspect='auto',cmap='RdBu_r'); ax[1].set_title("C3 local multipliers phi_{n,k}, L=2"); ax[1].set_xlabel("position bin"); ax[1].set_ylabel("prime power index"); plt.colorbar(im,ax=ax[1])
plt.tight_layout(); plt.savefig("sos.png",dpi=110); plt.savefig("/workspace/sos.png",dpi=110)
open("sos_results.txt","w").write("\n".join(out)+"\n")
