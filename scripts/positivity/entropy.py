"""Entropy routes to Weil positivity. UNCERTIFIED float64 (mpmath for H_t).
Conventions: fhat(t)=int f e^{-itx}dx; densities p=|f|^2/||f||^2 on x, q=|fhat|^2/(2pi||f||^2) on t.
Hirschman-Beckner in this convention: H(p)+H(q) >= log(pi e) = 2.1447."""
import numpy as np, math, mpmath as mp
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
import place_margin as pm, near_null_lib as nl
M=pm.M; out=[]; P=lambda *a: (out.append(" ".join(str(x) for x in a)), print(*a, flush=True))
G=np.load("/tmp/zeta_zeros_600.npy"); rng=np.random.default_rng(5); JIT={n:0.05*rng.normal() for n in range(2,len(pm.LAM))}
def form(L,jit=None,flip=()):
    arch,prim,a,b,_=pm.forms(L)
    if jit or flip:
        x=np.linspace(-L,L,4001); dx=x[1]-x[0]; B=pm.basis_vals(x,L); prim=np.zeros((M,M))
        for n in range(2,len(pm.LAM)):
            if pm.LAM[n]==0: continue
            y=math.log(n)+(jit.get(n,0) if jit else 0)
            if 0<y<2*L: C=B@pm.basis_vals(x-y,L).T*dx; prim+=(-1 if n in flip else 1)*pm.LAM[n]/math.sqrt(n)*(C+C.T)
    W=arch-prim; Q,_=np.linalg.qr(np.stack([a,b],1)); U=np.linalg.svd(np.eye(M)-Q@Q.T)[0][:,:M-2]
    return U.T@((W+W.T)/2)@U, U
def ent(c,L):
    x=np.linspace(-L,L,4001); f=c@pm.basis_vals(x,L); p=f**2; p/=p.sum()*(x[1]-x[0])
    Hx=-np.sum(p*np.log(p+1e-300))*(x[1]-x[0])
    t=np.linspace(-400,400,80001); F=np.abs(c@nl.fh(np.abs(t),L))**2; q=F/(F.sum()*(t[1]-t[0]))
    Ht=-np.sum(q*np.log(q+1e-300))*(t[1]-t[0])
    tz=np.concatenate([G,-G]); dip=np.zeros_like(t,bool)
    for g in tz[np.abs(tz)<400]: dip|=np.abs(t-g)<0.25
    return Hx,Ht,q[dip].sum()*(t[1]-t[0])
P("1. entropic uncertainty (bound log(pi e)=%.4f; support bound H(p)<=log 2L)"%math.log(math.pi*math.e))
P("  L  set    vec        H(p)    H(q)    sum    mass within 0.25 of a zero (dips cover %s of [0,400])")
cov={}
for L in (1.0,2.0):
    for lab,kw in (("real",{}),("jit",{"jit":JIT}),("flip",{"flip":(3,)})):
        Wu,U=form(L,**kw); ev,V=np.linalg.eigh(Wu)
        for nm,j in (("bottom",0),("mid",19),("top",-1)):
            Hx,Ht,dm=ent(U@V[:,j],L)
            P(" %.1f %-5s %-6s eig%+.1e  %.3f  %.3f  %.3f  %.4f"%(L,lab,nm,ev[j],Hx,Ht,Hx+Ht,dm))
nz=np.sum(G<400); P("  dip measure fraction of [0,400]: %.4f"%(nz*0.5/400))
P("\n2. von Neumann entropy S of rho=W_+/Tr W_+, negative-mass ratio Tr W_-/Tr|W|, effective rank e^S")
Ls=np.round(np.arange(0.4,3.01,0.2),2); S={k:[] for k in ("real","jit","flip")}; NEG={k:[] for k in S}
for L in Ls:
    for k,kw in (("real",{}),("jit",{"jit":JIT}),("flip",{"flip":(3,)})):
        ev=np.linalg.eigvalsh(form(L,**kw)[0]); pos=np.clip(ev,0,None); r=pos/pos.sum()
        S[k].append(-np.sum(r[r>0]*np.log(r[r>0]))); NEG[k].append(-ev[ev<0].sum()/np.abs(ev).sum())
    P(" L=%.1f  S real %.3f jit %.3f flip %.3f | neg-mass real %.1e jit %.3f flip %.3f"%(L,S["real"][-1],S["jit"][-1],S["flip"][-1],NEG["real"][-1],NEG["jit"][-1],NEG["flip"][-1]))
P("\n3a. Bost-Connes: Z=zeta(beta), E=<H>=-zeta'/zeta, S=log Z+beta E (natural units)")
BC=[]
for be in (1.01,1.05,1.1,1.5,2,3,4):
    Z=mp.zeta(be); E=-mp.zeta(be,derivative=1)/Z; Sb=mp.log(Z)+be*E; BC.append((be,float(Z),float(E),float(Sb)))
    P(" beta=%.2f  log Z=%.4f  E=%.4f  S=%.4f  F=-logZ/beta=%.4f"%(be,math.log(float(Z)),float(E),float(Sb),-math.log(float(Z))/be))
P("\n3b. de Bruijn-Newman: real zeros of H_t(z)=int_0^inf e^{t u^2} Phi(u) cos(zu) du; H_0 zeros = 2*gamma")
mp.mp.dps=30
def Phi(u): return mp.nsum(lambda n:(2*mp.pi**2*n**4*mp.e**(9*u)-3*mp.pi*n**2*mp.e**(5*u))*mp.e**(-mp.pi*n**2*mp.e**(4*u)),[1,mp.inf])
uu=np.linspace(0,1.2,2401); PH=np.array([float(Phi(u)) for u in uu]); du=uu[1]-uu[0]
def Ht(z,t): w=np.exp(t*uu**2)*PH; return np.sum(w*np.cos(z*uu))*du - 0.5*w[0]*du
def zeros(t,zmax=90):
    zs=np.arange(1,zmax,0.02); v=np.array([Ht(z,t) for z in zs]); r=[]
    for i in np.where(np.sign(v[:-1])!=np.sign(v[1:]))[0]:
        a,b=zs[i],zs[i+1]
        for _ in range(40):
            m=(a+b)/2
            if np.sign(Ht(m,t))==np.sign(Ht(a,t)): a=m
            else: b=m
        r.append((a+b)/2)
    return np.array(r)
DB={}
for t in (-0.2,-0.1,0.0,0.1,0.2):
    z=zeros(t); DB[t]=z; P(" t=%+.1f  #real zeros<90: %d  first: %s"%(t,len(z),np.round(z[:6]/2,4)))
P("  check H_0 zeros/2 vs gamma: max diff %.2e"%np.max(np.abs(DB[0.0][:6]/2-G[:6])))
d=(DB[0.1][:6]-DB[-0.1][:6])/0.2; P("  dz/dt (central diff) first 6:",np.round(d,3))
z0=DB[0.0]; zz=np.concatenate([z0,-z0])
pred=[2*sum(1/(z0[k]-w) for w in zz if w!=z0[k]) for k in range(6)]
P("  ODE dz_k/dt = 2 sum_{j!=k} 1/(z_k-z_j) (truncated to zeros<90, partial):",np.round(pred,3))
P("  near-null dim of zero-side form at L=2 using zeros of H_t/2 (<45) + G beyond:")
for t,z in DB.items():
    g=np.concatenate([z/2,G[G>z.max()/2]]); a,b=pm.forms(2.0)[2:4]; Q,_=np.linalg.qr(np.stack([a,b],1)); U=np.linalg.svd(np.eye(M)-Q@Q.T)[0][:,:M-2]
    e=np.linalg.eigvalsh(U.T@nl.zform(2.0,g)@U); P("   t=%+.1f  #<1e-6 %d"%(t,np.sum(e<1e-6)))
P("\n4. Liouville block entropy (bits) up to N=1e6 vs random +-1; Mertens max |M(x)|/sqrt x")
N=10**6; sp=np.arange(N+1); lam=np.ones(N+1,int); mu=np.ones(N+1,int); smallest=np.zeros(N+1,int)
for p in range(2,N+1):
    if smallest[p]==0: smallest[p::p][smallest[p::p]==0]=p
Om=np.zeros(N+1,int); sqf=np.ones(N+1,bool)
for n in range(2,N+1):
    p=smallest[n]; m=n//p; Om[n]=Om[m]+1; sqf[n]=sqf[m] and (m%p!=0)
lam=(-1)**Om; mu=np.where(sqf,lam,0); lam=lam[1:]; Mx=np.cumsum(mu[1:])
rnd=rng.choice([-1,1],size=N)
def bent(s,k):
    b=((s[:len(s)-k+1]>0).astype(int)); idx=np.zeros(len(b),int)
    for j in range(k): idx=idx*2+((s[j:len(s)-k+1+j])>0)
    c=np.bincount(idx,minlength=2**k)/len(idx); c=c[c>0]; return -np.sum(c*np.log2(c))
BE=[]
for k in (1,2,4,8,12):
    BE.append((k,bent(lam,k),bent(rnd,k))); P(" k=%2d  Liouville %.5f  random %.5f  max %d  deficit L %.2e R %.2e"%(k,BE[-1][1],BE[-1][2],k,k-BE[-1][1],k-BE[-1][2]))
xs=np.arange(1,N+1); P(" max |M(x)|/sqrt x on [1e3,1e6]: %.3f"%np.max(np.abs(Mx[999:])/np.sqrt(xs[999:])))
fig,ax=plt.subplots(1,4,figsize=(20,4.5))
for k in S: ax[0].plot(Ls,S[k],'o-',label=k)
ax[0].set_title("2. von Neumann entropy of W_+ (pole-orth)"); ax[0].set_xlabel("L"); ax[0].legend()
ax[1].plot([b[0] for b in BC],[b[3] for b in BC],'o-'); ax[1].set_title("3a. Bost-Connes entropy S(beta)"); ax[1].set_xlabel("beta"); ax[1].set_yscale('log')
for t,z in DB.items(): ax[2].plot(z[:12]/2,[t]*min(12,len(z)),'o',ms=3)
ax[2].set_title("3b. real zeros of H_t (/2) vs t"); ax[2].set_xlabel("z/2"); ax[2].set_ylabel("t")
ax[3].plot(xs[::200],Mx[::200]/np.sqrt(xs[::200]),lw=.5); ax[3].set_title("4. M(x)/sqrt(x)"); ax[3].set_xscale('log')
plt.tight_layout(); plt.savefig("entropy.png",dpi=110); plt.savefig("/workspace/entropy.png",dpi=110)
open("entropy_results.txt","w").write("\n".join(out)+"\n")
