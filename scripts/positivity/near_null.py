"""Near-null directions of the Weil form (pole-orth, support [-L,L], 40-sine basis). UNCERTIFIED float64."""
import numpy as np, math, os
import mpmath as mp
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
import place_margin as pm, sonin_prolate as sp
M=pm.M; out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
zf="/tmp/zeta_zeros_600.npy"
if not os.path.exists(zf): np.save(zf,np.array([float(mp.im(mp.zetazero(n))) for n in range(1,601)]))
G=np.load(zf)
def fh(t,L):
    k=np.arange(1,M+1)*math.pi/(2*L); t=np.asarray(t)[None,:]; k=k[:,None]
    I=((np.exp(1j*(t+k)*2*L)-1)/(1j*(t+k))-(np.exp(1j*(t-k)*2*L)-1)/(1j*(t-k)))/(2j)
    return np.exp(-1j*t*L)*I/math.sqrt(L)
def zform(L,g):  # 2 sum |fhat(gamma)|^2 as a matrix
    F=fh(g,L); return 2*(F@F.conj().T).real
def Nsm(T): return T/(2*math.pi)*math.log(T/(2*math.pi*math.e))+7/8
def gue_fake(rng):
    H=rng.normal(size=(1200,1200))+1j*rng.normal(size=(1200,1200)); H=(H+H.conj().T)/2
    e=np.linalg.eigvalsh(H)/math.sqrt(1200); e=e[(e>-1)&(e<1)]                # bulk
    u=1200*(0.5+(e*np.sqrt(4-e**2))/(4*math.pi)+np.arcsin(e/2)/math.pi)  # semicircle unfold (radius 2)
    u=u-u[0]+0.5; gs=[]; from scipy.optimize import brentq
    for v in u[:600]: gs.append(brentq(lambda T, v=v: Nsm(T)-v, 2*math.pi, 1e5))
    return np.array(gs)
xs=np.linspace(-1,1,801)
def fx(c,L,x): return c@pm.basis_vals(x,L)
res={}
P("1. eigenvalue counts on pole-orth subspace (dim 38); bandwidth K=M*pi/(2L); 2*N(K) = real dims killed by zeros below K")
P("  L    min eig     #<1e-3  #<1e-6   N(K) zeros<K   38-2N(K)   ||W - Z600|| (rel)")
for L in (0.7,1.0,1.5,2.0,3.0):
    arch,prim,a,b,_=pm.forms(L); W=arch-prim
    Q,_=np.linalg.qr(np.stack([a,b],1)); U=np.linalg.svd(np.eye(M)-Q@Q.T)[0][:,:M-2]
    Wu=U.T@((W+W.T)/2)@U; ev,V=np.linalg.eigh(Wu); K=M*math.pi/(2*L); NK=int(np.sum(G<K))
    Z=U.T@zform(L,G)@U; rel=np.linalg.norm(Wu-Z)/np.linalg.norm(Wu)
    P("%.1f  %+.2e   %2d      %2d       %3d          %3d        %.2e"%(L,ev[0],np.sum(ev<1e-3),np.sum(ev<1e-6),NK,38-2*NK,rel))
    res[L]=(U,ev,V,Z)
P("\n2. bottom eigenvector: zero-side check  (eig vs 2*sum|fhat(gamma)|^2 over 600 zeros; max|fhat| at first 10 zeros vs max|fhat| on [0,K])")
fig,ax=plt.subplots(2,2,figsize=(12,8))
for i,L in enumerate((1.0,2.0)):
    U,ev,V,Z=res[L]
    for j in range(3):
        c=U@V[:,j]; x=xs*L; ax[0,i].plot(x,fx(c,L,x),label="eig %.1e"%ev[j])
        t=np.linspace(0.01,120,6000); F=np.abs(c@fh(t,L))**2; ax[1,i].semilogy(t,F,lw=0.8)
        if j==0:
            zs=2*np.sum(np.abs(c@fh(G,L))**2); f10=np.abs(c@fh(G[:10],L)).max(); fmax=np.sqrt(F.max())
            P("L=%.1f eig=%.2e  zero-sum=%.2e  max|fhat(gamma_1..10)|=%.2e  max|fhat|=%.2e"%(L,ev[0],zs,f10,fmax))
    for g in G[G<120]: ax[1,i].axvline(g,color='k',lw=0.3)
    ax[0,i].set_title("bottom 3 eigvecs f(x), L=%.1f"%L); ax[0,i].legend(); ax[1,i].set_title("|fhat(t)|^2, zeta zeros as lines")
plt.tight_layout(); plt.savefig("near_null.png",dpi=110); plt.savefig("/workspace/near_null.png",dpi=110)
P("\n3. shape test: |<f_L, f_L' rescaled>| for bottom eigvec; and best overlap with even/odd prolate xi_n(|x|/L) (n<8)")
bot={L:U@V[:,0] for L,(U,ev,V,Z) in res.items()}
def prof(L): v=fx(bot[L],L,xs*L); return v/np.linalg.norm(v)
Ls=sorted(bot)
for i in range(len(Ls)-1):
    P("L=%.1f vs %.1f: overlap %.3f"%(Ls[i],Ls[i+1],abs(prof(Ls[i])@prof(Ls[i+1]))))
for L in Ls:
    p=prof(L); best=0
    for n in range(8):
        e=sp.xi(n,np.abs(xs)); o=e*np.sign(xs) if False else e
        for q in (e, e*np.sign(xs)):
            q=q/np.linalg.norm(q); best=max(best,abs(p@q))
    P("L=%.1f best prolate overlap %.3f"%(L,best))
P("\n4. GUE control: zero-side form with 600 GUE fake ordinates (same smooth density), counts below thresholds")
rng=np.random.default_rng(1); Gf=gue_fake(rng); P("fake ordinates first 5:",np.round(Gf[:5],2),"real:",np.round(G[:5],2))
for L in (1.0,2.0,3.0):
    U,ev,V,Z=res[L]; ez=np.linalg.eigvalsh(Z); ef=np.linalg.eigvalsh(U.T@zform(L,Gf)@U)
    P("L=%.1f  #<1e-3 real-zeros %2d  GUE %2d | #<1e-6 real %2d GUE %2d | min real %.1e GUE %.1e"%(L,np.sum(ez<1e-3),np.sum(ef<1e-3),np.sum(ez<1e-6),np.sum(ef<1e-6),ez[0],ef[0]))
open("near_null_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
