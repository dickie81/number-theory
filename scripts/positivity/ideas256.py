"""Ideas 2 (symmetry splitting), 5 (reweighted metric), 6 (GUE bridge) for the Weil form W_L
(support [-L,L], 40-sine basis of place_margin). UNCERTIFIED float64."""
import numpy as np, math, os
from scipy.special import digamma
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
import place_margin as pm
M=pm.M; T=pm.T; out=[]; P=lambda *a: (out.append(" ".join(str(x) for x in a)), print(*a, flush=True))
G=np.load("/tmp/zeta_zeros_600.npy")
def Bx(L): x=np.linspace(-L,L,4001); return x,x[1]-x[0],pm.basis_vals(x,L)
def primeform(L,chi=lambda n:1,jit=None,flip=()):
    x,dx,B=Bx(L); pr=np.zeros((M,M))
    for n in range(2,len(pm.LAM)):
        if pm.LAM[n]==0 or chi(n)==0: continue
        y=math.log(n)+(jit.get(n,0) if jit else 0)
        if y<=0 or y>=2*L: continue
        C=B@pm.basis_vals(x-y,L).T*dx; pr+=(-1 if n in flip else 1)*chi(n)*pm.LAM[n]/math.sqrt(n)*(C+C.T)
    return pr
def archform(L,a=0,q=1):
    F=pm.fhat(L); psi=digamma(0.25+a/2+0.5j*T).real
    A=((F*psi[None,:])@F.conj().T*0.02*2/(2*math.pi)).real; return A+(math.log(q)-math.log(math.pi))*np.eye(M),F
def poles(L): x,dx,B=Bx(L); return B@np.exp(-x/2)*dx, B@np.exp(x/2)*dx
def orth(cols):
    Q,_=np.linalg.qr(np.stack(cols,1)); return np.linalg.svd(np.eye(M)-Q@Q.T)[0][:,:M-len(cols)]
def mine(W,U): return np.linalg.eigvalsh(U.T@((W+W.T)/2)@U)
rng=np.random.default_rng(5); JIT={n:0.05*rng.normal() for n in range(2,len(pm.LAM))}
# parity: m odd -> even fn about 0, m even -> odd
par=np.array([1 if (m%2) else -1 for m in range(1,M+1)])
Ls=(0.5,0.7,1.0,1.5,2.0,2.5)
P("IDEA 2a. parity split. cross-block norm |W_eo|/|W|; min eig even block / odd block (pole-orth within block)")
P("   L   cross     real even    real odd   | jitter even  odd   | flip3 even  odd   | #<1e-6 even/odd (real)")
p2={}
for L in Ls:
    A,_=archform(L); a,b=poles(L); E=np.diag(par==1).astype(float); O=np.eye(M)-E
    res=[]
    for kw in ({},{"jit":JIT},{"flip":(3,)}):
        W=A-primeform(L,**kw)
        ue=orth([E@(a+b)])[:, :]; ue=ue[:, np.abs(O@ue).sum(0)<1e-8] if False else None
        # bases inside blocks
        Ie=np.where(par==1)[0]; Io=np.where(par==-1)[0]
        We=W[np.ix_(Ie,Ie)]; Wo=W[np.ix_(Io,Io)]
        ae=(a+b)[Ie]; ao=(a-b)[Io]
        Ue=np.linalg.svd(np.eye(len(Ie))-np.outer(ae,ae)/(ae@ae))[0][:,:-1]; Uo=np.linalg.svd(np.eye(len(Io))-np.outer(ao,ao)/(ao@ao))[0][:,:-1]
        ee=np.linalg.eigvalsh(Ue.T@We@Ue); eo=np.linalg.eigvalsh(Uo.T@Wo@Uo)
        res.append((ee,eo)); cross=np.linalg.norm(W[np.ix_(Ie,Io)])/np.linalg.norm(W) if not kw else cross
    p2[L]=res
    P("%.1f  %.1e   %+.2e  %+.2e  | %+.2e %+.2e | %+.2e %+.2e | %d/%d"%(L,cross,res[0][0][0],res[0][1][0],res[1][0][0],res[1][1][0],res[2][0][0],res[2][1][0],np.sum(res[0][0]<1e-6),np.sum(res[0][1]<1e-6)))
chis={"mod4 (odd)":(lambda n:[0,1,0,-1][n%4],1,4,6.0209),"mod3 (odd)":(lambda n:[0,1,-1][n%3],1,3,8.0397),
      "mod5 real (even)":(lambda n:[0,1,-1,-1,1][n%5],0,5,6.6485),"mod8 even":(lambda n:[0,1,0,-1,0,-1,0,1][n%8],0,8,3.5761)}
P("\nIDEA 2b. Dirichlet-twisted Weil forms W_L(chi) (no pole; arch psi(1/4+a/2+it/2)+log(q/pi)); min eig and #<1e-6 vs L; first zero gamma_1(chi) listed (literature values, not recomputed)")
p2b={}
for name,(chi,a,q,g1) in chis.items():
    row=[]
    for L in Ls:
        A,_=archform(L,a,q); W=A-primeform(L,chi); e=np.linalg.eigvalsh((W+W.T)/2)
        We=A-primeform(L,chi,flip=(3,) if chi(3) else (5,)); ef=np.linalg.eigvalsh((We+We.T)/2)[0]
        row.append((e[0],np.sum(e<1e-6),ef))
    p2b[name]=row
    P(" %-17s g1=%.2f  "%(name,g1)+"  ".join("L=%.1f:%+.1e(%d) flip%+.1e"%(L,*r) for L,r in zip(Ls,row)))
P("\nIDEA 5. generalised min eig c(L)=min W/M on pole-orth space, M_w = int |fhat|^2 w(t) dt/pi:")
fams={"L2 (w=1)":lambda t:np.ones_like(t),"H^-1 1/(1+t^2)":lambda t:1/(1+t**2),"H^-2":lambda t:1/(1+t**2)**2,
      "gauss e^-(t/10)^2":lambda t:np.exp(-(t/10)**2),"arch-adapted log(2+t)":lambda t:np.log(2+t),
      "zero-dip prod":None}
p5={}
for name,w in fams.items():
    row=[]
    for L in Ls:
        A,F=archform(L); a,b=poles(L); U=orth([a,b])
        if w is None:  # circular control: weight vanishing at first 10 zeros
            wt=np.prod([np.minimum(1,((T-g)/1.0)**2) for g in G[:10]],axis=0)
        else: wt=w(T)
        Mm=((F*wt[None,:])@F.conj().T*0.02*2/(2*math.pi)).real
        Mu=U.T@Mm@U; Mu=(Mu+Mu.T)/2
        res=[]
        for kw in ({},{"jit":JIT}):
            Wu=U.T@(A-primeform(L,**kw))@U; Wu=(Wu+Wu.T)/2
            em,V=np.linalg.eigh(Mu); keep=em>1e-12*em.max(); S=V[:,keep]/np.sqrt(em[keep])
            res.append(np.linalg.eigvalsh(S.T@Wu@S)[0])
        row.append(res)
    p5[name]=row
    P(" %-22s "%name+"  ".join("L=%.1f:%+.1e/j%+.1e"%(L,*r) for L,r in zip(Ls,row)))
P("\nIDEA 6. GUE bridge: zero-side forms Z=2 sum|fhat(g)|^2 (600 ordinates), real vs 40 GUE samples (same smooth density)")
import near_null_lib as nl
p6={}
for L in (1.0,2.0):
    a,b=poles(L); U=orth([a,b]); ez=np.linalg.eigvalsh(U.T@nl.zform(L,G)@U)
    S=[]
    r2=np.random.default_rng(11)
    for s in range(40): S.append(np.linalg.eigvalsh(U.T@nl.zform(L,nl.gue_fake(r2))@U))
    S=np.array(S); p6[L]=(ez,S)
    nn=lambda e:np.sum(e<1e-6); lg=lambda e:np.log10(np.maximum(e,1e-18))
    P(" L=%.1f near-null dim real %d, GUE mean %.1f sd %.1f range %d-%d"%(L,nn(ez),np.mean([nn(e) for e in S]),np.std([nn(e) for e in S]),min(nn(e) for e in S),max(nn(e) for e in S)))
    for k in (0,5,10,20,30,37):
        pct=np.mean(lg(S[:,k])<lg(ez[k]))*100
        P("   log10 lambda_%d real %+.2f  GUE mean %+.2f sd %.2f  real percentile %.0f%%"%(k+1,lg(ez[k]),lg(S[:,k]).mean(),lg(S[:,k]).std(),pct))
fig,ax=plt.subplots(1,3,figsize=(17,4.5))
for name,row in p2b.items(): ax[0].semilogy(Ls,[max(abs(r[0]),1e-16) for r in row],'o-',label=name)
ax[0].semilogy(Ls,[max(abs(p2[L][0][0][0]),1e-16) for L in Ls],'k--',label="zeta even");ax[0].semilogy(Ls,[max(abs(p2[L][0][1][0]),1e-16) for L in Ls],'k:',label="zeta odd")
ax[0].set_title("Idea 2: |min eig| per block / twist"); ax[0].legend(fontsize=7); ax[0].set_xlabel("L")
for name,row in p5.items(): ax[1].semilogy(Ls,[max(abs(r[0]),1e-16) for r in row],'o-',label=name)
ax[1].set_title("Idea 5: |c(L)| = |min W/M|"); ax[1].legend(fontsize=7); ax[1].set_xlabel("L")
ez,S=p6[2.0]; k=np.arange(1,39)
for e in S: ax[2].semilogy(k,np.maximum(e,1e-18),color='0.7',lw=.5)
ax[2].semilogy(k,np.maximum(ez,1e-18),'r',lw=2,label="real zeros"); ax[2].set_title("Idea 6: zero-side spectrum L=2, real vs 40 GUE"); ax[2].legend()
plt.tight_layout(); plt.savefig("ideas256.png",dpi=110); plt.savefig("/workspace/ideas256.png",dpi=110)
open("ideas256_results.txt","w").write("\n".join(out)+"\n")
