"""(b') Junction slice done exactly: the orthogonal complement of L2[-L-,L-] inside L2[-L+,L+] is the
shell L-<|x|<L+. Basis: 10 sines on each strip (20 dims), L+-=log(n)/2 +- d. UNCERTIFIED floats.
Reports min eig of W (pole-orth) on the shell, with and without the entering prime power n."""
import numpy as np, math
import place_margin as pm
out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
K=10; NQ=160
def shell(Lm,Lp):
    xs,ws,B=[],[],[]
    g,w=np.polynomial.legendre.leggauss(NQ)
    for s in (-1,1):
        lo,hi=(Lm,Lp) if s>0 else (-Lp,-Lm); x=lo+(hi-lo)*(g+1)/2; xs.append(x); ws.append(w*(hi-lo)/2)
    x=np.concatenate(xs); wq=np.concatenate(ws); B=np.zeros((2*K,2*NQ)); wd=Lp-Lm
    for j in range(K):
        B[j,:NQ]=np.sin((j+1)*math.pi*(xs[0]-(-Lp))/wd)*math.sqrt(2/wd)
        B[K+j,NQ:]=np.sin((j+1)*math.pi*(xs[1]-Lm)/wd)*math.sqrt(2/wd)
    return x,wq,B
def Wparts(n,d):
    Lm,Lp=math.log(n)/2-d,math.log(n)/2+d; x,wq,B=shell(Lm,Lp); Bw=B*wq
    T=pm.T; F=Bw@np.exp(1j*np.outer(x,T))           # fhat on t-grid
    arch=((F*pm.PSI)@F.conj().T).real*0.02*2/(2*math.pi)-math.log(math.pi)*(Bw@B.T)
    def basis_at(y):                                  # shell basis evaluated at points y (zero outside)
        out=np.zeros((2*K,len(y))); wd=Lp-Lm
        for j in range(K):
            m1=(y>-Lp)&(y<-Lm); m2=(y>Lm)&(y<Lp)
            out[j,m1]=np.sin((j+1)*math.pi*(y[m1]+Lp)/wd)*math.sqrt(2/wd)
            out[K+j,m2]=np.sin((j+1)*math.pi*(y[m2]-Lm)/wd)*math.sqrt(2/wd)
        return out
    prim_old=np.zeros((2*K,2*K)); prim_n=np.zeros((2*K,2*K))
    for m in range(2,len(pm.LAM)):
        y=math.log(m)
        if pm.LAM[m]==0 or y>=2*Lp: continue
        C=Bw@basis_at(x-y).T; t=pm.LAM[m]/math.sqrt(m)*(C+C.T)
        if m==n: prim_n+=t
        else: prim_old+=t
    a=Bw@np.exp(-x/2); b=Bw@np.exp(x/2)
    return arch,prim_old,prim_n,a,b
P("junction shell L-<|x|<L+, L+-=log(n)/2+-d; min eig on pole-orth shell functions")
P(" n    d     W without n     W with n        drop        arch-only")
for d in (0.05,0.02):
    for n in (2,3,4,5,7,8,9,11,13):
        A,Po,Pn,a,b=Wparts(n,d)
        Q,_=np.linalg.qr(np.stack([a,b],1)); U=np.linalg.svd(np.eye(2*K)-Q@Q.T)[0][:,:2*K-2]
        e=lambda W: np.linalg.eigvalsh(U.T@((W+W.T)/2)@U)[0]
        w0,w1=e(A-Po),e(A-Po-Pn)
        P("%2d  %.2f   %+.4e    %+.4e    %+.3e   %+.4e"%(n,d,w0,w1,w1-w0,e(A)))
open("junction_shell_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
