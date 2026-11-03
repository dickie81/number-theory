"""Shell-interior Schur analysis of the Weil form at each prime-power entry. UNCERTIFIED float64.
Support [-L+,L+], L+-=log(n)/2+-d. Basis: 40 sines on interior [-L-,L-] + 10 sines on each shell strip.
On the pole-orthogonal subspace: interior block = pole-orth interior functions; shell block = its complement.
a=min eig A, c=min eig C, b=||B||, Schur=min eig(C - B^T A^-1 B). Also with a synthetic off-line zero."""
import numpy as np, math
import place_margin as pm
out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
NI,NS=40,10
QI,QS=3000,600
def segs(Lm,Lp): return [(-Lm,Lm,NI),(-Lp,-Lm,NS),(Lm,Lp,NS)]
def fhat(sg,t):
    t=np.asarray(t,dtype=complex); rows=[]
    for al,be,K in sg:
        w=be-al
        for j in range(1,K+1):
            k=j*math.pi/w
            I=((np.exp(1j*(t+k)*w)-1)/(1j*(t+k))-(np.exp(1j*(t-k)*w)-1)/(1j*(t-k)))/(2j)
            rows.append(np.exp(1j*t*al)*I*math.sqrt(2/w))
    return np.array(rows)
def vals(sg,y):
    rows=[]
    for al,be,K in sg:
        w=be-al; m=(y>al)&(y<be)
        for j in range(1,K+1):
            r=np.zeros_like(y); r[m]=np.sin(j*math.pi*(y[m]-al)/w)*math.sqrt(2/w); rows.append(r)
    return np.array(rows)
def build(n,d):
    Lm,Lp=math.log(n)/2-d,math.log(n)/2+d; sg=segs(Lm,Lp); N=NI+2*NS
    F=fhat(sg,pm.T); arch=((F*pm.PSI)@F.conj().T).real*0.02*2/(2*math.pi)-math.log(math.pi)*np.eye(N)
    xs,wq=[],[]
    g,w=np.polynomial.legendre.leggauss(600)
    for al,be,_ in sg:
        q=QI if be-al>2*d+1e-9 else QS; g,w=np.polynomial.legendre.leggauss(q)
        xs.append(al+(be-al)*(g+1)/2); wq.append(w*(be-al)/2)
    x=np.concatenate(xs); wq=np.concatenate(wq); Bw=vals(sg,x)*wq
    prim=np.zeros((N,N))
    for m in range(2,len(pm.LAM)):
        y=math.log(m)
        if pm.LAM[m]==0 or y>=2*Lp: continue
        C=Bw@vals(sg,x-y).T; prim+=pm.LAM[m]/math.sqrt(m)*(C+C.T)
    a=Bw@np.exp(-x/2); b=Bw@np.exp(x/2)
    return sg,arch-prim,a,b
def offline(sg,gam,dl):   # replace on-line pair at gam by off-line quadruple gam+-i dl
    def pair(z):
        u=fhat(sg,[z])[:,0]; v=fhat(sg,[-z])[:,0]; M=np.outer(u,v); return (M+M.T).real
    return pair(gam-1j*dl)+pair(gam+1j*dl)-2*pair(gam)
def analyse(W,a,b):
    N=W.shape[0]; Q,_=np.linalg.qr(np.stack([a,b],1)); Pp=np.eye(N)-Q@Q.T
    Ui=np.linalg.svd(Pp[:NI,:NI] if False else Pp[:,:NI])[0][:,:NI]   # pole-orth part of interior span
    # interior pole-orth: x in span(e_1..e_NI) with a.x=b.x=0
    Qi,_=np.linalg.qr(np.stack([a[:NI],b[:NI]],1)); Ii=np.linalg.svd(np.eye(NI)-Qi@Qi.T)[0][:,:NI-2]
    Ui=np.vstack([Ii,np.zeros((2*NS,NI-2))])
    Uall=np.linalg.svd(Pp)[0][:,:N-2]; R=Uall-Ui@(Ui.T@Uall); Us=np.linalg.svd(R)[0][:,:2*NS]
    A=Ui.T@W@Ui; C=Us.T@W@Us; B=Ui.T@W@Us
    ea=np.linalg.eigvalsh(A)[0]; ec=np.linalg.eigvalsh(C)[0]; bn=np.linalg.norm(B,2)
    sch=np.linalg.eigvalsh(C-B.T@np.linalg.solve(A,B))[0] if ea>0 else float('nan')
    tot=np.linalg.eigvalsh(Uall.T@W@Uall)[0]
    return ea,ec,bn,sch,tot
d=0.02
P("d=%.2f; interior |x|<L-, shell L-<|x|<L+, L+-=log(n)/2+-d; min eigs on pole-orth subspace"%d)
P(" n   a(interior)   c(shell)    b=||B||    b^2/(ac)     Schur min    whole W    Lam(n)/sqrt(n)")
ns=[n for n in range(2,51) if pm.LAM[n]>0]
for n in ns:
    sg,W,a,b=build(n,d); ea,ec,bn,sch,tot=analyse((W+W.T)/2,a,b)
    P("%2d  %+.3e  %+.3e  %.3e  %+.3e  %+.3e  %+.3e  %.3f"%(n,ea,ec,bn,bn**2/(ea*ec) if ea*ec!=0 else float('nan'),sch,tot,pm.LAM[n]/math.sqrt(n)))
P("\nsynthetic off-line zero at gamma=14.1347, delta (support at n):")
for n in (7,13,23):
    for dl in (0.3,0.1):
        sg,W,a,b=build(n,d); W=(W+W.T)/2+offline(sg,14.134725,dl); ea,ec,bn,sch,tot=analyse(W,a,b)
        P("n=%2d delta=%.1f: a=%+.3e c=%+.3e b=%.3e Schur=%+.3e whole=%+.3e"%(n,dl,ea,ec,bn,sch,tot))
open("shell_schur_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
