"""Junction slice + scoped semilocal partial. UNCERTIFIED floats (float64, 40-mode sine basis).
(b) at L+=log(n)/2+d, restrict W to directions orthogonal to functions supported in [-L-,L-], L-=log(n)/2-d.
(a-partial) S-truncated Weil form W_S = W_inf - (terms of primes in S): slack min eig vs cost of primes outside S.
NOT built: the semilocal Sonin projector itself (p-adic cutoff + semilocal Fourier transform)."""
import numpy as np, math
import place_margin as pm
M=pm.M; out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
def pp(n):
    for p in range(2,n+1):
        if n%p==0:
            while n%p==0: n//=p
            return p if n==1 else None
def parts(L):
    arch,_,a,b,_=pm.forms(L); x=np.linspace(-L,L,4001); dx=x[1]-x[0]; B=pm.basis_vals(x,L); pr={}
    for n in range(2,len(pm.LAM)):
        y=math.log(n)
        if pm.LAM[n]==0 or y>=2*L: continue
        C=B@pm.basis_vals(x-y,L).T*dx; p=pp(n); pr[p]=pr.get(p,0)+pm.LAM[n]/math.sqrt(n)*(C+C.T)
    return arch,pr,a,b,x,B
def U_of(cons):
    Q,_=np.linalg.qr(np.stack(cons,1)); return np.linalg.svd(np.eye(M)-Q@Q.T)[0][:,:M-len(cons)]
ev=lambda U,W: np.linalg.eigvalsh(U.T@((W+W.T)/2)@U)
d=0.004
P("(b) junction slice: margins of full W at L+ = log(n)/2+%.3f"%d)
P(" n   whole L+ space   old dirs (supp L-)   junction complement   drop(L- -> L+)")
for n in (2,3,4,5,7,8,9,11,13):
    Lp=math.log(n)/2+d; Lm=Lp-2*d
    arch,pr,a,b,x,B=parts(Lp); W=arch-sum(pr.values())
    Bm=pm.basis_vals(x,Lm)*(np.abs(x)<=Lm); dx=x[1]-x[0]
    C=B@Bm.T*dx                                   # L- functions in L+ coords (L2 projection)
    Qo,_=np.linalg.qr(C); Qo=Qo[:,np.linalg.svd(C)[1]>1e-6]
    Pc=np.eye(M)-Qo@Qo.T; cons=[a,b]
    whole=ev(U_of(cons),W)[0]
    Uc=np.linalg.svd(Pc)[0][:,:M-Qo.shape[1]]     # complement
    Uc2=Uc@U_of([Uc.T@a,Uc.T@b])[:Uc.shape[1],:Uc.shape[1]-2] if Uc.shape[1]>2 else Uc
    jc=ev(Uc2,W)[0] if Uc2.shape[1] else float('nan')
    Uo=Qo@U_of([Qo.T@a,Qo.T@b])[:Qo.shape[1],:Qo.shape[1]-2]
    old=ev(Uo,W)[0]
    P("%2d   %+.3e       %+.3e           %+.3e (dim %d)   %+.3e"%(n,whole,old,jc,Uc.shape[1],whole-old))
P("\n(a-partial) S-truncated Weil form: slack = min eig(W_inf - primes in S) on pole-orth; cost = max eig(sum of primes outside S)")
P(" L     S        slack        cost(outside S)   slack>=cost?")
for L in (0.6,0.8,1.0,1.2,1.5):
    arch,pr,a,b,_,_=parts(L); U=U_of([a,b])
    for S in ({2},{2,3}):
        WS=arch-sum(v for p,v in pr.items() if p in S); rest=sum((v for p,v in pr.items() if p not in S),np.zeros((M,M)))
        s=ev(U,WS)[0]; c=ev(U,rest)[-1]
        P("%.1f  %-8s %+.3e   %+.3e        %s"%(L,"{inf,"+",".join(map(str,sorted(S)))+"}",s,c,s>=c))
open("junction_slice_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
