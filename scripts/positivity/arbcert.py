"""Rigorous ball-arithmetic (arb via python-flint) enclosures of the even-sector Weil-form matrix, Zhu's convention
(eq. 17 of arXiv 2608.24827), basis s_k(u)=sin(k pi(u+L)/2L)/sqrt(L), k odd <= K.
Archimedean integral int_0^{2L} f(x)dx, f = 2(e^{-2x}d - e^{-x/2}G(x))/(1-e^{-2x}) (removable singularity at 0):
  [0,eta]: Taylor series of f at 0 (acb_series, exact zero constant term of numerator dropped since G_ij(0)=d_ij),
           remainder <= eta*B*q^M/(1-q), q=eta/R, B = max|f| on |z|=R from a ball cover of the circle (Cauchy).
  [eta,2L]: acb.integral (rigorous adaptive Gauss-Legendre with error bounds).
Primes and pole term in closed form. All in ball arithmetic. Output exact (man,exp) midpoints and radii."""
import sys, math, time, pickle
from flint import arb, acb, acb_series, fmpq, ctx
def build(Lq, K, prec, M=110):
    ctx.prec=prec; ctx.cap=M+2
    L=arb(Lq); pi=arb.pi(); ks=[k for k in range(1,K+1) if k%2]; n=len(ks)
    al=[pi*k/(2*L) for k in ks]; amax=al[-1]
    R=arb(7)/amax; R=arb(min(float(R.mid()),1.0)); R=arb(R.mid()); eta=R/4
    def Gf(i,j,x,one):  # x may be arb/acb/acb_series; one = unit of that type
        def c(a1,a2,same):
            A=2*L*one-x
            def I(b,ph,zero): return A*ph.cos() if zero else ((b*A+ph).sin()-ph.sin())/b
            return (I(a1-a2,a1*x,same)-I(a1+a2,a1*x,False))/(2*L)
        return (c(al[i],al[j],i==j)+c(al[j],al[i],i==j))/2
    def f(i,j,x,one):
        d=1 if i==j else 0
        return 2*((-2*x).exp()*d-(-x/2).exp()*Gf(i,j,x,one))/(one-(-2*x).exp())
    c0=arb.const_euler()+pi.log()+(1-(-4*L).exp()).log()
    pr=[]
    for m in range(2,int(math.exp(2*float(Lq)))+2):
        p=next(q for q in range(2,m+1) if m%q==0); t=m
        while t%p==0: t//=p
        if t!=1: continue
        y=arb(m).log()
        if y<2*L: pr.append((y,2*arb(p).log()/arb(m).sqrt()))
        else: assert y>2*L
    def polev(a):
        s=arb(0)
        for c in (arb(1)/2,-arb(1)/2):
            F=lambda th:(c*th).exp()*(c*(a*th).sin()-a*(a*th).cos())/(c*c+a*a)
            s+=(F(2*L)-F(arb(0)))*(-c*L).exp()/2
        return s/L.sqrt()
    pv=[polev(a) for a in al]
    xs=acb_series([0,1]); NC=256
    A=[[None]*n for _ in range(n)]; t0=time.time()
    for i in range(n):
        for j in range(i,n):
            d=1 if i==j else 0
            num=2*((-2*xs).exp()*d-(-xs/2).exp()*Gf(i,j,xs,acb(1)))
            den=1-(-2*xs).exp()
            nc=num.coeffs(); dc=den.coeffs()
            q=acb_series(nc[1:])/acb_series(dc[1:])
            cf=q.coeffs()[:M]
            Ilow=sum((cf[m]*acb(eta)**(m+1)/(m+1) for m in range(len(cf))),acb(0)).real
            B=arb(0)
            for s in range(NC):
                z=acb(R*(2*pi*s/NC).cos(),R*(2*pi*s/NC).sin())
                zb=acb(arb(z.real.mid(),float((R*pi/NC*1.01).mid())),arb(z.imag.mid(),float((R*pi/NC*1.01).mid())))
                v=abs(f(i,j,zb,acb(1)))
                B=max(B,arb(v.mid()+v.rad()))
            qq=eta/R; rem=eta*B*qq**M/(1-qq)
            Ihi=acb.integral(lambda z,an:f(i,j,z,acb(1)),acb(eta),acb(2*L),rel_tol=arb(2)**(-prec+30),eval_limit=10**6,depth_limit=10**5).real
            arch=Ilow+Ihi+arb(0,float(rem.mid()+rem.rad())*1.000001)
            prime=sum((w*Gf(i,j,y,arb(1)) for y,w in pr),arb(0))
            A[i][j]=A[j][i]=-c0*d+arch-prime+2*pv[i]*pv[j]
    return A,n,time.time()-t0
if __name__=="__main__":
    Ls=sys.argv[1]; K=int(sys.argv[2]); prec=int(sys.argv[3])
    Lq=fmpq(*map(int,Ls.split('/')))
    A,n,sec=build(Lq,K,prec)
    me=lambda a:tuple(int(t) for t in a.man_exp())
    maxrad=max(float(A[i][j].rad()) for i in range(n) for j in range(n))
    print("L",Ls,"n",n,"time %.0fs"%sec,"max arb radius %.3e"%maxrad,flush=True)
    pickle.dump(dict(L=Ls,K=K,prec=prec,mid=[[me(A[i][j].mid()) for j in range(n)] for i in range(n)],
        rad=[[me(A[i][j].rad()) for j in range(n)] for i in range(n)]), open("/workspace/arb_%s.pkl"%Ls.replace('/','_'),"wb"))
