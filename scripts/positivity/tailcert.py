"""Zhu-style full-window certificate, even sector, Legendre basis T_n(x)=Pbar_n(x/L)/sqrt(L), n even.
Reduced form (Zhu Thm 1.1): R(f) = 2F(i/2)^2 + (1/pi) int_0^{T#} (Psi_L - beta*) |F|^2 dt + beta* ||f||^2 <= Q(f),
beta* = log(T#/2pi) - 1/T# - A_L.  Matrix: R_nm = beta* d_nm + 2 p_n p_m + C_nm,
That_n(t) = (-1)^{n/2} 2 sqrt(L nu_n) j_n(tL), p_n = 2 sqrt(L nu_n) i_n(L/2), nu_n = n+1/2.
Head entries by acb.integral (rigorous); tail via |j_n(x)| <= x^n/(2n+1)!!, i_n(z) <= z^n cosh z/(2n+1)!!."""
import sys, math, time, pickle
from flint import arb, acb, fmpq, ctx
from multiprocessing import Pool
Lq=fmpq(1,2); TS=30; PREC=256
def setup():
    ctx.prec=PREC
    g=dict(L=arb(Lq),T=arb(TS),pi=arb.pi())
    L=g['L']; pr=[]
    for m in range(2,int(math.exp(2*float(Lq)))+2):
        p=next(q for q in range(2,m+1) if m%q==0); t=m
        while t%p==0: t//=p
        if t==1 and arb(m).log()<2*L: pr.append((m,p))
    g['pr']=pr; g['A']=sum((2*arb(p).log()/arb(m).sqrt() for m,p in pr),arb(0))
    g['beta']=(g['T']/(2*g['pi'])).log()-1/g['T']-g['A']
    return g
def dfact(n): # (2n+1)!!
    r=1
    for k in range(1,2*n+2,2): r*=k
    return r
def jn(n,z):  # spherical bessel, z acb
    return z**n/dfact(n)*(-z*z/4).hypgeom_0f1(acb(n)+acb(3)/2)
def That(n,t,g): return (-1)**(n//2)*2*(g['L']*(n+arb(1)/2)).sqrt()*jn(n,t*g['L'])
def Psi(t,g):
    s=((acb(1)/4+t*acb(0,1)/2).digamma()+(acb(1)/4-t*acb(0,1)/2).digamma())/2-g['pi'].log()
    for m,p in g['pr']: s-=2*arb(p).log()/arb(m).sqrt()*(t*arb(m).log()).cos()
    return s
def entry(a):
    n,m=a; g=setup()
    f=lambda t,an: (Psi(t,g)-g['beta'])*That(n,t,g)*That(m,t,g)
    I=acb.integral(f,acb(0),acb(g['T']),rel_tol=arb(2)**(-120),eval_limit=10**7)
    v=I.real/g['pi']; return n,m,(tuple(int(t) for t in v.mid().man_exp()),tuple(int(t) for t in v.rad().man_exp()))
def pole(n,g): z=acb(g['L']/2); return (2*(g['L']*(n+arb(1)/2)).sqrt()*(z**n/dfact(n)*(z*z/4).hypgeom_0f1(acb(n)+acb(3)/2))).real
if __name__=="__main__":
    H=int(sys.argv[1]); par=int(sys.argv[2]) if len(sys.argv)>2 else 0; g=setup()
    print("A_L",g['A'],"beta*",g['beta'],flush=True)
    ords=[2*i+par for i in range(H)]; sg=-1 if par else 1; t0=time.time()
    tasks=[(ords[i],ords[j]) for i in range(H) for j in range(i,H)]
    with Pool(7) as P: res=P.map(entry,tasks,chunksize=4)
    mk=lambda a,b: arb(fmpq(a[0])*fmpq(2)**a[1] if a[1]>=0 else fmpq(a[0],2**(-a[1])), fmpq(b[0])*fmpq(2)**b[1] if b[1]>=0 else fmpq(b[0],2**(-b[1])))
    C={(n,m):mk(*v) for n,m,v in res}
    p=[pole(n,g) for n in ords]
    Rm=[[None]*H for _ in range(H)]
    for i in range(H):
        for j in range(i,H):
            v=C[(ords[i],ords[j])]+sg*2*p[i]*p[j]+(g['beta'] if i==j else 0); Rm[i][j]=Rm[j][i]=v
    me=lambda a:tuple(int(t) for t in a.man_exp())
    print("time %.0f maxrad %.2e"%(time.time()-t0,max(float(Rm[i][j].rad()) for i in range(H) for j in range(H))))
    pickle.dump(dict(H=H,mid=[[me(Rm[i][j].mid()) for j in range(H)] for i in range(H)],rad=[[me(Rm[i][j].rad()) for j in range(H)] for i in range(H)],
                     beta=me(g['beta'].mid()),beta_rad=me(g['beta'].rad()),prec=PREC),open(f"/workspace/tail_L05_H{H}"+("_odd" if par else "")+".pkl","wb"))
