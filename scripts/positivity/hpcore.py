"""High-precision Weil form in Zhu's convention (arXiv 2608.24827, eq. 17): supp f in [-L,L], g = f*f~,
Q(f) = pole - (gamma+log pi+log(1-e^{-4L}))||f||^2 + int_0^{2L} 2(e^{-2x}||f||^2 - e^{-x/2} g(x))/(1-e^{-2x}) dx
       - sum_{log n<2L} 2 Lambda(n)/sqrt(n) g(log n);  pole = +2(int f cosh(x/2))^2 (even f), -2(int f sinh(x/2))^2 (odd f).
Basis: s_k(u)=sin(k pi (u+L)/(2L))/sqrt(L) (orthonormal); odd k -> even f, even k -> odd f. mpmath, not interval-certified."""
import mpmath as mp, math
def lam_list(L, jit=None, flip=(), extra=None):
    """list of (y=log n, weight 2Lambda(n)/sqrt n) with log n < 2L; optional fake sets."""
    if extra is not None: return extra
    N=int(math.exp(2*L))+1; out=[]
    for n in range(2,N+1):
        p=None
        for q in range(2,n+1):
            if n%q==0: p=q; break
        m=n
        while m%p==0: m//=p
        if m!=1: continue
        y=mp.log(n)
        if y>=2*L: continue
        w=2*mp.log(p)/mp.sqrt(n)
        if n in flip: w=-w
        if jit: y=y+jit.get(n,0)
        if 0<y<2*L: out.append((y,w))
    return out
def C(j,k,x,L):  # int s_j(u+x) s_k(u) du over overlap, x>=0 (normalised basis)
    aj=mp.pi*j/(2*L); ak=mp.pi*k/(2*L); A=2*L-x
    def I(b,ph): return A*mp.cos(ph) if b==0 else (mp.sin(b*A+ph)-mp.sin(ph))/b
    return (I(aj-ak,aj*x)-I(aj+ak,aj*x))/(2*L)
def G(j,k,x,L): return (C(j,k,x,L)+C(k,j,x,L))/2
def pole_vec(ks,L,odd):
    v=[]
    for k in ks:
        a=mp.pi*k/(2*L); s=0
        for c,sg in ((mp.mpf(1)/2,1),(-mp.mpf(1)/2,1 if not odd else -1)):
            F=lambda th: mp.e**(c*th)*(c*mp.sin(a*th)-a*mp.cos(a*th))/(c*c+a*a)
            s+=sg*(F(2*L)-F(0))*mp.e**(-c*L)/2
        v.append(s/mp.sqrt(L))
    return v
def form(L,K,odd=False,panels=None,nodes=None,**kw):
    ks=[k for k in range(1,K+1) if (k%2==0)==odd]; n=len(ks); L=mp.mpf(L)
    P=panels or max(4,int(K*float(L)/6)+2); nq=nodes or 40
    xs,ws=[],[]
    gx,gw=mp.gauss_legendre_nodes(nq) if hasattr(mp,'gauss_legendre_nodes') else _gl(nq)
    for p in range(P):
        a=2*L*p/P; b=2*L*(p+1)/P
        for x,w in zip(gx,gw): xs.append((a+b)/2+(b-a)/2*x); ws.append((b-a)/2*w)
    c0=mp.euler+mp.log(mp.pi)+mp.log(1-mp.e**(-4*L))
    pr=lam_list(float(L),**kw)
    kern=[(w*2/(1-mp.e**(-2*x)), mp.e**(-2*x), mp.e**(-x/2)) for x,w in zip(xs,ws)]
    M=mp.matrix(n,n)
    for i in range(n):
        for jj in range(i,n):
            j,k=ks[i],ks[jj]; d=1 if i==jj else 0
            arch=mp.fsum(kw_*(e2*d-eh*G(j,k,x,L)) for (kw_,e2,eh),x in zip(kern,xs))
            prime=mp.fsum(w*G(j,k,y,L) for y,w in pr)
            M[i,jj]=M[jj,i]=-c0*d+arch-prime
    v=pole_vec(ks,L,odd); s=-2 if odd else 2
    for i in range(n):
        for jj in range(n): M[i,jj]+=s*v[i]*v[jj]
    return M,ks
_glc={}
def _gl(n):
    if n in _glc: return _glc[n]
    xs,ws=[],[]
    for i in range(1,n+1):
        x=mp.cos(mp.pi*(i-mp.mpf(1)/4)/(n+mp.mpf(1)/2))
        for _ in range(100):
            p0,p1=mp.mpf(1),x
            for m in range(2,n+1): p0,p1=p1,((2*m-1)*x*p1-(m-1)*p0)/m
            dp=n*(x*p1-p0)/(x*x-1); dx=p1/dp; x-=dx
            if abs(dx)<mp.mpf(10)**(-mp.mp.dps+5): break
        p0,p1=mp.mpf(1),x
        for m in range(2,n+1): p0,p1=p1,((2*m-1)*x*p1-(m-1)*p0)/m
        dp=n*(x*p1-p0)/(x*x-1); xs.append(x); ws.append(2/((1-x*x)*dp*dp))
    _glc[n]=(xs,ws); return xs,ws
def eig(M):
    E,Q=mp.eigsy(M); idx=sorted(range(len(E)),key=lambda i:E[i])
    return [E[i] for i in idx],[Q[:,i] for i in idx]
