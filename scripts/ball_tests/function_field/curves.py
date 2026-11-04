"""Hyperelliptic curves over F_q and their L-polynomials by point counting over F_{q^i}, i<=g."""
import itertools, random
def factor_pp(q):
    for p in range(2, q+1):
        if q % p == 0:
            n, t = 0, q
            while t % p == 0: t//=p; n+=1
            return p, n
class GF:
    """F_{p^n} with elements as ints 0..Q-1 (base-p digits), via exp/log tables."""
    def __init__(self, p, n):
        self.p, self.n, self.Q = p, n, p**n
        Q = self.Q
        for mod in itertools.product(range(p), repeat=n):  # monic x^n + mod
            exp=[0]*(Q-1); x=[1]+[0]*(n-1); ok=True; seen=set()
            for i in range(Q-1):
                v=sum(c*p**k for k,c in enumerate(x))
                if v in seen or v==0: ok=False; break
                seen.add(v); exp[i]=v
                # multiply by X
                top=x[-1]; x=[0]+x[:-1]
                x=[(x[k]-top*mod[k])%p for k in range(n)]
            if ok and len(seen)==Q-1: break
        self.exp=exp+exp; self.log=[None]*Q
        for i in range(Q-1): self.log[exp[i]]=i
    def add(self,a,b):
        p=self.p; r=0; m=1
        while a or b: r+=((a%p+b%p)%p)*m; a//=p; b//=p; m*=p
        return r
    def mul(self,a,b):
        if a==0 or b==0: return 0
        return self.exp[self.log[a]+self.log[b]]
def embed_tables(Fq, FQ):
    """map F_q -> F_Q (q^i): element of order dividing q-1 via exp: g_Q^((Q-1)/(q-1)) generates F_q^*, match by minimal relation:
    we match via additive structure: find subfield {x: x^q=x} and an iso by sending generator to a root of Fq's modulus."""
    q, Q = Fq.Q, FQ.Q
    sub=[x for x in range(Q) if x==0 or (FQ.log[x]*q)%(Q-1)==FQ.log[x]]
    # brute iso: pick image of Fq generator exp[1] among sub elements of order q-1, check additivity
    gq=Fq.exp[1]
    for cand in sub:
        if cand==0: continue
        if (Q-1)//__import__('math').gcd(Q-1,FQ.log[cand])!=q-1: continue
        mp={0:0}
        for i in range(q-1): mp[Fq.exp[i]]=FQ.exp[(FQ.log[cand]*i)%(Q-1)]
        if all(mp[Fq.add(a,b)]==FQ.add(mp[a],mp[b]) for a in range(q) for b in range(q)):
            return [mp[a] for a in range(q)]
    raise RuntimeError
_cache={}
def field(Q):
    if Q not in _cache: _cache[Q]=GF(*factor_pp(Q))
    return _cache[Q]
def addtab(Fl):
    Q=Fl.Q; return [[Fl.add(a,b) for b in range(Q)] for a in range(Q)]
_at={}
def count(q, i, f, h):
    """#C(F_{q^i}) for y^2 + h y = f (coeff lists low->high over F_q), deg f = 2g+1, one point at infinity."""
    Q=q**i; FQ=field(Q); Fq=field(q)
    emb = list(range(q)) if i==1 else embed_tables(Fq,FQ)
    if Q not in _at: _at[Q]=addtab(FQ)
    AT=_at[Q]; mul=FQ.mul
    fe=[emb[c] for c in f]; he=[emb[c] for c in h]
    def ev(c,x):
        r=0
        for a in reversed(c): r=AT[mul(r,x)][a]
        return r
    p=FQ.p; N=1
    if p!=2:
        for x in range(Q):
            v=ev(fe,x)
            if v==0: N+=1
            elif FQ.log[v]%2==0: N+=2
    else:
        # trace F_Q -> F_2 : sum of x^(2^k)
        def tr(z):
            t=0; w=z
            for _ in range(FQ.n): t=AT[t][w]; w=mul(w,w)
            return t
        for x in range(Q):
            hv=ev(he,x); fv=ev(fe,x)
            if hv==0: N+=1
            else:
                z=mul(fv, FQ.exp[(-2*FQ.log[hv])%(Q-1)])
                N+= 2 if tr(z)==0 else 0
    return N
def lpoly(q,g,f,h):
    Ns=[count(q,i,f,h) for i in range(1,g+1)]
    s=[q**i+1-Ns[i-1] for i in range(1,g+1)]  # power sums of alpha
    # Newton -> e_k, coefficients c_k=(-1)^k e_k
    e=[1]
    for k in range(1,g+1):
        v=sum((-1)**(j-1)*e[k-j]*s[j-1] for j in range(1,k+1))
        assert v%k==0; e.append(v//k)
    c=[(-1)**k*e[k] for k in range(g+1)]
    c+= [q**(g-k)*c[k] for k in range(g-1,-1,-1)]
    return c, Ns
def rh_ok(c,q):
    """|alpha_j| = sqrt(q) for every root, at 60 digits: a root of multiplicity m is only accurate to about
    eps^(1/m), so double precision rejects valid L-polynomials with repeated roots, such as (1 + qT^2)^3."""
    import mpmath as mp
    with mp.workdps(60):
        r = mp.polyroots([mp.mpf(x) for x in c[::-1]], maxsteps=500, extraprec=400)  # roots of P are 1/alpha
        return all(abs(abs(z)*mp.sqrt(q) - 1) < mp.mpf(10)**-12 for z in r)
def _neg(F, a):
    p=F.p; r=0; m=1
    while a: r+=((-(a%p))%p)*m; a//=p; m*=p
    return r
def _inv(F, a): return F.exp[(F.Q-1-F.log[a])%(F.Q-1)]
def _trim(f):
    while f and f[-1]==0: f=f[:-1]
    return f
def _deriv(F, f):
    """f' over F_q: the coefficient k*c_k, with k acting through F_p (digitwise)."""
    p=F.p; out=[]
    for k in range(1,len(f)):
        a=f[k]; r=0; m=1; km=k%p
        while a: r+=((a%p)*km%p)*m; a//=p; m*=p
        out.append(r)
    return _trim(out)
def _pmul(F, f, g):
    if not f or not g: return []
    r=[0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g): r[i+j]=F.add(r[i+j],F.mul(a,b))
    return _trim(r)
def _padd(F, f, g):
    n=max(len(f),len(g)); f=f+[0]*(n-len(f)); g=g+[0]*(n-len(g))
    return _trim([F.add(a,b) for a,b in zip(f,g)])
def _pmod(F, f, g):
    f=_trim(list(f)); g=_trim(list(g)); il=_inv(F,g[-1])
    while len(f)>=len(g):
        c=F.mul(f[-1],il); sh=len(f)-len(g)
        for i,b in enumerate(g): f[i+sh]=F.add(f[i+sh],_neg(F,F.mul(c,b)))
        f=_trim(f)
    return f
def _pgcd_deg(F, f, g):
    f=_trim(list(f)); g=_trim(list(g))
    while g: f,g=g,_pmod(F,f,g)
    return len(f)-1
def nonsingular(q, f, h):
    """The affine model y^2 + h y = f is smooth (f monic of odd degree 2g+1, so the point at infinity is too).
    Odd p (h = 0): f squarefree, gcd(f, f') = 1. Characteristic 2: a singular point has h(x) = 0, h'(x)y = f'(x) and
    y^2 = f(x), so it exists exactly when gcd(h, f'^2 + f h'^2) is not constant."""
    F=field(q); f=_trim(list(f)); h=_trim(list(h))
    if F.p!=2: return _pgcd_deg(F, f, _deriv(F,f))==0
    fd=_deriv(F,f); hd=_deriv(F,h)
    return _pgcd_deg(F, h, _padd(F, _pmul(F,fd,fd), _pmul(F,f,_pmul(F,hd,hd))))==0
def random_curve(q,g,rng):
    p,_=factor_pp(q)
    f=[rng.randrange(q) for _ in range(2*g+1)]+[1]
    h=[rng.randrange(q) for _ in range(g+1)] if p==2 else [0]
    if p==2 and all(x==0 for x in h): h[0]=1
    return f,h
