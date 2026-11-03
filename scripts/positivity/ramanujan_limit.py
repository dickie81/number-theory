"""Limits of Ramanujan black-hole networks. UNCERTIFIED floating point (numpy/mpmath)."""
import numpy as np, math, itertools, mpmath as mp
out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
def lps_moments(p,q,K):
    i0=next(x for x in range(q) if (x*x+1)%q==0)
    def norm(M):
        a,b,c,d=[v%q for v in M]; s=pow(a if a else b,-1,q); return tuple(v*s%q for v in (a,b,c,d))
    r=math.isqrt(p)+1; e=2*(r//2); G=[]
    for a0 in range(1,r,2):
        for a1,a2,a3 in itertools.product(range(-e,e+1,2),repeat=3):
            if a0*a0+a1*a1+a2*a2+a3*a3==p: G.append(norm((a0+a1*i0,a2+a3*i0,-a2+a3*i0,a0-a1*i0)))
    assert len(G)==p+1
    mul=lambda A,B: norm((A[0]*B[0]+A[1]*B[2],A[0]*B[1]+A[1]*B[3],A[2]*B[0]+A[3]*B[2],A[2]*B[1]+A[3]*B[3]))
    # closed walks at identity via distribution over group elements (vertex-transitive => tr A^k / n)
    I=norm((1,0,0,1)); dist={I:1}; m=[]
    for k in range(1,K+1):
        nd={}
        for v,c in dist.items():
            for g in G:
                w=mul(g,v); nd[w]=nd.get(w,0)+c
        dist=nd; m.append(dist.get(I,0))
    return m
def tree_moments(d,K):
    # closed walks at root of d-regular tree, by distance distribution
    v=[1]+[0]*(K+1); m=[]
    for k in range(1,K+1):
        w=[0]*(K+2)
        for j,c in enumerate(v[:-1]):
            if not c: continue
            if j==0: w[1]+=d*c
            else: w[j-1]+=c; w[j+1]+=(d-1)*c
        v=w; m.append(v[0])
    return m
P("== 1a. Size limit: closed-walk moments m_k = tr(A^k)/n of LPS X^{5,q} vs 6-regular tree (Kesten-McKay) ==")
K=12; T=tree_moments(6,K); P("tree      m_2..m_12 (even):",T[1::2])
for q in (13,17,29,37,41):
    m=lps_moments(5,q,K)
    first=next((k+1 for k in range(K) if m[k]!=T[k]),None)
    P("q=%2d      m_2..m_12 (even): %s  first deviation at k=%s (girth-type effect; grows ~ log q)"%(q,m[1::2],first))
P("Moments agree up to k ~ girth, which grows with q, so spectral measure -> Kesten-McKay (weak convergence).")
# 1b. Sato-Tate for 11a: y^2+y=x^3-x^2-10x-20
def ap_11a(p):
    if p in (2,11): return None
    x=np.arange(p,dtype=np.int64); rhs=(x**3-x*x-10*x-20)%p
    # y^2+y=rhs  <=> (2y+1)^2 = 4rhs+1
    D=(4*rhs+1)%p
    sq=np.zeros(p,dtype=np.int64); sq[(x*x)%p]=1
    nsol=np.where(D==0,1,np.where(sq[D]==1,2,0)).sum()
    return p-nsol
def primes(n):
    s=np.ones(n+1,bool); s[:2]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=0
    return np.nonzero(s)[0]
PR=[int(p) for p in primes(30000) if p not in (2,11)]
A={p:ap_11a(p) for p in PR}
viol=[p for p in PR if abs(A[p])>2*math.sqrt(p)]
th=np.array([math.acos(A[p]/(2*math.sqrt(p))) for p in PR])
P("\n== 1b. Hecke angles for 11a (S_2(Gamma_0(11))), %d primes < 30000 =="%len(PR))
P("Hasse/Ramanujan |a_p|<=2sqrt p violations:",len(viol))
P("a_2..: a_3=%d a_5=%d a_7=%d a_13=%d (LMFDB 11.a2: -1,1,-2,4)"%(A[3],A[5],A[7],A[13]))
for k in (2,4,6):
    P("E[(2cos th)^%d] = %.3f   Sato-Tate (Catalan) %d"%(k,np.mean((2*np.cos(th))**k),math.comb(k,k//2)//(k//2+1)))
P("(p-adic Plancherel at fixed p would instead give the Kesten-McKay law; Sato-Tate is its p->inf limit.)")
P("\n== 2. L(11a,s): finite-prime Ramanujan holds, zeros need the archimedean Gamma factor ==")
mp.mp.dps=20; N=11; Mx=400
an=[0]*(Mx+1); an[1]=1
for n in range(2,Mx+1):
    m=n; f={}
    p=2
    while p*p<=m:
        while m%p==0: f[p]=f.get(p,0)+1; m//=p
        p+=1
    if m>1: f[m]=f.get(m,0)+1
    v=1
    for p,e in f.items():
        a=-2 if p==2 else (1 if p==11 else A[p])
        if p==11: v*=a**e; continue
        b0,b1=1,a
        for _ in range(e-1): b0,b1=b1,a*b1-p*b0
        v*=b1 if e>=1 else 1
    an[n]=v
c=mp.sqrt(N)/(2*mp.pi)
def Lam(s):
    return sum(an[n]*(c**s*mp.gammainc(s,2*mp.pi*n/mp.sqrt(N))*mp.power(n,-s)+c**(2-s)*mp.gammainc(2-s,2*mp.pi*n/mp.sqrt(N))*mp.power(n,s-2)) for n in range(1,Mx+1) if an[n])
P("functional-equation check Lam(1.3+2i)-Lam(0.7-2i) =",mp.nstr(abs(Lam(mp.mpc(1.3,2))-Lam(mp.mpc(0.7,-2))),3),"(symmetric by construction; real test is the zero match below)")
ts=np.arange(0.2,20,0.05); vals=[float(mp.re(Lam(mp.mpc(1,t)))) for t in ts]
zs=[float(mp.findroot(lambda t: mp.re(Lam(mp.mpc(1,t))),(ts[i]+ts[i+1])/2)) for i in range(len(ts)-1) if vals[i]*vals[i+1]<0]
P("zeros of L(11a,1+it), t<20:",[round(z,4) for z in zs],"(LMFDB first zero 6.3626)")
P("These sit on Re s=1 because of the completed function Lam = (sqrt N/2pi)^s Gamma(s) L; the Euler product")
P("over finite primes alone (with Ramanujan at every p) does not control zero location.")
P("\nDavenport-Heilbronn: f = (1-ik)/2 L(s,chi) + (1+ik)/2 L(s,chibar), chi mod 5, |coeffs|<=1, satisfies a")
P("Riemann-type functional equation, but has no Euler product -> zeros OFF the line:")
k=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
chi=[0,1,1j,-1j,-1]; chib=[0,1,-1j,1j,-1]
f=lambda s: (1-1j*k)/2*mp.dirichlet(s,chi)+(1+1j*k)/2*mp.dirichlet(s,chib)
z=mp.findroot(f,mp.mpc(0.808,85.699))
P("DH zero found: s = %s  |f| = %s  (literature: 0.808517 + 85.699348i)"%(mp.nstr(z,10),mp.nstr(abs(f(z)),3)))
open("ramanujan_limit_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
