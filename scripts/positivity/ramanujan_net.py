"""Same-dimension black-hole network = LPS Ramanujan graphs (Bruhat-Tits quotients).
UNCERTIFIED floating-point (numpy eigvalsh)."""
import numpy as np, math, itertools, random
out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
q=13
i0=next(x for x in range(q) if (x*x+1)%q==0)
def norm(M):
    a,b,c,d=[v%q for v in M]
    s=pow(a if a else b, -1, q)
    return tuple(v*s%q for v in (a,b,c,d))
def gens(p):
    G=[]
    r=int(math.isqrt(p))+1
    for a0 in range(1,r,2):
        for a1,a2,a3 in itertools.product(range(-2*(r//2),2*(r//2)+1,2),repeat=3):
            if a0*a0+a1*a1+a2*a2+a3*a3==p: G.append(norm((a0+a1*i0,a2+a3*i0,-a2+a3*i0,a0-a1*i0)))
    assert len(G)==p+1,(p,len(G)); return G
def mul(A,B):
    a,b,c,d=A; e,f,g,h=B
    return norm((a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h))
# vertices = PGL(2,q) (projective), size q(q^2-1)
V=sorted({norm((a,b,c,d)) for a in range(q) for b in range(q) for c in range(q) for d in range(q) if (a*d-b*c)%q})
idx={v:k for k,v in enumerate(V)}; n=len(V)
def adj(p):
    A=np.zeros((n,n))
    for g in gens(p):
        for v in V: A[idx[v],idx[mul(g,v)]]+=1
    return A
def report(name,A,p):
    ev=np.sort(np.linalg.eigvalsh(A)); d=p+1
    triv=np.isclose(np.abs(ev),d,atol=1e-8); nt=ev[~triv]
    lam=np.max(np.abs(nt)); bound=2*math.sqrt(p)
    # Ihara poles: 1 - lam u + p u^2 = 0
    us=np.concatenate([np.roots([p,-l,1]) for l in nt])
    dev=np.max(np.abs(np.abs(us)-p**-0.5))
    P("%-28s n=%d deg=%d trivial=%d max|lam_nontriv|=%.4f 2sqrt(p)=%.4f Ramanujan=%s max||u|-p^-1/2|=%.1e"%(name,len(ev),d,triv.sum(),lam,bound,lam<=bound+1e-9,dev))
    return ev
P("== 1. LPS X^{p,%d} on PGL(2,%d) (bipartite if (p|q)=-1) =="%(q,q))
A={}
for p in (5,17,29):
    A[p]=adj(p); assert np.allclose(A[p].sum(1),p+1); report("LPS X^{%d,%d}"%(p,q),A[p],p)
rng=random.Random(0)
def random_regular(n,d):
    while True:
        stubs=[v for v in range(n) for _ in range(d)]; rng.shuffle(stubs)
        M=np.zeros((n,n)); ok=True
        for a,b in zip(stubs[::2],stubs[1::2]):
            if a==b or M[a,b]: ok=False;break
            M[a,b]=M[b,a]=1
        if ok: return M
R=random_regular(n,6); report("random 6-regular (Friedman)",R,5)
P("\n== 2. Two primes on one quotient: Hecke operators A_5, A_17 ==")
P("commute: max|[A5,A17]| = %.1e"%np.max(np.abs(A[5]@A[17]-A[17]@A[5])))
H=A[5]+math.pi*A[17]/10; w,U=np.linalg.eigh(H)
l5=np.einsum('ij,ik,kj->j',U,A[5],U); l17=np.einsum('ij,ik,kj->j',U,A[17],U)
nt=~(np.isclose(np.abs(l5),6)|np.isclose(np.abs(l17),18))
P("joint eigenvectors: %d nontrivial; max|l5|=%.4f (<=%.4f), max|l17|=%.4f (<=%.4f): both Ramanujan simultaneously"%(nt.sum(),np.max(np.abs(l5[nt])),2*5**.5,np.max(np.abs(l17[nt])),2*17**.5))
P("Satake angles l_p=2sqrt(p)cos(theta_p): sample (theta_5,theta_17) in degrees:",
  sorted({(round(math.degrees(math.acos(a/(2*5**.5))),1),round(math.degrees(math.acos(b/(2*17**.5))),1)) for a,b in zip(l5[nt],l17[nt])})[:6], '(distinct pairs; eigenspaces are degenerate)')
s=0.5+14.1347j
k=np.where(nt)[0][0]
Lpart=1/((1-l5[k]*5**-s+5**(1-2*s))*(1-l17[k]*17**-s+17**(1-2*s)))
P("partial L(s)=prod_{p=5,17}(1-l_p p^-s+p^{1-2s})^-1 at s=1/2+14.13i: |L|=%.3f (just a 2-factor Euler product; no zeros forced)"%abs(Lpart))
P("Ramanujan at every p = Ramanujan-Petersson for this automorphic form; it is a theorem here (LPS via Deligne),")
P("and it says nothing about zeta's zeros: that needs the archimedean place.")
P("\n== 3. Bad gluing: two copies of X^{5,%d} joined by k double-edge swaps (stays 6-regular) =="%q)
B=A[5]
for k in (1,3,10,30,100,300,1000):
    M=np.zeros((2*n,2*n)); M[:n,:n]=B; M[n:,n:]=B
    edges=[(a,b) for a in range(n) for b in range(a+1,n) if B[a,b]>0]
    for (a,b) in rng.sample(edges,k):
        M[a,b]-=1;M[b,a]-=1;M[n+a,n+b]-=1;M[n+b,n+a]-=1
        M[a,n+b]+=1;M[n+b,a]+=1;M[n+a,b]+=1;M[b,n+a]+=1
    ev=np.sort(np.linalg.eigvalsh(M)); nt=ev[~np.isclose(np.abs(ev),6,atol=1e-8)]
    l=np.max(np.abs(nt)); margin=2*5**.5-l
    P("k=%5d  max|lam_nontriv|=%.4f  margin 2sqrt5-lam=%+.4f  %s"%(k,l,margin,"RH ok" if margin>=0 else "RH FAILS (Ihara pole off |u|=5^-1/2)"))
open("ramanujan_net_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
