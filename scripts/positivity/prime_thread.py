"""Where rational primes enter the modular surface. UNCERTIFIED floating point (mpmath)."""
import math, mpmath as mp
from collections import Counter
from arith_horizon import narrow_classes, fundamental
mp.mp.dps=30
out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
def kron(D,n):  # Kronecker symbol (D/n), n>0
    r=1
    while n%2==0:
        n//=2
        if D%2==0: return 0
        if D%8 in (3,5): r=-r
    if n==1: return r
    a=D%n
    while a:
        while a%2==0:
            a//=2
            if n%8 in (3,5): r=-r
        a,n=n,a
        if a%4==3 and n%4==3: r=-r
        a%=n
    return r if n==1 else 0
def fundamental_disc(D):
    if D%4==1: return all(D%(q*q) for q in range(3,math.isqrt(D)+1,2))
    if D%4==0:
        m=D//4; return m%4 in (2,3) and all(m%(q*q) for q in range(3,math.isqrt(m)+1,2))
    return False
P("== 1. Class number formula h+(D) log eps+(D) = sqrt(D) L(1,chi_D), fundamental D ==")
P("D  h+  eps+=(t+u sqrtD)/2  lhs  rhs  |diff|")
worst=0
for D in [d for d in range(5,400) if fundamental_disc(d)]:
    f=fundamental(D)
    if f is None: continue
    h=narrow_classes(D); t,u=f; eps=(t+u*math.sqrt(D))/2
    L=-sum(kron(D,a)*mp.log(mp.sin(mp.pi*a/D)) for a in range(1,D))/mp.sqrt(D)
    lhs=h*math.log(eps); rhs=float(mp.sqrt(D)*L); worst=max(worst,abs(lhs-rhs))
    if D<60: P(D,h,round(eps,4),round(lhs,8),round(rhs,8),"%.1e"%abs(lhs-rhs))
P("worst |diff| over fundamental D<400 (Pell u<1e6): %.1e"%worst)
P("So multiplicity x length = sqrt(D) L(1,chi_D) = sqrt(D) prod_p (1-chi_D(p)/p)^{-1}:")
P("rational primes enter through how they split in Q(sqrt D).")
P("\n== 2. Frobenius of geodesics mod p (Chebotarev in SL2(F_p)) ==")
T=300; prim=Counter()
for t in range(3,T+1):
    n=t*t-4
    for u in range(1,math.isqrt(n)+1):
        if n%(u*u): continue
        D=n//(u*u)
        if D%4 not in (0,1) or math.isqrt(D)**2==D: continue
        if fundamental(D)==(t,u): prim[t]+=narrow_classes(D)
tot=sum(prim.values())
P("weighted by multiplicity, t<=%d (%d geodesics). split=(t^2-4|p)=+1, inert=-1, t=+-2 mod p"%(T,tot))
for p in (3,5,7,11,13):
    c=Counter()
    for t,m in prim.items():
        c[kron(t*t-4,p) if (t*t-4)%p else 0]+=m
    g=p*(p*p-1)
    P("p=%2d split %.3f (SL2(F_p) %.3f) inert %.3f (%.3f) t=+-2 %.3f (%.3f)"%(p,c[1]/tot,p*(p+1)*(p-3)/2/g,c[-1]/tot,p*(p-1)**2/2/g,c[0]/tot,2*p*p/g))
P("(slow convergence; agreement approximate, uncertified)")
P("\n== 3. Hecke: not computed (needs Maass eigenfunctions). T_p acts via the p+1 index-p")
P("sublattices; these are the arithmetic 'pseudo-symmetries' (Bogomolny et al.).")
P("\n== 4. Scattering phi(s)=sqrt(pi)G(s-1/2)zeta(2s-1)/(G(s)zeta(2s)) ==")
phi=lambda s: mp.sqrt(mp.pi)*mp.gamma(s-0.5)*mp.zeta(2*s-1)/(mp.gamma(s)*mp.zeta(2*s))
for tt in (3,10,25.7): P("unitarity |phi(1/2+%si)| = %s"%(tt,mp.nstr(abs(phi(mp.mpc(0.5,tt))),15)))
P("poles at s=rho/2 (zeta(2s)=0):")
for n in range(1,6):
    g=mp.im(mp.zetazero(n)); s0=mp.mpc(0.25,g/2)
    P("gamma_%d=%s  s=1/4+%si  |phi(s+1e-6)|=%s  |phi(s+0.05)|=%s"%(n,mp.nstr(g,10),mp.nstr(g/2,10),
      mp.nstr(abs(phi(s0+1e-6)),4),mp.nstr(abs(phi(s0+0.05)),4)))
P("Resonances of PSL2Z\\H = {rho/2} (+ trivial): all on Re s=1/4 iff RH. Restatement, not leverage:")
P("the scattering problem is non-self-adjoint, so no spectral theorem forces the line.")
open("prime_thread_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
