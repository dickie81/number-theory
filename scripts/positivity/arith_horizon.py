"""Arithmetic horizons: closed geodesics of PSL(2,Z)\\H as BTZ-type horizons.
UNCERTIFIED floating-point numerics. Maass r_j are quoted literature values
(Hejhal / Then), transcribed, not recomputed here."""
import math
from collections import Counter

def isqrt(n): return math.isqrt(n)

def narrow_classes(D):
    """# SL2Z classes of primitive forms of non-square disc D>0 (cycles of reduced forms)."""
    s = math.sqrt(D); forms=set()
    for b in range(1, int(s)+1):
        if (b*b-D)%4: continue
        ac=(b*b-D)//4
        for a in range(1, abs(ac)+1):
            if ac % a: continue
            for A in (a,-a):
                C=ac//A
                if math.gcd(math.gcd(A,b),C)!=1: continue
                if 0<b<s and s-b<2*abs(A)<s+b: forms.add((A,b,C))
    seen=set(); cyc=0
    for f in forms:
        if f in seen: continue
        cyc+=1; g=f
        while g not in seen:
            seen.add(g); a,b,c=g
            # rho: (a,b,c)->(c,b',*) with b'≡-b mod 2c, s-2|c|<b'<s
            m=2*abs(c); bp=-b % m
            while bp< s-m: bp+=m
            while bp> s: bp-=m
            g=(c,bp,(bp*bp-D)//(4*c))
    return cyc

def fundamental(D):
    for u in range(1,10**6):
        t2=D*u*u+4; t=isqrt(t2)
        if t*t==t2: return t,u

def _main():
    T=300
    prim=Counter()
    for t in range(3,T+1):
        n=t*t-4
        for u in range(1,isqrt(n)+1):
            if n%(u*u): continue
            D=n//(u*u)
            if D%4 not in (0,1) or isqrt(D)**2==D: continue
            if fundamental(D)==(t,u): prim[t]+=narrow_classes(D)
    out=[]
    P=lambda *a: out.append(" ".join(str(x) for x in a))
    P("== Primitive closed geodesics on PSL(2,Z)\\H, trace t<=%d =="%T)
    P("t  length=2arccosh(t/2)  mult  N=eps^2  nearest-int  |logN-log p| (p prime nearest N)")
    def isprime(n): return n>1 and all(n%k for k in range(2,isqrt(n)+1))
    for t in range(3,16):
        L=2*math.acosh(t/2); N=math.exp(L); k=round(N)
        p=min((q for q in range(2,k+40) if isprime(q)),key=lambda q:abs(q-N))
        P(t, round(L,6), prim[t], round(N,6), k, round(abs(L-math.log(p)),4))
    P("N_t = eps^2 = ((t+sqrt(t^2-4))/2)^2 is a quadratic irrational (t>=3): never a rational prime;")
    P("log N = log p would need N = p in Q, impossible. lengths ~ 2 log t, not log p.")
    # prime geodesic theorem
    P("\n== Prime geodesic theorem: pi_G(x) = #{N<=x} vs Li(x) ==")
    def Li(x):
        s=0;n=200000;a=2.0
        h=(x-a)/n
        return sum(h/math.log(a+(i+.5)*h) for i in range(n))
    for X in (1e2,1e3,1e4,1e4*9):
        c=sum(m for t,m in prim.items() if ((t+math.sqrt(t*t-4))/2)**2<=X)
        P("x=%g pi_G=%d Li=%.1f ratio=%.3f"%(X,c,Li(X),c/Li(X)))
    mults=[prim[t] for t in range(3,T+1)]
    P("mean multiplicity over t<=%d: %.2f, max %d (exponential degeneracy grows ~ e^{L/2}/L)"%(T,sum(mults)/len(mults),max(mults)))
    # Maass vs zeta
    r=[9.53369526,12.17300832,13.77975135,14.35850951,16.13807317,16.64425920,17.73856338,
       18.18091783,19.42348147,19.48471385,20.10669468,21.31579594,21.47905643,22.19467106,
       22.78590849,23.20139618,23.26371470,24.11235273,24.41971380,25.05085494]
    z=[14.134725,21.022040,25.010858,30.424876,32.935062,37.586178,40.918719,43.327073,48.005151,49.773832]
    P("\n== Maass r_j (PSL2Z, literature) vs zeta zeros gamma_n ==")
    P("min |r_j - gamma_n| over pairs:",round(min(abs(a-b) for a in r for b in z),4),
      "(expected for random sets of this density ~0.1; no alignment)")
    P("ratios r_j/gamma_1:",[round(a/z[0],3) for a in r[:6]])
    # spacing stats, Weyl unfolding N(r)~ r^2/12
    u=sorted(x*x/12 for x in r); s=[u[i+1]-u[i] for i in range(len(u)-1)]; m=sum(s)/len(s); s=[x/m for x in s]
    small=sum(1 for x in s if x<0.3)/len(s)
    P("unfolded spacings (Weyl r^2/12): fraction s<0.3 = %.2f  [Poisson 0.26, GOE 0.07, GUE 0.03]"%small)
    P("  n=%d only: weak evidence; literature (Bogomolny et al., Steil) finds Poisson on 1000s of levels."%len(s))
    uz=[]  # zeta unfolding N(g)~g/2pi log(g/2pi e)
    uz=[g/(2*math.pi)*math.log(g/(2*math.pi*math.e)) for g in z]
    sz=[uz[i+1]-uz[i] for i in range(len(uz)-1)]; mz=sum(sz)/len(sz)
    P("zeta first-10 unfolded: fraction s<0.3 = %.2f (GUE-like repulsion)"%(sum(1 for x in sz if x/mz<0.3)/len(sz)))
    # horizons
    P("\n== BTZ horizons from geodesics (AdS radius 1): circumference 2pi r+ = length, T_H = r+/2pi ==")
    for t in range(3,9):
        L=2*math.acosh(t/2); P("t=%d  r+=%.5f  T_H=%.6f"%(t,L/(2*math.pi),L/(4*math.pi**2)))
    P("Prime family Gamma_p=<diag(p^1/2,p^-1/2)>: each cyclic, discrete, BTZ with length log p, T_p=log p/4pi^2.")
    P("  but p is put in by hand (tautological). Joint group <all Gamma_p> is abelian with lengths")
    P("  {a log2+b log3+...}: dense in R (log p rationally independent) => NOT discrete, no quotient manifold.")
    best=min((abs(a*math.log(2)-b*math.log(3)),a,b) for a in range(1,2000) for b in range(1,1300))
    P("  e.g. min |a log2 - b log3| for a<2000: %.2e at (a,b)=(%d,%d) -> translation lengths accumulate at 0"%best)
    open("arith_horizon_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
if __name__=="__main__": _main()
