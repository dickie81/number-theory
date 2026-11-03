"""Weil's finite-field proof numerically: intersection Gram on C x C, signature, RH. UNCERTIFIED floats (counts exact)."""
import numpy as np, math, cmath
out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
def count(f, q, k=1):
    """#C(F_{q^k}) for y^2=f(x), q prime, k in {1,2}; smooth model with points at infinity (deg 3: 1, deg 5: 1)."""
    if k==1:
        sq=[0]*q
        for y in range(q): sq[y*y%q]+=1
        return sum(sq[sum(c*pow(x,i,q) for i,c in enumerate(f))%q] for x in range(q))+1
    # F_{q^2} = F_q[t]/(t^2-n), n non-residue
    n=next(a for a in range(2,q) if pow(a,(q-1)//2,q)==q-1)
    mul=lambda a,b: ((a[0]*b[0]+n*a[1]*b[1])%q,(a[0]*b[1]+a[1]*b[0])%q)
    sq={}
    for y0 in range(q):
        for y1 in range(q):
            s=mul((y0,y1),(y0,y1)); sq[s]=sq.get(s,0)+1
    tot=0
    for x0 in range(q):
        for x1 in range(q):
            x=(x0,x1); v=(0,0); p=(1,0)
            for c in f:
                v=((v[0]+c*p[0])%q,(v[1]+c*p[1])%q); p=mul(p,x)
            tot+=sq.get(v,0)
    return tot+1
def gram(q,g,N):
    return np.array([[0,1,1,1],[1,0,1,q],[1,1,2-2*g,N],[1,q,N,q*(2-2*g)]],float)
cases=[("E: y^2=x^3+x+1",[1,1,0,1],1,(23,101)),("E: y^2=x^3-x",[0,-1,0,1],1,(29,103)),
       ("g=2: y^2=x^5+x+3",[3,1,0,0,0,1],2,(13,31))]
P("curve | q | N1 N2 | |N1-q-1| <= 2g sqrt q | Gram signature (+,-,0) on <e1,e2,Delta,Gamma> | |alpha_i|/sqrt q")
for name,f,g,qs in cases:
    for q in qs:
        N1=count(f,q); N2=count(f,q,2)
        ev=np.linalg.eigvalsh(gram(q,g,N1)); tol=1e-9*np.max(abs(ev))
        sig=(int((ev>tol).sum()),int((ev<-tol).sum()),int((abs(ev)<=tol).sum()))
        S1=q+1-N1; S2=q*q+1-N2
        if g==1: coeffs=[1,-S1,q]
        else:
            c1=-S1; c2=(S1*S1-S2)/2; coeffs=[1,c1,c2,q*c1,q*q]
        # L(T)=prod(1-alpha T): alphas = roots of reversed polynomial
        al=np.roots(coeffs)
        P("%-18s q=%3d N1=%4d N2=%5d  |%d| <= %.2f  sig=%s  %s"%(name,q,N1,N2,abs(N1-q-1),2*g*math.sqrt(q),sig,
          " ".join("%.6f"%(abs(a)/math.sqrt(q)) for a in al)))
        for k in (2,):
            Nk=N2; P("   F^2: |N2-q^2-1|=%d <= 2g q = %d"%(abs(Nk-q*q-1),2*g*q))
P("Signature (1,n): exactly one positive direction (the hyperbolic plane <e1,e2> carries it); RH: |alpha|=sqrt q.")
open("weil_hodge_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
