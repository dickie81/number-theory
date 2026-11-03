"""Split the arb head enclosures of R = beta*·I + 2σ p pᵀ + C into the three families, with exact
rational (dyadic) centres; emit Lean ℚ data for the kernel-checked head certificate."""
import pickle, sys
from fractions import Fraction as F
from flint import arb, fmpq, ctx
import tailcert as T
ctx.prec=256
def q(me): m,e=me; return F(m)*(F(2)**e) if e>=0 else F(m,2**(-e))
def A(fr,r): return arb(fmpq(fr.numerator,fr.denominator),fmpq(r.numerator,r.denominator))
def rnd(x,b=110): return F(round(x*2**b),2**b)
EPS=F(1,10**30)
FAM={}
def go(par,certpkl,tag):
    d=pickle.load(open(f"/workspace/tail_L05_H28"+("_odd" if par else "")+".pkl","rb")); H=d['H']
    g=T.setup(); sg=-1 if par else 1
    beta=A(q(d['beta']),q(d['beta_rad']))
    p=[T.pole(2*i+par,g) for i in range(H)]
    tofr=lambda a: F(int(a.mid().man_exp()[0]))*F(2)**int(a.mid().man_exp()[1])
    tor=lambda a: F(int(a.rad().man_exp()[0]))*F(2)**int(a.rad().man_exp()[1])
    bq=rnd(tofr(beta)); assert tor(beta)+abs(tofr(beta)-bq)<EPS
    pq=[rnd(tofr(x)) for x in p]
    for x,c in zip(p,pq): assert tor(x)+abs(tofr(x)-c)<EPS and abs(c)<=2
    cq=[[None]*H for _ in range(H)]; mx=F(0)
    for i in range(H):
        for j in range(H):
            R=A(q(d['mid'][i][j]),q(d['rad'][i][j]))
            Cij=R-sg*2*p[i]*p[j]-(beta if i==j else 0)
            c=rnd(tofr(Cij)); cq[i][j]=c; mx=max(mx,tor(Cij)+abs(tofr(Cij)-c))
    assert mx<EPS, float(mx)
    FAM[par]=(bq,pq,cq)
    cert=pickle.load(open(certpkl,"rb")); cert=cert.get('c',cert)
    M,D,dl,rho=cert['M'],cert['D'],cert['delta'],cert['rho']
    worst=F(0)
    for i in range(H):
        for j in range(H):
            a=(bq if i==j else 0)+sg*2*pq[i]*pq[j]+cq[i][j]
            c=sum(M[k][i]*D[k]*M[k][j] for k in range(H))+(dl if i==j else 0)
            worst=max(worst,abs(a-c))
    budget=rho-12*EPS
    print(tag,"max |A-cert| %.3e  rho %.3e  ok %s  maxCrad %.2e"%(float(worst),float(rho),worst<=budget,float(mx)))
    fr=lambda x: f"({x.numerator}/{x.denominator})" if x.denominator!=1 else f"({x.numerator})"
    L=lambda xs: "["+", ".join(fr(x) for x in xs)+"]"
    s=f"""
namespace {tag}
def Mq : List (List ℚ) := [{(','+chr(10)+'  ').join(L(r) for r in M)}]
def Dq : List ℚ := {L(D)}
def bq : ℚ := {fr(bq)}
def pq : List ℚ := {L(pq)}
def cq : List (List ℚ) := [{(','+chr(10)+'  ').join(L(r) for r in cq)}]
end {tag}
"""
    return s,cert
s1,_=go(0,"/workspace/tailcert_final.pkl","EvenQ")
s2,_=go(1,"/workspace/cert_tailodd.pkl","OddQ")
open("/workspace/headq_data.lean","w").write(s1+s2)
