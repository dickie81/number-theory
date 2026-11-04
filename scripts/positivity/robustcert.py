"""Robust head certificates (L=1/2): λ_min of the arb mid matrices, an LDLᵀ certificate of A − δI with
δ ≈ 0.9 λ_min, small dyadic data, and the entry tolerance budget ρ with 28ρ < δ − m (Cauchy–Schwarz head bound)."""
import pickle, mpmath as mp
from fractions import Fraction as F
import headsplit as HS   # reuses tailcert setup; runs headsplit main harmlessly
mp.mp.prec=200
def q(me): m,e=me; return F(m)*(F(2)**e) if e>=0 else F(m,2**(-e))
def rnd(x,b=64): return F(int(mp.nint(x*mp.mpf(2)**b)),2**b)
def frnd(x,b=64): return F(round(x*2**b),2**b)
cfg={0:dict(delta=F(2,10**7),rho=F(67,10**10),m=F(1,10**8),eb=F(1,10**12),ep=F(1,10**12),ec=F(6,10**9)),
     1:dict(delta=F(42,10**6),rho=F(14,10**7),m=F(2,10**6),eb=F(1,10**10),ep=F(1,10**10),ec=F(13,10**7))}
out=""
for par,tag in ((0,"Even2"),(1,"Odd2")):
    d=pickle.load(open("/workspace/tail_L05_H28"+("_odd" if par else "")+".pkl","rb")); n=d['H']
    c=cfg[par]
    A=[[q(d['mid'][i][j]) for j in range(n)] for i in range(n)]
    Am=mp.matrix([[mp.mpf(A[i][j].numerator)/A[i][j].denominator for j in range(n)] for i in range(n)])
    lam=min(mp.eigsy(Am)[0])
    dl=c['delta']; B=Am-mp.mpf(dl.numerator)/dl.denominator*mp.eye(n); Lm=mp.eye(n); Dv=[0]*n
    for j in range(n):
        Dv[j]=B[j,j]-sum(Lm[j,k]**2*Dv[k] for k in range(j))
        for i in range(j+1,n): Lm[i,j]=(B[i,j]-sum(Lm[i,k]*Lm[j,k]*Dv[k] for k in range(j)))/Dv[j]
    M=[[rnd(Lm[j,k]) if j>=k else F(0) for j in range(n)] for k in range(n)]; D=[rnd(v) for v in Dv]
    assert all(x>=0 for x in D)
    # rational centres of the three families (from headsplit data, rounded to 2^-64)
    import headsplit
    bq,pq,cq=headsplit.FAM[par]
    bq=frnd(bq); pq=[frnd(x) for x in pq]; cq=[[frnd(x) for x in r] for r in cq]
    sg=-1 if par else 1; worst=F(0)
    for i in range(n):
        for j in range(n):
            a=(bq if i==j else 0)+sg*2*pq[i]*pq[j]+cq[i][j]
            cc=sum(M[k][i]*D[k]*M[k][j] for k in range(n))+(dl if i==j else 0)
            worst=max(worst,abs(a-cc))
    fam=c['eb']+10*c['ep']+c['ec']; r=c['rho']-fam
    ok = worst<=r and 28*c['rho']<=dl-c['m'] and c['m']>0
    print(tag,"lam_min %s delta %s rho %s m %s |A-cert| %.2e r %.2e famε(β,p,c)=%s,%s,%s ok %s"%(mp.nstr(lam,6),float(dl),float(c['rho']),float(c['m']),float(worst),float(r),float(c['eb']),float(c['ep']),float(c['ec']),ok))
    fr=lambda x: f"({x.numerator}/{x.denominator})" if x.denominator!=1 else f"({x.numerator})"
    L=lambda xs: "["+", ".join(fr(x) for x in xs)+"]"
    out+=f"""
namespace {tag}
def Mq : List (List ℚ) := [{(','+chr(10)+'  ').join(L(r_) for r_ in M)}]
def Dq : List ℚ := {L(D)}
def bq : ℚ := {fr(bq)}
def pq : List ℚ := {L(pq)}
def cq : List (List ℚ) := [{(','+chr(10)+'  ').join(L(r_) for r_ in cq)}]
end {tag}
"""
open("/workspace/robust_data.lean","w").write(out)
