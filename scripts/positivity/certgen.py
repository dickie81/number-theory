"""From arb enclosures (exact dyadic mid, rad) build an exact-rational certificate C = M^T D M + delta I,
with D>=0 and rho >= max_ij (rad_ij + |mid_ij - C_ij|), check n^2 rho < delta exactly, emit Lean data."""
import pickle, sys, mpmath as mp
from fractions import Fraction as F
def q(me): m,e=me; return F(m)*(F(2)**e) if e>=0 else F(m,2**(-e))
def go(tag, delta_frac=F(1,2), bits=None):
    d=pickle.load(open(f"/workspace/arb_{tag}.pkl","rb")); n=len(d['mid'])
    mid=[[q(d['mid'][i][j]) for j in range(n)] for i in range(n)]; rad=[[q(d['rad'][i][j]) for j in range(n)] for i in range(n)]
    bits=bits or d['prec']; mp.mp.prec=bits+64
    Am=mp.matrix([[mp.mpf(mid[i][j].numerator)/mid[i][j].denominator for j in range(n)] for i in range(n)])
    lam=min(mp.eigsy(Am)[0]); delta=F(mp.nstr(lam*float(delta_frac),3))  # rational ~ lam/2
    # LDL^T of mid - delta I in high precision
    B=Am-mp.mpf(delta.numerator)/delta.denominator*mp.eye(n); Lm=mp.eye(n); Dv=[0]*n
    for j in range(n):
        Dv[j]=B[j,j]-sum(Lm[j,k]**2*Dv[k] for k in range(j))
        for i in range(j+1,n): Lm[i,j]=(B[i,j]-sum(Lm[i,k]*Lm[j,k]*Dv[k] for k in range(j)))/Dv[j]
    rnd=lambda x:F(int(mp.nint(x*mp.mpf(2)**bits)),2**bits)
    Mq=[[rnd(Lm[j,k]) if j>=k else F(0) for j in range(n)] for k in range(n)]   # M[k][i] = L[i][k]
    Dq=[rnd(v) for v in Dv]; assert all(x>=0 for x in Dq), "negative pivot"
    rho=F(0)
    for i in range(n):
        for j in range(n):
            c=sum(Mq[k][i]*Dq[k]*Mq[k][j] for k in range(n))+(delta if i==j else 0)
            rho=max(rho,rad[i][j]+abs(mid[i][j]-c))
    rho_up=F(mp.nstr(mp.mpf(rho.numerator)/rho.denominator*1.01,3)); assert rho_up>=rho
    ok=n*n*rho_up<delta
    print(tag,"n",n,"lam_min(mid) %s delta %s  max arb rad %.2e  rho %s  n^2 rho/delta %.2e  ok=%s"%(mp.nstr(lam,6),delta,float(max(max(r) for r in rad)),rho_up,float(n*n*rho_up/delta),ok))
    return dict(n=n,M=Mq,D=Dq,delta=delta,rho=rho_up,ok=ok,lam=lam)
def lean(tag,c,name):
    n=c['n']; fr=lambda x:f"({x.numerator}/{x.denominator}:ℝ)" if x.denominator!=1 else f"({x.numerator}:ℝ)"
    rows=[]
    for k in range(n): rows.append("![" + ", ".join(fr(c['M'][k][i]) for i in range(n)) + "]")
    s=f"""
namespace {name}
/-- Upper-triangular factor (row `k` = column `k` of the unit lower LDLᵀ factor), exact rationals. -/
noncomputable def M : Fin {n} → Fin {n} → ℝ := ![{(','+chr(10)+'  ').join(rows)}]
/-- LDLᵀ pivots of `mid − δ I`, exact rationals. -/
noncomputable def D : Fin {n} → ℝ := ![{', '.join(fr(x) for x in c['D'])}]
noncomputable def δ : ℝ := {fr(c['delta'])}
noncomputable def ρ : ℝ := {fr(c['rho'])}
lemma hD : ∀ k, 0 ≤ D k := by intro k; fin_cases k <;> simp [D] <;> norm_num
lemma hρ : ((({n}:ℕ)):ℝ) ^ 2 * ρ < δ := by simp only [ρ, δ]; norm_num
end {name}
"""
    return s
if __name__=="__main__":
    out=""
    for tag,name in (("1_2","L05"),("7_10","L07"),("4_5","L08")):
        c=go(tag); pickle.dump(c,open(f"/workspace/cert_{tag}.pkl","wb"))
        if c['ok']: out+=lean(tag,c,name)
    open("/workspace/weilcert_data.lean","w").write(out)
