"""Ground state (even sector, Zhu convention) from hp1 results: zeros of its Fourier transform.
xi^(r) = cos(rL)/sqrt(L) * sum_k a_k 2 alpha_k/(alpha_k^2 - r^2)  (odd k)  =>  zeros = roots z=r^2 of
P(z) = sum_k a_k 2 alpha_k prod_{j!=k}(alpha_j^2 - z)  [degree n-1]  plus cos zeros alpha_m, m odd > K. mpmath."""
import mpmath as mp, pickle, math
G=[float(mp.im(mp.zetazero(n))) for n in range(1,80)]
R=pickle.load(open("/workspace/hp1_res.pkl","rb"))
out=[]; P_=lambda *a:(out.append(" ".join(str(x) for x in a)),print(*a,flush=True))
P_("L   n  dps  lam2/lam1(even)  lam1odd/lam1even | #roots z=r^2: real>0 / complex / real<0 | N(T*) | roots r below T* vs gamma (max |r-gamma|)")
rows={}
for L in (0.5,0.6,0.7,0.8,0.9,1.0,1.1,1.2):
    v=R[(L,False,"real",0)]; o=R[(L,True,"real",0)]; mp.mp.dps=v["dps"]
    E=[mp.mpf(e) for e in v["E"]]; Eo=mp.mpf(o["E"][0]); a=[mp.mpf(x) for x in v["v0"]]; ks=v["ks"]; LL=mp.mpf(L)
    al=[mp.pi*k/(2*LL) for k in ks]; n=len(ks)
    # build polynomial coefficients (in z) by multiplying out
    poly=[mp.mpf(0)]*n
    for i in range(n):
        c=[mp.mpf(1)]
        for j in range(n):
            if j==i: continue
            b=al[j]**2; c=[ (c[m] if m<len(c) else 0)*b - (c[m-1] if m>=1 else 0) for m in range(len(c)+1)]
        for m in range(len(c)): poly[m]+=a[i]*2*al[i]*c[m]
    coeffs=list(reversed(poly))  # highest first
    while abs(coeffs[0])<mp.mpf(10)**(-v["dps"]+10): coeffs=coeffs[1:]
    rts=mp.polyroots(coeffs,maxsteps=400,extraprec=4*v["dps"])
    rp=[r for r in rts if abs(mp.im(r))<mp.mpf(10)**(-10)*max(1,abs(r)) and mp.re(r)>0]
    rn=[r for r in rts if abs(mp.im(r))<mp.mpf(10)**(-10)*max(1,abs(r)) and mp.re(r)<=0]
    rc=[r for r in rts if r not in rp and r not in rn]
    rr=sorted(float(mp.sqrt(mp.re(r))) for r in rp); T=2*math.pi*math.exp(2*L); NT=sum(g<T for g in G)
    low=[x for x in rr if x<T]; dev=max([min(abs(x-g) for g in G) for x in low],default=float('nan'))
    rows[L]=dict(gap=float(E[1]/E[0]),par=float(Eo/E[0]),rr=rr,nc=len(rc),NT=NT,T=T)
    P_("%.1f %3d %3d  %.3e        %.3e        | %d / %d / %d | %d | %s  max dev %.2e"%(L,n,v["dps"],E[1]/E[0],Eo/E[0],len(rp),len(rc),len(rn),NT,[round(x,4) for x in low],dev))
    P_("     next real roots above T*:",[round(x,2) for x in rr if x>=T][:6], " alpha_k (k odd) first:",[round(float(x),2) for x in al[:6]])
open("hp2_results.txt","w").write("\n".join(out)+"\n"); pickle.dump(rows,open("/workspace/hp2_rows.pkl","wb"))
