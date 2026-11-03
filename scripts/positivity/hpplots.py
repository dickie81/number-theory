import pickle, math, numpy as np, os
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
R=pickle.load(open("/workspace/hp1_res.pkl","rb"))
if os.path.exists("/workspace/hp1_res14.pkl"): R.update(pickle.load(open("/workspace/hp1_res14.pkl","rb")))
Ls=sorted({k[0] for k in R if k[2]=="real" and k[3]==0})
zhu={0.5:1.05e-6,0.6:1.82e-9,0.7:4.99e-13,0.8:2.27e-17,0.9:5.91e-23,1.0:8.08e-30,1.1:2.78e-38,1.2:9.98e-49,1.4:1.91e-77}
fig,ax=plt.subplots(1,2,figsize=(12,4.5))
for o,lab in ((False,"even"),(True,"odd")):
    for j in range(3): ax[0].semilogy(Ls,[float(R[(L,o,"real",0)]["E"][j]) for L in Ls],'o-' if o==False else 's--',label=f"{lab} λ{j+1}",ms=3)
ax[0].semilogy(sorted(zhu),[zhu[L] for L in sorted(zhu)],'kx',ms=8,label="Zhu Table 3 (upper bd)")
ax[0].axhline(2.2e-16,color='r',lw=.5); ax[0].text(0.3,4e-16,"float64 eps",color='r'); ax[0].set_xlabel("L"); ax[0].legend(fontsize=7); ax[0].set_title("Weil form low spectrum, mpmath (Zhu convention)")
for c,m in (("jit","^"),("flip","v")):
    xs=[L for L in Ls if (L,False,c,0) in R]; ax[1].plot(xs,[float(R[(L,False,c,0)]["E"][0]) for L in xs],m+'-',label=c+" even λ1")
ax[1].plot(Ls,[float(R[(L,False,"real",0)]["E"][0]) for L in Ls],'o-',label="real even λ1"); ax[1].axhline(0,color='k',lw=.5); ax[1].legend(); ax[1].set_title("fake-prime controls (linear scale)"); ax[1].set_xlabel("L")
plt.tight_layout(); plt.savefig("hp1.png",dpi=110); plt.savefig("/workspace/hp1.png",dpi=110)
rows=pickle.load(open("/workspace/hp2_rows.pkl","rb")); L2=sorted(rows)
fig,ax=plt.subplots(1,2,figsize=(12,4.5))
ax[0].semilogy(L2,[rows[L]["gap"] for L in L2],'o-',label="λ2/λ1 even"); ax[0].semilogy(L2,[rows[L]["par"] for L in L2],'s-',label="λ1 odd / λ1 even"); ax[0].legend(); ax[0].set_xlabel("L"); ax[0].set_title("ground state: simple and even")
import mpmath as mp; G=[float(mp.im(mp.zetazero(n))) for n in range(1,60)]
for L in (0.8,1.0,1.2): r=rows[L]["rr"]; ax[1].plot(r[:40],[L]*min(40,len(r)),'|',ms=12)
for g in G: ax[1].axvline(g,color='0.8',lw=.5)
for L in (0.8,1.0,1.2): ax[1].plot(rows[L]["T"],L,'r*')
ax[1].set_xlim(0,110); ax[1].set_xlabel("t"); ax[1].set_ylabel("L"); ax[1].set_title("real zeros of ground-state transform (|), zeta zeros (grey), T* (*)")
plt.tight_layout(); plt.savefig("hp2.png",dpi=110); plt.savefig("/workspace/hp2.png",dpi=110)
cur=pickle.load(open("/workspace/hp3_curves.pkl","rb")); B=pickle.load(open("/workspace/hp3b.pkl","rb"))
fig,ax=plt.subplots(1,2,figsize=(12,4.5))
for lab in ("real","jit","flip3"):
    t,s=cur[(2.0,lab)]; ax[0].hist(s,bins=100,histtype='step',density=True,label=lab)
ax[0].set_title("distribution of S(t)/A on [1,T*], L=2"); ax[0].legend()
for L,mk in ((0.8,'o'),(1.0,'s')):
    pts=[b for b in B if b[0]==L]; ax[1].scatter([b[3] for b in pts],[np.sign(b[2])*min(1,abs(b[2]))**0.1 if abs(b[2])>1e-12 else 0 for b in pts],marker=mk,label=f"L={L}")
ax[1].set_xlabel("max alignment S/A on [1,T*]"); ax[1].set_ylabel("sign(λ_min)·|λ_min|^0.1"); ax[1].legend(); ax[1].set_title("Cramér random primes: alignment vs positivity")
plt.tight_layout(); plt.savefig("hp3.png",dpi=110); plt.savefig("/workspace/hp3.png",dpi=110)
