"""Head certificate for the 28-mode Zhu-reduced matrix R (L=1/2, even, T#=30) + Lean data."""
import pickle, certgen, mpmath as mp
from fractions import Fraction as F
import shutil
shutil.copy("/workspace/tail_L05_H28.pkl","/workspace/arb_tailL05.pkl")
c=certgen.go("tailL05",bits=80)
tb=pickle.load(open("/workspace/tailbounds_h28.pkl","rb"))
d=pickle.load(open("/workspace/tail_L05_H28.pkl","rb"))
beta_lo=certgen.q(d['beta'])-certgen.q(d['beta_rad'])
n=c['n']; lam0=c['delta']-n*n*c['rho']
dlo=F(5497,10000)-tb['dneg']*2; assert dlo<=beta_lo-tb['dneg']
e=tb['e']; c2=tb['c2']
m=F(mp.nstr(min(lam0,dlo-e)*0.9,3)) if False else None
lam0f=float(lam0); m=F(int(min(lam0f,float(dlo-e))*900),1000)
ok=c2<=(lam0-m)*(dlo-e-m) and m<=lam0 and m<=dlo-e
print("lam0",float(lam0),"d",float(dlo),"e",float(e),"c2",float(c2),"m",m,"ok",ok)
pickle.dump(dict(c=c,dlo=dlo,e=e,c2=c2,m=m),open("/workspace/tailcert_final.pkl","wb"))
open("/workspace/tail_data.lean","w").write(certgen.lean("tailL05",c,"L05Tail"))
