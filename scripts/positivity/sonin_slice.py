"""Connes-Consani Sonin functional in the place_margin setup. UNCERTIFIED floats.
Quadratic forms on f in span(40 sines on [-L,L]) with f-hat(+-i/2)=0 and f-hat(0)=0 (int f = 0):
  W_inf (archimedean), S = W_inf + E (Sonin trace, Thm 7: >=0 always), -E = W_inf - S (Thm 1: >=0 if L<=log(2)/2),
  W = W_inf - primes (full Weil), W - S = -E - primes."""
import numpy as np, math
import place_margin as pm
import sonin_prolate as sp
out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
def Emat(L):
    x=np.linspace(-L,L,601); dx=x[1]-x[0]; B=pm.basis_vals(x,L)
    d=np.linspace(0,2*L,1201); tab=np.array([sp.eps(math.exp(v)) for v in d])
    K=np.interp(np.abs(x[:,None]-x[None,:]),d,tab)
    return B@K@B.T*dx*dx, B@np.ones_like(x)*dx
def mins(L):
    arch,prim,a,b,_=pm.forms(L); E,c0=Emat(L)
    Q,_=np.linalg.qr(np.stack([a,b,c0],1)); U=np.linalg.svd(np.eye(pm.M)-Q@Q.T)[0][:,:pm.M-3]
    m=lambda W: np.linalg.eigvalsh(U.T@((W+W.T)/2)@U)[0]
    return dict(Winf=m(arch),S=m(arch+E),mE=m(-E),W=m(arch-prim),WmS=m(-E-prim))
P("min eigenvalues on {fhat(+-i/2)=fhat(0)=0}, support [-L,L] (log scale); Thm 1 range L<=%.4f"%(math.log(2)/2))
P("  L      W_inf       S=W_inf+E     -E=W_inf-S    W(full)       W-S")
for L in (0.1,0.2,0.3,math.log(2)/2,0.4,0.5,0.6,0.8,1.0,1.2,1.5):
    r=mins(L); P("%.4f  %+.3e  %+.3e  %+.3e  %+.3e  %+.3e"%(L,r['Winf'],r['S'],r['mE'],r['W'],r['WmS']))
P("\nper-prime-power drops (L = log(n)/2 -+ 0.004):  n   W before -> after   |  W-S before -> after")
for n in (2,3,4,5,7,8,9,11,13,16,17,19):
    l=math.log(n)/2; b=mins(l-0.004); a=mins(l+0.004)
    P("n=%2d  W %+.3e -> %+.3e   W-S %+.3e -> %+.3e"%(n,b['W'],a['W'],b['WmS'],a['WmS']))
open("sonin_slice_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
