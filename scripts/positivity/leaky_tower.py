"""Leaky gravastar tower: truncated modular cusps coupled losslessly. UNCERTIFIED numerics (mpmath/numpy)."""
import mpmath as mp, numpy as np, math, random
mp.mp.dps=20
out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
phi=lambda s: mp.sqrt(mp.pi)*mp.gamma(s-0.5)*mp.zeta(2*s-1)/(mp.gamma(s)*mp.zeta(2*s))
G=[float(mp.im(mp.zetazero(n))) for n in range(1,11)]
theta=lambda r: float(mp.arg(phi(mp.mpc(0.5,r))))
P("== 1. Single truncated cusp: constant term y^s+phi(s)y^{1-s} vanishes at Y  <=>  Y^{2s-1} = -phi(s) ==")
P("On Re s=1/2 |phi|=1 so solutions s=1/2+ir are REAL (pseudo-Laplacian is self-adjoint).")
R=np.arange(0.05,30,0.01); TH=np.array([theta(r) for r in R])
for Y in (2.0,5.0,20.0,100.0):
    F=np.angle(np.exp(1j*(2*R*math.log(Y)-TH-math.pi)))
    roots=[R[i] for i in range(len(R)-1) if F[i]<0<=F[i+1] and abs(F[i+1]-F[i])<1]
    d=[min(abs(x-g/2) for x in roots) for g in G]
    P("Y=%5g: %3d real r in (0,30); spacing~pi/logY=%.3f; mean dist gamma_n/2 -> nearest r = %.3f (random ~ spacing/4=%.3f)"%(Y,len(roots),math.pi/math.log(Y),np.mean(d),math.pi/math.log(Y)/4))
P("Off-line solutions seeded at rho/2 (where phi has poles):")
for Y in (2.0,5.0,20.0,100.0):
    row=[]
    for g in G[:3]:
        try: s=mp.findroot(lambda s: mp.power(Y,2*s-1)+phi(s), mp.mpc(0.25,g/2)+0.01)
        except Exception: s=None
        row.append("none" if s is None else "%s"%mp.nstr(s,6))
    P("Y=%5g:"%Y," | ".join(row))
P("(rho/2 are poles of phi, hence never solutions; nearby roots drift with Y and are not the zeros)")
P("\n== 2. Tower: K shells, cavity lengths L, junction Fresnel matrices from sphere areas A_d ==")
A=lambda d: 2*math.pi**(d/2)/math.gamma(d/2)
def tower_modes(K,L,junction,rmax=52,dr=0.004):
    rs=np.arange(0.05,rmax,dr); m=[]
    for r in rs:
        # transfer through: left end reflects with phi(1/2+ir); right end hard wall (-1)
        ph=np.exp(1j*TH_i(r)); M=np.eye(2,dtype=complex)
        for k in range(K):
            e=np.exp(1j*r*L); M=np.diag([e,1/e])@M
            if k<K-1: M=junction(k)@M
        # wave (a,b): a right-moving. left boundary: a0 = ph*b0 ; right: b=-a
        v=M@np.array([ph,1]); m.append(v[0]+v[1])
    m=np.array(m); f=np.abs(m)
    return [rs[i] for i in range(1,len(f)-1) if f[i]<f[i-1] and f[i]<f[i+1] and f[i]<0.05]
_cache={}
def TH_i(r):
    k=round(r,3)
    if k not in _cache: _cache[k]=theta(k)
    return _cache[k]
def fresnel(Z1,Z2):
    rr=(Z1-Z2)/(Z1+Z2); t=math.sqrt(1-rr*rr)
    return np.array([[1/t,rr/t],[rr/t,1/t]],dtype=complex)  # transfer matrix of lossless step (det 1)
geo=lambda k: fresnel(A(k+2),A(k+3))
def rnd(seed):
    rng=random.Random(seed)
    def j(k):
        a=rng.uniform(-1,1); t=math.sqrt(1-a*a); p=rng.uniform(0,2*math.pi)
        return np.array([[np.exp(1j*p)/t,a/t],[a/t,np.exp(-1j*p)/t]],dtype=complex)
    return j
def score(modes):
    sp=52/max(len(modes),1)
    return np.mean([min(abs(x-g) for x in modes) for g in G]), np.mean([min(abs(x-g/2) for x in modes) for g in G]), sp
for K in (3,6,10):
    m=tower_modes(K,1.0,geo); a,b,sp=score(m)
    P("K=%2d geometric: %3d real modes in (0,52); mean dist to gamma_n %.3f, to gamma_n/2 %.3f; spacing %.3f (random~%.3f)"%(K,len(m),a,b,sp,sp/4))
    for s in (1,2):
        m=tower_modes(K,1.0,rnd(100*K+s)); a,b,sp=score(m)
        P("     random-junction control %d: %3d modes; dist gamma %.3f, gamma/2 %.3f; random~%.3f"%(s,len(m),a,b,sp/4))
P("Mode count check: transfer matrices have det 1 and |phi|=1, so the closed tower is lossless and every")
P("mode found is a real r (real axis only; modes = local minima |f|<0.05 on a 0.004 grid, may miss some).")
P("Note on part 1: near r=gamma_n/2 the phase of phi winds fast (pole at distance 1/4 off the line),")
P("forcing an extra real root there, so roots cluster at gamma_n/2 better than random. This is the known")
P("resonance phase-shift effect: it reads off Im(rho) given the zeros, and says nothing about Re(rho).")
P("\n== 3. Verdict ==")
P("Losslessness makes the tower spectrum real, but that spectrum is a cavity spectrum set by L, K, A_d;")
P("its distance to gamma_n and gamma_n/2 is at the random baseline, like random junctions. The zeros sit at the")
P("POLES of phi (s=rho/2, Re s=1/4), off the unitary line; closing the system does not move them onto it")
P("nor make them eigenvalues. Reality of the tower spectrum says nothing about Re(rho).")
open("leaky_tower_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
