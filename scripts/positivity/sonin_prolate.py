"""Prolate data (c=2pi, even) and the Connes-Consani remainder eps(rho) (Theorem 7). UNCERTIFIED floats."""
import numpy as np, math
xg,wg=np.polynomial.legendre.leggauss(120); xg=(xg+1)/2; wg=wg/2      # nodes on [0,1]
A=2*np.cos(2*math.pi*np.outer(xg,xg))*wg[None,:]
sw=np.sqrt(wg); S=sw[:,None]*A/sw[None,:]                             # symmetric
lam,V=np.linalg.eigh((S+S.T)/2); o=np.argsort(-abs(lam)); lam=lam[o]; V=V[:,o]
NP=8; lam=lam[:NP]; XI=V[:,:NP]/sw[:,None]                            # xi_n at nodes, int_0^1 xi^2 = 1
def xi(n,x):   # Nystrom interpolation, x in [0,1]
    return 2*np.cos(2*math.pi*np.outer(x,xg))@(wg*XI[:,n])/lam[n]
def psi(n,v):  # (F xi_n)(v) = 2 int_0^1 xi_n cos(2 pi x v)
    return 2*np.cos(2*math.pi*np.outer(v,xg))@(wg*XI[:,n])
def eps(rho, nx=400):
    """eps(rho) = sum tau_n rho^{1/2} int_{1/rho}^1 xi_n(x) zeta_n(rho x) dx, rho>=1."""
    if rho<=1: rho=1/rho if rho<1 else rho
    a=1/rho; xs,ws=np.polynomial.legendre.leggauss(nx); xs=a+(1-a)*(xs+1)/2; ws=ws*(1-a)/2
    tot=0.0
    for n in range(NP):
        tau=lam[n]/math.sqrt(1-lam[n]**2)
        tot+=tau/math.sqrt(1-lam[n]**2)*math.sqrt(rho)*np.sum(ws*xi(n,xs)*psi(n,rho*xs))
    return tot
if __name__=="__main__":
    print("lambda(n):"," ".join("%.6f"%l for l in lam[:6]),"(paper: 0.999971 -0.979485 0.524086 -0.0589766 0.00273233)")
    print("sum lambda^2 = %.9f (paper 2.237484835)"%np.sum(lam**2))
    h=1e-4; print("eps'(1+) ~ %.4f (paper ~22.9965); eps(1)=%.5f eps(1.5)=%.5f eps(2)=%.5f"%((eps(1+h)-eps(1+2*h))/(-h),eps(1.0),eps(1.5),eps(2.0)))
