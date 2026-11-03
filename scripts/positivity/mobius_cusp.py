"""Close the modular cusp on itself (periodic vs Mobius). UNCERTIFIED floating point (mpmath/numpy).
v(x)=e^{-x/2}u = e^{irx}+phi e^{-irx}, s=1/2+ir, x=log y; -d^2/dx^2 is the self-adjoint form."""
import mpmath as mp, numpy as np, math, random
mp.mp.dps=20
out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
phi=lambda s: mp.sqrt(mp.pi)*mp.gamma(s-0.5)*mp.zeta(2*s-1)/(mp.gamma(s)*mp.zeta(2*s))
G=[float(mp.im(mp.zetazero(n))) for n in range(1,11)]
P("Algebra:")
P(" (a) periodic v(X2)=v(X1), v'(X2)=v'(X1): both e^{+-irx} terms must vanish separately -> e^{irL}=1,")
P("     r=2pi n/L. phi drops out: no zeta at all.")
P(" (b) Mobius x->2c-x (y->Y^2/y, Y=sqrt(Y1Y2)), v(2c-x)=eps v(x): matching coefficients gives")
P("     phi(s) = eps Y^{2s-1}, eps=+1 (Neumann-type) or -1 (Dirichlet-type, = pseudo-Laplacian).")
P(" (c) twisted: phi(s) = e^{i alpha} Y^{2s-1}.")
P(" All are restrictions of a self-adjoint problem: |phi|=1=|Y^{2s-1}| on Re s=1/2 gives real r.")
R=np.arange(0.05,30,0.01); TH=np.array([float(mp.arg(phi(mp.mpc(0.5,r)))) for r in R])
def roots(Y,alpha):
    F=np.angle(np.exp(1j*(2*R*math.log(Y)+alpha-TH)))
    return [R[i] for i in range(len(R)-1) if F[i]<0<=F[i+1] and F[i+1]-F[i]<1]
def score(rs,targets): return np.mean([min(abs(x-g) for x in rs) for g in targets if g<30])
P("\n== real-line modes, distance to gamma_n/2 and gamma_n (n<=10, within r<30) vs chance spacing/4 ==")
rng=random.Random(3)
for Y in (2,10,100,1000):
    sp=math.pi/math.log(Y)
    for name,al in (("Mobius eps=+1",0.0),("Mobius eps=-1",math.pi),("random twist",rng.uniform(0,2*math.pi))):
        rs=roots(Y,al)
        P("Y=%5d %-14s %3d modes  d(gamma/2)=%.3f  d(gamma)=%.3f  chance~%.3f"%(Y,name,len(rs),score(rs,[g/2 for g in G]),score(rs,G),sp/4))
P("\n== off-line search seeded at rho/2 ==")
for Y in (1000,10,2,0.5,0.1,0.01,0.001):
    row=[]
    for g in G[:2]:
        try:
            z=mp.findroot(lambda s: 1/phi(s)+mp.power(Y,1-2*s), mp.mpc(0.25,g/2)+0.003)  # phi=-Y^{2s-1} <=> 1/phi=-Y^{1-2s}
            row.append("%s (|z-rho/2|=%.1e)"%(mp.nstr(z,8),float(abs(z-mp.mpc(0.25,g/2)))))
        except Exception: row.append("no root")
    P("Y=%-6g eps=-1:"%Y," | ".join(row))
P("Y>=2: roots fall onto Re s=1/2 (real modes), never at rho/2.")
P("Y->0 (closing BELOW height 1, outside the cusp region of the fundamental domain): Y^{1-2s}->0 for")
P("Re s<1/2, so roots converge to zeros of 1/phi = poles of phi = rho/2. Distance shrinks like Y^{1/2}.")
P("\nVerdict: phi(s)=c with finite c never holds at zeta(2s)=0 (phi has a pole there, and zeta(2s-1),Gamma")
P("cannot cancel it). The spectrum is exactly {rho/2} only in the degenerate limit c=Y^{2s-1}->inf, i.e. Y->0,")
P("where the cut leaves the cusp and the self-adjoint truncation no longer exists. Mobius closure =")
P("pseudo-Laplacian: real modes, Im-parts near gamma_n/2 only through the known phase-shift effect.")
open("mobius_cusp_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
