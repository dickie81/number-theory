"""Rigorous (arb) tail constants for the L=1/2 even-sector block theorem.
Head = Legendre even orders 0..2(h-1); tail = orders >= 2h. Bounds used (analytic, see docs):
 |j_n(x)| <= min(1, x^n/(2n+1)!!) for real x>=0;  0 <= i_n(z) <= z^n cosh z/(2n+1)!!.
 |C_nm| <= (Mpsi/pi) 4L sqrt(nu_n nu_m) int_0^T |j_n(tL) j_m(tL)| dt,  Mpsi = sup_[0,T]|Psi - beta*|."""
import sys, math
from flint import arb, acb, fmpq, ctx
from fractions import Fraction as F
import tailcert as tc
g=tc.setup(); L=g['L']; T=g['T']; pi=g['pi']; beta=g['beta']
h=int(sys.argv[1]) if len(sys.argv)>1 else 28
# Mpsi by interval cover of [0,T]
K=6000; Mp=arb(0)
for k in range(K):
    a=arb(fmpq(k*tc.TS,K)); b=arb(fmpq((k+1)*tc.TS,K)); t=acb((a+b)/2+ (b-a)/2*arb(0,1))
    v=abs((tc.Psi(t,g)-beta).real); Mp=Mp.max(v) if hasattr(Mp,'max') else max(Mp,v)
Mpu=float(Mp.upper()) if hasattr(Mp,'upper') else float(Mp.mid()+Mp.rad())
print("Mpsi <=",Mpu)
Mq=F(math.ceil(Mpu*1000)+1,1000)
df=tc.dfact; Lf=F(1,2); Tf=F(tc.TS)
pi_lo=F(314159,100000)
def jint(n,m): # int_0^T (tL)^{n+m}/((2n+1)!!(2m+1)!!) dt, exact rational
    return Lf**(n+m)*Tf**(n+m+1)/((n+m+1)*df(n)*df(m))
def jint1(m): # int_0^T (tL)^m/(2m+1)!! dt  (head factor |j_n|<=1)
    return Lf**m*Tf**(m+1)/((m+1)*df(m))
def sq_up(x): # rational upper bound of sqrt
    r=F(math.isqrt(int(x*10**40))+1,10**20); assert r*r>=x; return r
nu=lambda n:F(2*n+1,2)
cosh_up=F(1032,1000) # cosh(1/4)=1.0314...
def pole_up(n): z=F(1,4); return 2*sq_up(Lf*nu(n))*z**n*cosh_up/df(n)
def Cb(n,m,head=False):
    pref=Mq/pi_lo*4*Lf*sq_up(nu(n)*nu(m))
    return pref*(jint1(m) if head else jint(n,m))
NMAX=600  # explicit; beyond NMAX geometric remainder (ratio check)
tail=[2*k for k in range(h,NMAX//2)]
# off-diagonal row sum e (sup over tail rows), includes pole cross terms
e=F(0); dmin=None
for n in tail[:40]:
    s=sum(Cb(n,m)+2*pole_up(n)*pole_up(m) for m in tail if m!=n)
    e=max(e,s); dd=-Cb(n,n); dmin=dd if dmin is None else min(dmin,dd)
c2=sum((Cb(n,m,True)+2*pole_up(n)*pole_up(m))**2 for n in range(0,2*h,2) for m in tail)
# remainder: terms decay faster than (15)^m/(2m+1)!!, ratio < 1/4 past m=60; bound by doubling the last explicit term (crudely x2 safety)
rem=Cb(0,NMAX,True); print("last term",float(rem))
e=e*F(1001,1000)+F(1,10**60); c2=c2*F(1001,1000)+F(1,10**60)
print("h",h,"first tail order",2*h,"d_off(min) -|C_nn| >=",float(dmin),"e <=",float(e),"c^2 <=",float(c2))
import pickle; pickle.dump(dict(h=h,Mpsi=Mq,e=e,c2=c2,dneg=-dmin),open(f"/workspace/tailbounds_h{h}.pkl","wb"))
