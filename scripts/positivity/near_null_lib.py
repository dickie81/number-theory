"""Near-null directions of the Weil form (pole-orth, support [-L,L], 40-sine basis). UNCERTIFIED float64."""
import numpy as np, math, os
import mpmath as mp
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
import place_margin as pm
M=pm.M; out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
zf="/tmp/zeta_zeros_600.npy"
if not os.path.exists(zf): np.save(zf,np.array([float(mp.im(mp.zetazero(n))) for n in range(1,601)]))
G=np.load(zf)
def fh(t,L):
    k=np.arange(1,M+1)*math.pi/(2*L); t=np.asarray(t)[None,:]; k=k[:,None]
    I=((np.exp(1j*(t+k)*2*L)-1)/(1j*(t+k))-(np.exp(1j*(t-k)*2*L)-1)/(1j*(t-k)))/(2j)
    return np.exp(-1j*t*L)*I/math.sqrt(L)
def zform(L,g):  # 2 sum |fhat(gamma)|^2 as a matrix
    F=fh(g,L); return 2*(F@F.conj().T).real
def Nsm(T): return T/(2*math.pi)*math.log(T/(2*math.pi*math.e))+7/8
def gue_fake(rng):
    H=rng.normal(size=(1200,1200))+1j*rng.normal(size=(1200,1200)); H=(H+H.conj().T)/2
    e=np.linalg.eigvalsh(H)/math.sqrt(1200); e=e[(e>-1)&(e<1)]                # bulk
    u=1200*(0.5+(e*np.sqrt(4-e**2))/(4*math.pi)+np.arcsin(e/2)/math.pi)  # semicircle unfold (radius 2)
    u=u-u[0]+0.5; gs=[]; from scipy.optimize import brentq
    for v in u[:600]: gs.append(brentq(lambda T, v=v: Nsm(T)-v, 2*math.pi, 1e5))
    return np.array(gs)
