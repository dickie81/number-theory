"""Negative squares of a truncated Weil form as an off-line-zero detector (Bombieri 2000 picture).
UNCERTIFIED floating point. Built FROM the zeros (spectral side), so circular as a proof device."""
import numpy as np, mpmath as mp
out=[]; P=lambda *a: out.append(" ".join(str(x) for x in a))
G=np.array([float(mp.im(mp.zetazero(n))) for n in range(1,61)])   # gamma < ~160
def form(zeros, centers, w):
    # W(c) = sum_gamma F(gamma) conj(F(conj gamma)), F = sum c_j e^{-(z-c_j)^2/2w^2}; zeros closed under conj and -.
    Z=np.concatenate([zeros,-zeros])
    U=np.exp(-(Z[:,None]-centers[None,:])**2/(2*w*w))          # F_j(gamma)
    V=np.exp(-(np.conj(Z)[:,None]-centers[None,:])**2/(2*w*w)) # F_j(conj gamma)
    M=V.conj().T@U        # sum over zeros: conj(F_k(conj g)) F_j(g)
    M=(M+M.conj().T)/2
    return np.linalg.eigvalsh(M)
def negs(ev,tol=1e-9): return int((ev< -tol*np.max(np.abs(ev))).sum())
cent=np.arange(5,160,0.7); w=1.2
P("basis: %d Gaussians, width %.1f, centres 5..160; 60 zeros (+-gamma)"%(len(cent),w))
P("RH zeros only: negative squares =",negs(form(G.astype(complex),cent,w)))
for pairs in ([(30.0,0.2)],[(30.0,0.2),(60.0,0.1)],[(30.0,0.2),(60.0,0.1),(95.0,0.05)],[(30.0,0.01)]):
    extra=[]
    for t,d in pairs: extra+= [t+1j*d, t-1j*d]
    Zs=np.concatenate([G.astype(complex),np.array(extra)])
    P("inject %s: off-line zeros (counting +-gamma) = %d, negative squares = %d (one-sided basis expects %d)"%(
      pairs,4*len(pairs),negs(form(Zs,cent,w)),len(pairs)))
cent=np.concatenate([-cent[::-1],cent]); P("\nsymmetric basis (centres +-5..160, %d functions):"%len(cent))
P("RH zeros only: negative squares =",negs(form(G.astype(complex),cent,w)))
for pairs in ([(30.0,0.2)],[(30.0,0.2),(60.0,0.1)]):
    extra=[]
    for t,d in pairs: extra+=[t+1j*d,t-1j*d]
    Zs=np.concatenate([G.astype(complex),np.array(extra)])
    P("inject %s: off-line zeros = %d, negative squares = %d (half = %d)"%(pairs,4*len(pairs),negs(form(Zs,cent,w)),len(pairs)))
P("(one-sided basis sees only Im gamma>0 copies, hence one negative per quadruple there.)")
P("Detector works (kappa = #off-line/2) but kappa=0 for the true zeros is RH restated, not derived.")
open("krein_detector_results.txt","w").write("\n".join(out)+"\n"); print("\n".join(out))
