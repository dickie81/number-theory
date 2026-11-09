"""Is the extremiser at its fourth-moment cap?  For the power method's b (from the interval start) and for the best
|b_n| = 1 vector: s = sum_{chi in W}|D_b|^2 / |b|^2, the cap (|W| sum_{all chi}|D_b|^4)^{1/2} / |b|^2, the same cap
without the principal character, and rho_E = sum_{chi != chi0}|D_b|^4 / (q |b|^4) (normalised multiplicative energy
mod q: about 2 for random b, about log of the support length for a dilated interval)."""
import sys, math, numpy as np
from sympy import nextprime
from probe import Field, tpm
from bohr import unimod_W

def caps(F, b, W):
    q = F.q; D = F.D(b); P = np.abs(D)**2; nb = np.sum(np.abs(b)**2)
    s = P[np.asarray(W)].sum()/nb
    P0 = P[0]                                   # k = 0 is the principal character
    cap = math.sqrt(len(W)*np.sum(P**2))/nb
    cap_np = math.sqrt(len(W)*(np.sum(P**2) - P0**2))/nb
    rhoE = (np.sum(P**2) - P0**2)/(q*nb**2)
    return s, cap, cap_np, rhoE

if __name__ == '__main__':
    for q0 in sys.argv[1:]:
        q = int(nextprime(int(float(q0)))); F = Field(q); N = F.N; R = int(round(q**(2/3)))
        val, W, b, it = tpm(F, np.ones(len(F.ns), complex), R, iters=80)
        s, cap, capnp, rhoE = caps(F, b, W)
        print(f"q={q} N={N} R={R}: adversarial s1^2={s:9.0f} ({s/q:.3f}q)  4th-moment cap {cap:9.0f}  without chi0 {capnp:9.0f}"
              f"  s/cap={s/capnp:.3f}  rho_E={rhoE:6.2f}  sqrt(qR)={math.sqrt(q*R):8.0f}", flush=True)
        Wu = unimod_W(F, R)
        bb = np.ones(len(F.ns), complex)
        for _ in range(120):
            D = F.D(bb); c = np.zeros_like(D); c[Wu] = D[Wu]; bb = np.exp(1j*np.angle(F.adj(c)))
        s, cap, capnp, rhoE = caps(F, bb, Wu)
        print(f"{'':{len(str(q))+2}s}|b_n|=1 vector: s={s:9.0f} ({s/N:.2f}N)  4th-moment cap {cap:9.0f}  without chi0 {capnp:9.0f}"
              f"  s/cap={s/capnp:.3f}  rho_E={rhoE:6.2f}", flush=True)
