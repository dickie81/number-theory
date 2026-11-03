# Uncertified: a tower of Tangherlini black holes D = 4..40, scalar quasinormal modes by 1st-order WKB (Schutz-Will),
# compared with zeta zeros (zeros used ONLY as the comparison target, never as input).
import numpy as np, mpmath as mp
from math import gamma, pi, log
out = open('scripts/positivity/bh_tower_results.txt', 'w')
def P(s): print(s, flush=True); out.write(s + "\n"); out.flush()
area = lambda n: 2*pi**((n+1)/2)/gamma((n+1)/2)  # |S^n|
def qnm(D, l, nmax, rh=1.0):
    f = lambda r: 1 - (rh/r)**(D-3)
    fp = lambda r: (D-3)*rh**(D-3)/r**(D-2)
    V = lambda r: f(r)*(l*(l+D-3)/r**2 + (D-2)*(D-4)*f(r)/(4*r**2) + (D-2)*fp(r)/(2*r))
    r = np.linspace(rh*1.0001, rh*6, 200001); v = V(r); i = np.argmax(v); r0, h = r[i], 1e-4*rh
    d = lambda g, x: f(x)*(g(x+h) - g(x-h))/(2*h)       # d/dr* = f d/dr
    V1 = lambda x: d(V, x); V2 = d(V1, r0)
    return [np.sqrt(complex(v[i], -(n+.5)*np.sqrt(-2*V2))) for n in range(nmax)], v[i]
P("| D | r_h (unit area) | kappa (r_h=1) | T_H | |S^{D-2}| | omega r_h (l=0,n=0) | omega r_h (l=1,n=0) | omega r_h (l=2,n=0) |")
spec_re, spec_im, rows = [], [], []
for D in range(4, 41):
    rhu = area(D-2)**(-1/(D-2)); kap = (D-3)/2; T = kap/(2*pi)
    ws = []
    for l in range(3):
        w, _ = qnm(D, l, 4); ws.append(w[0]); spec_re += [x.real for x in w]; spec_im += [-x.imag for x in w]
    if D <= 10 or D % 10 == 0:
        P(f"| {D} | {rhu:.4f} | {kap:.2f} | {T:.4f} | {area(D-2):.4g} | {ws[0]:.4f} | {ws[1]:.4f} | {ws[2]:.4f} |")
    rows.append((D, kap, ws))
P("check D=4 l=2 n=0 (literature 0.9673-0.1935i in units 2M=1... here r_h=1): " + f"{qnm(4,2,1)[0][0]:.4f}")
z = np.array([float(mp.zetazero(k).imag) for k in range(1, 31)])
def rstat(e):
    e = np.sort(e); s = np.diff(e); s = s[s > 1e-12]; return np.mean(np.minimum(s[1:], s[:-1])/np.maximum(s[1:], s[:-1]))
def fit(x):
    x = np.sort(np.asarray(x))[:30]; A = np.stack([np.ones(30), x], 1); c = np.linalg.lstsq(A, z, rcond=None)[0]
    res = z - A @ c; return np.sqrt(np.mean(res**2)), c
rng = np.random.default_rng(0)
ctrl = [fit(np.sort(rng.uniform(0, 1, 30)))[0] for _ in range(200)]
pick = fit(np.arange(30.))[0]
lnN = fit(np.arange(1, 31) / np.log(np.arange(2, 32)))[0]
P(f"\nzeta zeros 1..30: <r>={rstat(z):.3f}; mean spacing {np.diff(z).mean():.3f}")
P(f"controls (best affine fit to first 30 zeros, rms residual): picket fence {pick:.3f}; uniform random median {np.median(ctrl):.3f}; n/log n {lnN:.3f}")
cands = {
    "Re omega r_h, all levels/l/n": spec_re,
    "Im omega r_h (damping ladder), all": spec_im,
    "Re omega/kappa, all": [x for (D, k, ws) in rows for x in [w.real/k for w in ws]],
    "kappa_D (the shells)": [k for (D, k, ws) in rows],
    "log |S^{D-2}| (shells)": [log(area(D-2)) for D in range(4, 41)],
    "T_H log 3 + i2piT_H(n+1/2) asymptotic ladder (D=4..40, n<4), Im parts": [2*pi*(D-3)/(4*pi)*(n+.5) for D in range(4, 41) for n in range(4)],
}
P("\n| candidate spectrum | <r> | rms residual of best affine fit to 30 zeros | fit (a, b) |")
for k, v in cands.items():
    rm, c = fit(v); P(f"| {k} | {rstat(v):.3f} | {rm:.3f} | ({c[0]:.2f}, {c[1]:.3f}) |")
P("(GUE 0.600, Poisson 0.386, picket fence 1.0; exact degeneracies dropped in <r>)")
