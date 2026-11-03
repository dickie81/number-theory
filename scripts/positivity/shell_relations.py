# Uncertified: shell-to-shell relations of the black-hole / sphere tower (D = 4..203) vs the first 200 zeta-zero gaps.
# Zeros are only the comparison target. Small memory.
import numpy as np, mpmath as mp
from math import lgamma, log, pi, exp
out = open('scripts/positivity/shell_relations_results.txt', 'w')
def P(s): print(s, flush=True); out.write(s + "\n"); out.flush()
Ds = np.arange(4, 204)
logarea = np.array([log(2) + (D-1)/2*log(pi) - lgamma((D-1)/2) for D in Ds])      # log |S^{D-2}|
kappa = (Ds-3)/2; T = kappa/(2*pi); rh = np.exp(-logarea/(Ds-2))
gratio = np.array([exp(0.5*log(pi) + lgamma((D-1)/2) - lgamma(D/2)) for D in Ds])   # sqrt(pi)G((D-1)/2)/G(D/2)
z = np.array([float(mp.zetazero(k).imag) for k in range(1, 201)])
def unfold_seq(x):  # treat x as levels; unfold by a smooth (cubic in index) fit of the counting function
    x = np.sort(x); k = np.arange(1, len(x)+1); c = np.polyfit(x, k, 3); u = np.polyval(c, x); return u
def rstat(x):
    s = np.diff(np.sort(x)); s = s[s > 1e-12]; return np.mean(np.minimum(s[1:], s[:-1])/np.maximum(s[1:], s[:-1]))
def hist(x):
    s = np.diff(x); s = s/s.mean(); h, _ = np.histogram(s, bins=[0, .25, .5, .75, 1, 1.25, 1.5, 2, 3, 99]); return h/len(s)
rv = lambda t: t/(2*pi)*np.log(t/(2*pi*np.e)) + 7/8
uz = rv(z)  # exact unfolding of the zeros
def count_shape(x):  # fit N(level) = a + b x log x + c x vs a + b x: does x log x thinning help?
    x = np.sort(x); k = np.arange(1, len(x)+1)
    r1 = np.linalg.lstsq(np.stack([np.ones_like(x), x], 1), k, rcond=None)[1]
    with np.errstate(all='ignore'): xl = x*np.log(np.abs(x)+1e-300)
    r2 = np.linalg.lstsq(np.stack([np.ones_like(x), x, xl], 1), k, rcond=None)[1]
    return float(np.sqrt(r1[0]/len(x))) if len(r1) else 0.0, float(np.sqrt(r2[0]/len(x))) if len(r2) else 0.0
seqs = {
    "kappa_D (levels)": kappa, "T_H": T, "unit-area r_h": rh, "log-area increments (cumsum of |diff|)": np.cumsum(np.abs(np.diff(logarea))),
    "-log |S^{D-2}| (levels)": -logarea, "Gamma ratio sqrt(pi)G((D-1)/2)/G(D/2) (levels)": gratio,
    "cumsum of 1/Gamma-ratio": np.cumsum(1/gratio), "cumsum of log D": np.cumsum(np.log(Ds)),
    "control: k/log k": np.arange(2, 202)/np.log(np.arange(2, 202)), "control: evenly spaced": np.arange(200.),
    "control: Poisson": np.cumsum(np.random.default_rng(1).exponential(size=200)),
}
P("reference <r>: GUE 0.600, GOE 0.531, Poisson 0.386, picket fence 1.0")
P("spacing histogram bins (unfolded spacing s): [0,.25,.5,.75,1,1.25,1.5,2,3,inf)")
P(f"| zeta zeros (unfolded by Riemann-von Mangoldt) | <r>={rstat(uz):.3f} | hist {np.round(hist(uz),2).tolist()} |")
P("\n| sequence | <r> (unfolded) | spacing histogram | counting rms: linear / with x log x |")
for k, x in seqs.items():
    u = unfold_seq(x); c = count_shape(x)
    P(f"| {k} | {rstat(u):.3f} | {np.round(hist(np.sort(u)),2).tolist()} | {c[0]:.3f} / {c[1]:.3f} |")
c = count_shape(z); P(f"| zeta zeros (raw) | — | — | {c[0]:.3f} / {c[1]:.3f} |")
# gaps: ratio of consecutive gaps of the raw sequences vs zeros
P(f"\nzeros: gaps mean {np.diff(z).mean():.3f}, gap ratio g_(k+1)/g_k median {np.median(np.diff(z)[1:]/np.diff(z)[:-1]):.3f}")
for k in ("kappa_D (levels)", "-log |S^{D-2}| (levels)", "Gamma ratio sqrt(pi)G((D-1)/2)/G(D/2) (levels)", "cumsum of log D"):
    g = np.abs(np.diff(np.sort(seqs[k]))); P(f"{k}: gap ratio median {np.median(g[1:]/g[:-1]):.3f}, gap CV {g.std()/g.mean():.3f} (zeros {np.diff(z).std()/np.diff(z).mean():.3f})")
