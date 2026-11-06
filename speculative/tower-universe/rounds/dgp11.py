import math, sys
import numpy as np
from scipy import integrate, stats
HERE = sys.path[0]
dat = [l.split() for l in open(f"{HERE}/data/desi_gaussian_bao_ALL_GCcomb_mean.txt") if not l.startswith("#")]
zs = np.array([float(d[0]) for d in dat]); vals = np.array([float(d[1]) for d in dat]); kinds = [d[2] for d in dat]
Cinv = np.linalg.inv(np.loadtxt(f"{HERE}/data/desi_gaussian_bao_ALL_GCcomb_cov.txt"))
def chi2_of(E):
    m = np.empty(len(zs))
    for i, (z, k) in enumerate(zip(zs, kinds)):
        dm = integrate.quad(lambda x: 1 / E(x), 0, z, epsabs=1e-12, epsrel=1e-10)[0]; dh = 1 / E(z)
        m[i] = {"DM_over_rs": dm, "DH_over_rs": dh, "DV_over_rs": (z * dm * dm * dh) ** (1 / 3)}[k]
    a = (m @ Cinv @ vals) / (m @ Cinv @ m); r = vals - a * m
    return float(r @ Cinv @ r), a
def best(fam, grid):
    c, g = min((chi2_of(fam(x))[0], x) for x in grid)
    st = grid[1] - grid[0]
    return min((chi2_of(fam(x))[0], x) for x in np.linspace(g - st, g + st, 81))
lcdm = lambda Om: (lambda z: math.sqrt(Om * (1 + z) ** 3 + 1 - Om))
def dgp(Om):
    orc = ((1 - Om) / 2) ** 2
    return lambda z: math.sqrt(orc) + math.sqrt(orc + Om * (1 + z) ** 3)
power = lambda p: (lambda z: (1 + z) ** (1 / p))
cl, oml = best(lcdm, np.linspace(0.2, 0.4, 41))
cd, omd = best(dgp, np.linspace(0.1, 0.5, 81))
cp, pp = best(power, np.linspace(0.3, 3.0, 136))
for nm, c, par in (("flat ΛCDM", cl, f"Ω_m = {oml:.4f}"), ("DGP self-accelerating", cd, f"Ω_m = {omd:.4f}, Ω_rc = {((1 - omd) / 2) ** 2:.4f}"),
                   ("best power law", cp, f"p = {pp:.3f}")):
    d = c - cl
    sig = stats.norm.isf(stats.chi2.sf(d, 1) / 2) if d > 0 else 0.0
    print(f"{nm:24s} χ² = {c:7.2f} (11 dof, p = {stats.chi2.sf(c, 11):.1e});  Δχ² vs ΛCDM = {d:6.2f} ({sig:.1f}σ);  {par}")
orc = ((1 - omd) / 2) ** 2
print(f"DGP crossover distance r_c = 1/(2 H0 √Ω_rc) = {1 / (2 * math.sqrt(orc)):.2f} Hubble lengths  (a second scale, put in by hand)")
