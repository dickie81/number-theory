"""Round 3 (PREREG3.md): the view from inside at N_now."""
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
    return float(r @ Cinv @ r)
LCDM = min(chi2_of(lambda z, Om=Om: math.sqrt(Om * (1 + z) ** 3 + 1 - Om)) for Om in np.linspace(0.29, 0.31, 81))
c = chi2_of(lambda z: 1 + z)
print("== O1: a ∝ t from inside (both clocks) ==")
print(f"T1: H0 t0 = 1.000; Planck (assumes LCDM) 0.950 ± 0.008: {(1 - 0.95) / 0.008:+.1f} sigma;"
      f" cosmology-independent 0.92–1.03: inside")
print(f"T2: DESI DR2 BAO chi2 = {c:.1f} for 12 dof (p = {stats.chi2.sf(c, 12):.0e}); flat LCDM {LCDM:.1f} for 11;"
      f" dchi2 = {c - LCDM:.1f} ({stats.norm.isf(stats.chi2.sf(c - LCDM, 1) / 2):.1f} sigma for one parameter)")
print("\n== O2: what marks 'now' from inside ==")
L = math.log(8.0702e60)
print(f"share of new integers that are prime: 1/log N = 1/{L:.1f}; changes by {100 / L:.2f}% per e-fold of time")
print(f"N·λ_N = 0.0429 log N + 0.032 = {0.0429 * L + 0.032:.3f}; changes by {100 * 0.0429 / (0.0429 * L + 0.032):.2f}% per e-fold")
Om = 0.315; Ht = 0.95
print(f"our universe: Omega_Lambda changes by {100 * 3 * Om * Ht:.0f}% per e-fold of time (d ln Ω_Λ/d ln a = 3Ω_m, × H·t)")
# the view of the past from now depends only on N/n: corr(w_N, w_n) = K(N/n)/K(1)
print("the view of the past: corr(w_N, w_n) = K(N/n)/H0 depends on N/n = 1 + z alone (exact, from G = √(mn)·K(m/n))")
