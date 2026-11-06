"""Post-hoc (not pre-registered): add the CMB shift parameter R = √Ω_m ∫_0^z* dz/E (Planck 2018 compressed:
R = 1.7502 ± 0.0046, Chen, Huang & Wang 2019) to the DESI DR2 BAO fit, for ΛCDM and self-accelerating DGP."""
import math, sys
import numpy as np
from scipy import integrate, stats
HERE = sys.path[0]
exec(open(f"{HERE}/dgp11.py").read().split("lcdm = ")[0])
Or = 4.176e-5 / 0.68 ** 2                     # photons + 3.044 neutrinos, h = 0.68
ZS = 1089.9
def E_l(Om): return lambda z: math.sqrt(Om * (1 + z) ** 3 + Or * (1 + z) ** 4 + 1 - Om - Or)
def E_d(Om):
    orc = ((1 - Om - Or) / 2) ** 2
    return lambda z: math.sqrt(orc) + math.sqrt(orc + Om * (1 + z) ** 3 + Or * (1 + z) ** 4)
def R(E, Om): return math.sqrt(Om) * integrate.quad(lambda z: 1 / E(z), 0, ZS, limit=400)[0]
for nm, fam in (("flat ΛCDM", E_l), ("DGP self-accelerating", E_d)):
    rows = []
    for Om in np.linspace(0.15, 0.70, 221):
        E = fam(Om); cb = chi2_of(E)[0]; r = R(E, Om); cr = ((r - 1.7502) / 0.0046) ** 2
        rows.append((cb + cr, Om, cb, r))
    c, Om, cb, r = min(rows)
    print(f"{nm:24s} BAO + CMB: χ² = {c:7.2f} at Ω_m = {Om:.3f} (BAO part {cb:.2f}, R = {r:.4f})")
    if nm.startswith("flat"): cl = c
d = c - cl
print(f"DGP worse than ΛCDM by Δχ² = {d:.1f} ({stats.norm.isf(stats.chi2.sf(d, 1) / 2):.1f}σ)")
