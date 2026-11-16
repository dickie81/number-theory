"""Round 2 (PREREG2.md): the 3D slice over time (S1, S2) and the adelic split (A1, A2)."""
import math, sys
import numpy as np
from scipy import integrate, stats
from scipy.linalg import lapack

HERE = sys.path[0]
G1, G2 = 14.134725141734693, 21.022039638771555
EG = 0.5772156649015329
H0SUM = 2 + EG - math.log(4 * math.pi)

# ------------------------------------------------------------------ BAO (as in fit.py)
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

print("== S1: a(t) ∝ ‖w_N‖ = √(N·H0), so H·t = 1/2 at all times ==")
c = chi2_of(lambda z: (1 + z) ** 2)
print(f"T1: H0 t0 = 0.500 against 0.950 ± 0.008 ({(0.5 - 0.95) / 0.008:+.0f} sigma)")
print(f"T2: DESI DR2 BAO chi2 = {c:.0f} for 12 dof (flat LCDM 10.3 for 11), p = {stats.chi2.sf(c, 12):.0e}")

# ------------------------------------------------------------------ S2: the slice's shape over time
print("\n== S2: the drawn slice as our space ==")
NMAX = 1 << 21
n = np.arange(1, NMAX + 1, dtype=float); t = np.log(n); r = np.sqrt(2 * n)
r1, r2 = 1 / math.hypot(0.5, G1), 1 / math.hypot(0.5, G2)
X, Y, Z = r * r1 * np.cos(G1 * t), r * r1 * np.sin(G1 * t), r * r2 * np.cos(G2 * t)
cs = {k: np.cumsum(v) for k, v in (("xx", X * X), ("yy", Y * Y), ("zz", Z * Z), ("xy", X * Y), ("xz", X * Z), ("yz", Y * Z))}
del X, Y, Z, r
Ns = np.unique(np.round(np.exp(np.linspace(math.log(1 << 12), math.log(NMAX), 6000))).astype(int))
eig, axis_angle = [], []
for N in Ns:
    i = N - 1
    M = np.array([[cs["xx"][i], cs["xy"][i], cs["xz"][i]], [cs["xy"][i], cs["yy"][i], cs["yz"][i]],
                  [cs["xz"][i], cs["yz"][i], cs["zz"][i]]]) / N
    w, v = np.linalg.eigh(M)
    eig.append(w[::-1]); axis_angle.append(math.atan2(v[1, 2], v[0, 2]))     # in-plane angle of the long axis
eig = np.array(eig); a = np.sqrt(eig); lnN = np.log(Ns)
rates = np.gradient(np.log(a), lnN, axis=0)                                   # H_i t on the integer clock
ratio = a / a[:, :1]
print(f"axis scale factors ∝ √N: mean H·t over the three axes = {rates.mean():.3f}")
for k, nm in enumerate(("long", "middle", "short")):
    print(f"  {nm:6s} axis: size/long = {ratio[:, k].min():.3f}–{ratio[:, k].max():.3f};"
          f" own rate H_i·t from {rates[:, k].min():+.2f} to {rates[:, k].max():+.2f}")
ang = np.unwrap(2 * np.array(axis_angle)) / 2
turn = np.polyfit(lnN, ang, 1)[0]
print(f"  long axis turns at {turn:.2f} rad per unit log N (γ1 = {G1:.2f}): once per ×{math.exp(math.pi / abs(turn)):.3f} in N,"
      f" i.e. {2 * abs(turn):.1f} radians per e-fold of the scale factor")
shear = np.sqrt(((rates - rates.mean(1, keepdims=True)) ** 2).mean(1)) / rates.mean(1)
print(f"  shear σ/H (rms spread of the axes' rates over their mean): median {np.median(shear):.2f}, max {shear.max():.2f}")
print(f"  measured: σ/H < 4.7e-11 (vector mode), < 1.0e-6 (tensor mode)  =>  off by ≥ {np.median(shear) / 1e-6:.0e}")

# ------------------------------------------------------------------ A1, A2: the adelic split
print("\n== A1/A2: the Gram matrix place by place ==")
NC = 4096
lam = np.zeros(NC + 1); comp = np.zeros(NC + 1, bool); primes = []
for p in range(2, NC + 1):
    if not comp[p]:
        primes.append(p); comp[p * p::p] = True
        q = p
        while q <= NC: lam[q] = math.log(p); q *= p
def tail(y):
    out = y - 0.5 * (1 + y) * np.log1p(y)
    with np.errstate(divide="ignore", invalid="ignore"):
        out += np.where(y < 1, 0.5 * (1 - y) * np.log1p(-np.minimum(y, 1 - 1e-300)), 0.0)
    return out
def collapse(lam_used, arch=True, N=NC):
    """Order of the first leading minor that is not positive definite (0: positive definite up to N)."""
    k = np.arange(NC + 1, dtype=float); k[0] = 1
    A = np.cumsum(lam_used / k); B = np.cumsum(lam_used)
    G = np.zeros((N, N), order="F")
    m = np.arange(1, N + 1, dtype=float)
    for j in range(N):                       # column j: rows i >= j, x = m_i / m_j >= 1
        x = m[j:] / m[j]; fl = np.floor(x + 1e-9).astype(int)
        kos = A[fl] - B[fl] / x
        if arch: kos = kos - np.log(x) + 1 + EG - math.log(2 * math.pi) / x + tail(1 / x)
        G[j:, j] = m[j:] * kos
    _, info = lapack.dpotrf(G, lower=1, overwrite_a=1, clean=0)
    return info
full = collapse(lam)
print(f"all places: positive definite to N = {NC}" if full == 0 else f"all places: fails at N = {full} (unexpected)")
print(f"lengths: ‖w_n‖² = n·kos(1), kos(1) = H0 = {H0SUM:.6f}, all of it from the real place (A(1) = ψ(1) = 0)")
print(f"finite places alone: fails at N = {collapse(lam, arch=False)} (no lengths: every diagonal entry is 0)")
print(f"real place alone: fails at N = {collapse(np.zeros_like(lam))}")
print("only the places p ≤ P (with the real place):")
for P in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97):
    keep = lam.copy()
    for p in primes:
        if p > P:
            q = p
            while q <= NC: keep[q] = 0; q *= p
    i = collapse(keep)
    print(f"   P = {P:3d}: fails at N = {i if i else '> ' + str(NC)}")
print("all places but one:")
for p in (2, 3, 5, 7, 11, 13, 31, 101, 307, 1009):
    drop = lam.copy(); q = p
    while q <= NC: drop[q] = 0; q *= p
    i = collapse(drop)
    print(f"   without p = {p:4d}: fails at N = {i if i else '> ' + str(NC)}")
