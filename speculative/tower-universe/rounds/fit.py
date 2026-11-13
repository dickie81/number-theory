"""The tower against measurements, by the rules fixed in PREREG.md (T1, T2, T3)."""
import math, sys
import numpy as np
from scipy import integrate, stats
import mpmath as mp

HERE = sys.path[0]
rng = np.random.default_rng(20261106)

# ---------------------------------------------------------------- constants
t_P = 5.391247e-44                      # s, CODATA 2022
Gyr = 3.15576e16                        # s
Mpc = 3.0856775814913673e22             # m
kmsMpc = 1e3 / Mpc                      # 1 km/s/Mpc in 1/s
t0, t0_err = 13.787, 0.020              # Gyr (the value fixed in PREREG.md)
H0 = 67.36                              # Planck 2018 TT,TE,EE+lowE+lensing
H0t0_meas, H0t0_err = 0.950, 0.008      # PREREG.md
OL_meas, OL_err = 0.6847, 0.0073

LSTAR, B = 0.0429, 0.032                # lambda_N * N = LSTAR log N + B
N_now = t0 * Gyr / t_P
L_now = math.log(N_now)

def nlam(N):                            # N * lambda_N, the model's law
    return LSTAR * math.log(N) + B

def inv_pi(tau):                        # N with pi(N) = tau (asymptotic inverse of li)
    l = math.log(tau); ll = math.log(l)
    return tau * (l + ll - 1 + (ll - 2) / l - (ll * ll - 6 * ll + 11) / (2 * l * l))

print(f"N_now = t0/t_P = {N_now:.4e}, log N_now = {L_now:.3f}")
print(f"  (age +- 0.020 Gyr moves log N by {0.020/13.787:.1e}; Planck's lensing column 13.797 Gyr: "
      f"{math.log(13.797*Gyr/t_P):.3f})")

# ---------------------------------------------------------------- T1
print("\n== T1: no free parameters ==")
Nl = nlam(N_now)
lo_cls, hi_thm = 0.0400 * L_now, 0.04294 * L_now
lo_prov = math.sqrt(L_now) / (220 * math.e ** 8)
print(f"N*lambda_N at N_now: law {Nl:.3f}; arithmetic class [{lo_cls:.2f}, {hi_thm:.2f}];"
      f" proven under RH only [{lo_prov:.1e}, {hi_thm:.2f}]")
tau_now = N_now
N_pc = inv_pi(tau_now)
tl = tau_now * nlam(N_pc) / N_pc
print(f"prime clock: pi(N) = {tau_now:.3e} at N = {N_pc:.3e}; tau*lambda_N = {tl:.4f}")

rows = []
# D1: H t = N lambda_N
p1 = Nl; q1 = -1 + 1 / p1 - LSTAR / p1 ** 2
rows.append(("D1 rate, integer clock", p1, q1, None))
# D2: H t = tau lambda_N, a power law
p2 = tl; q2 = -1 + 1 / p2
rows.append(("D2 rate, prime clock", p2, q2, None))
# D3, D4: (8 pi G/3) rho_vac t^2 = V. With matter and a bang at t = 0 the solution is a ~ t^(2/3) exactly
# when V < 4/9, with Omega_vac = 9V/4 for all time; V > 4/9 leaves no matter: a ~ t^sqrt(V).
for name, X in (("D3 density, integer clock", Nl), ("D4 density, prime clock", tl)):
    for units, V in (("G=1", 8 * math.pi / 3 * X ** 2), ("8piG=1", None)):
        if V is None:   # reduced units: t unit sqrt(8pi) t_P, density unit 1/(8 pi G tbar^2)
            Nb = N_now / math.sqrt(8 * math.pi)
            if "prime" in name:
                Np = inv_pi(Nb); Xb = Nb * nlam(Np) / Np
            else:
                Xb = nlam(Nb)
            V = Xb ** 2 / 3
        if V < 4 / 9:
            rows.append((f"{name} [{units}]", 2 / 3, 0.5, 9 * V / 4))
        else:
            p = math.sqrt(V); rows.append((f"{name} [{units}]", p, -1 + 1 / p, 1.0))
print(f"{'reading':38s} {'H0 t0':>8s} {'q0':>7s} {'Omega_vac':>10s}   measured: H0t0 = {H0t0_meas} +- {H0t0_err},"
      f" q0 = -0.53, Omega_L = {OL_meas}")
for name, p, q, ov in rows:
    ovs = "-" if ov is None else f"{ov:.3f}"
    print(f"{name:38s} {p:8.3f} {q:7.3f} {ovs:>10s}   H0t0 off by {(p - H0t0_meas)/H0t0_err:+8.0f} sigma")

# ---------------------------------------------------------------- T2
print("\n== T2: shape only, DESI DR2 BAO (13 points, full covariance, H0 r_d free) ==")
dat = [l.split() for l in open(f"{HERE}/data/desi_gaussian_bao_ALL_GCcomb_mean.txt") if not l.startswith("#")]
zs = np.array([float(d[0]) for d in dat]); vals = np.array([float(d[1]) for d in dat]); kinds = [d[2] for d in dat]
Cinv = np.linalg.inv(np.loadtxt(f"{HERE}/data/desi_gaussian_bao_ALL_GCcomb_cov.txt"))

def chi2_of(E):
    """E: callable E(z) = H/H0. Returns chi2 minimised analytically over alpha = c/(H0 r_d)."""
    m = np.empty(len(zs))
    for i, (z, k) in enumerate(zip(zs, kinds)):
        dm = integrate.quad(lambda x: 1 / E(x), 0, z, epsabs=1e-12, epsrel=1e-10)[0]
        dh = 1 / E(z)
        m[i] = {"DM_over_rs": dm, "DH_over_rs": dh, "DV_over_rs": (z * dm * dm * dh) ** (1 / 3)}[k]
    a = (m @ Cinv @ vals) / (m @ Cinv @ m)
    r = vals - a * m
    return float(r @ Cinv @ r), a

def best(fam, grid):
    res = [(chi2_of(fam(g))[0], g) for g in grid]
    c, g = min(res)
    fine = np.linspace(g - (grid[1] - grid[0]), g + (grid[1] - grid[0]), 81)
    return min((chi2_of(fam(x))[0], x) for x in fine)

lcdm = lambda Om: (lambda z: math.sqrt(Om * (1 + z) ** 3 + 1 - Om))
power = lambda p: (lambda z: (1 + z) ** (1 / p))
def d1(p):          # H t = A L, L = log(t/t_P): E = (L/L0) e^(L0 - L), L = sqrt(L0^2 - (2 L0/p) log(1+z))
    L0 = L_now
    def E(z):
        L = math.sqrt(L0 * L0 - 2 * L0 / p * math.log1p(z)); return L / L0 * math.exp(L0 - L)
    return E
eds = lambda z: (1 + z) ** 1.5

c_l, Om = best(lcdm, np.linspace(0.20, 0.40, 41))
c_d1, pd1 = best(d1, np.linspace(0.5, 3.0, 51))
c_pw, ppw = best(power, np.linspace(0.5, 3.0, 51))
c_eds = chi2_of(eds)[0]
dof = len(zs) - 2
out = [("flat LCDM (Omega_m free)", c_l, f"Omega_m = {Om:.4f}", dof),
       ("D1 shape (H t = A log t)", c_d1, f"H0 t0 = {pd1:.3f}", dof),
       ("D2 shape (power law)", c_pw, f"p = {ppw:.3f}", dof),
       ("D3/D4 shape (a ~ t^2/3)", c_eds, "none", len(zs) - 1)]
for name, c, par, k in out:
    pv = stats.chi2.sf(c, k)
    nsig = stats.norm.isf(stats.chi2.sf(c - c_l, 1) / 2) if c > c_l else 0.0
    print(f"{name:28s} chi2 = {c:8.2f}  dof {k:2d}  p = {pv:.1e}  dchi2 vs LCDM = {c - c_l:7.1f}"
          f" ({nsig:.1f} sigma)   best {par}")
# the D1 dictionary's own amplitude in the shape test
c_own = chi2_of(d1(Nl))[0]
print(f"D1 with its own amplitude (H0 t0 = {Nl:.2f}): chi2 = {c_own:.1f}")

# ---------------------------------------------------------------- T3
print("\n== T3: numerology audit ==")
mp.mp.dps = 20
gam = [float(mp.zetazero(k).imag) for k in range(1, 101)]
Hsum = 2 + float(mp.euler) - math.log(4 * math.pi)
w = [2 / (0.25 + g * g) / Hsum for g in gam]
cum = np.cumsum(w)
n_below_100 = sum(1 for g in gam if g < 100)
share = {k: cum[k - 1] for k in (1, 2, 3, 5, 10, n_below_100, 50, 100)}
print("shares:", {k: round(v, 4) for k, v in share.items()}, f"(zeros below 100: {n_below_100})")
# (name, value, abs precision, kind) -- every pure number reported for the model in this conversation or the repo
M = []
for k, v in share.items(): M.append((f"share of first {k} zeros", v, 1e-6, "frac"))
for p, v in ((2, .229), (3, .219), (5, .180), (7, .149)): M.append((f"tick drop at {p}", v, 5e-4, "frac"))
M += [("x_1 share of thin direction", .870, 5e-4, "frac"), ("primes' share of decay", .406, 5e-4, "frac"),
      ("fence exponent 3/5", .6, 1e-9, "frac"), ("N lambda at N=32768", .4829, 5e-5, "frac"),
      ("H0 = sum 1/|rho|^2", Hsum, 1e-9, "num"), ("constant Lambda* 0.0429", .0429, 1e-4, "num"),
      ("fit slope 0.0434", .0434, 1e-4, "num"), ("fit offset 0.032", .032, 5e-4, "num"),
      ("profile kappa 0.096", .096, 5e-4, "num"), ("correction 0.0316", .0316, 5e-5, "num"),
      ("inverse-theorem 0.0400", .0400, 5e-5, "num")]
for N, v in ((2048, .0547), (4096, .0541), (8192, .0530), (16384, .0525), (32768, .0518)):
    M.append((f"tau*lambda at N={N}", v, 5e-5, "num"))
M += [("gamma_1", gam[0], 1e-9, "num"), ("gamma_2", gam[1], 1e-9, "num"), ("gamma_3", gam[2], 1e-9, "num"),
      ("gamma_2/gamma_1", gam[1] / gam[0], 1e-9, "num"), ("gamma_3/gamma_1", gam[2] / gam[0], 1e-9, "num"),
      ("log N_now", L_now, 2e-3, "num"), ("N/pi(N) at N_now", N_now / (N_now / (L_now - 1 - 1 / L_now)), 2e-3, "num"),
      ("N lambda at N_now", Nl, 2e-2, "num"), ("tau*lambda at N_now", .0439, 2e-4, "num"),
      ("pivot ratio 182.06", 182.06, 5e-3, "num"), ("room per integer 94", 94, .5, "num"),
      ("room per integer 181", 181, .5, "num"), ("room per tick 550", 550, .5, "num"),
      ("room per tick 1864", 1864, .5, "num"), ("integers per tick 5.87", 5.87, 5e-3, "num"),
      ("integers per tick 10.29", 10.29, 5e-3, "num")]
# headline dimensionless measurements: (name, value, sigma)
P = [("1/alpha", 137.035999177, 2.1e-8), ("alpha_s(M_Z)", .1180, .0009), ("sin^2 theta_W(M_Z)", .23129, .00004),
     ("m_p/m_e", 1836.152673426, 3.2e-8), ("m_mu/m_e", 206.7682827, 4.6e-6), ("m_tau/m_e", 3477.23, .23),
     ("m_tau/m_mu", 16.8170, .0011), ("m_n/m_p", 1.00137841946, 4e-10), ("m_W/m_Z", .88136, .00015),
     ("m_H/m_Z", 1.37299, .0012), ("m_t/m_Z", 1.8925, .0033), ("m_H/m_W", 1.5578, .0014),
     ("|V_us|", .2243, .0008), ("|V_cb|", .0411, .0012), ("|V_ub|", .00382, .0002), ("sin^2 theta_12", .307, .013),
     ("sin^2 theta_23", .558, .018), ("sin^2 theta_13", .02195, .00058), ("dm2_21/dm2_32", .03067, .00081),
     ("a_e", .00115965218059, 1.3e-13), ("a_mu", .00116592072, 1.5e-10),
     ("Omega_Lambda", .6847, .0073), ("Omega_m", .3153, .0073), ("Omega_b", .0493, .0009), ("Omega_c", .2645, .005),
     ("f_b = Omega_b/Omega_m", .1564, .003), ("n_s", .9649, .0042), ("sigma_8", .8111, .006),
     ("tau_reio", .0544, .0073), ("z_reio", 7.67, .73), ("z_*", 1089.92, .25), ("z_drag", 1059.94, .30),
     ("z_eq", 3402, 26), ("100 theta_*", 1.04110, .00031), ("N_eff", 2.99, .17), ("Y_p", .2453, .0034),
     ("H0 t0", .950, .008), ("ln(1e10 A_s)", 3.044, .014)]
mv = np.array([m[1] for m in M]); ms = np.array([m[2] for m in M]); frac = np.array([m[3] == "frac" for m in M])
pv = np.array([p[1] for p in P]); ps = np.array([p[2] for p in P])
print(f"{len(M)} model numbers, {len(P)} measurements")

FACT = [(1, "1"), (2, "2"), (3, "3"), (4, "4"), (.5, "1/2"), (1 / 3, "1/3"), (.25, "1/4"), (math.pi, "pi"),
        (1 / math.pi, "1/pi"), (2 * math.pi, "2pi"), (1 / (2 * math.pi), "1/2pi"), (4 * math.pi, "4pi"),
        (1 / (4 * math.pi), "1/4pi"), (8 * math.pi, "8pi"), (1 / (8 * math.pi), "1/8pi"), (math.e, "e"), (1 / math.e, "1/e")]
OPS = [("x", lambda x, s: (x, s)), ("1/x", lambda x, s: (1 / x, s / x ** 2)),
       ("1-x", lambda x, s: (np.where(x < 1, 1 - x, np.nan), s)), ("x^2", lambda x, s: (x * x, 2 * x * s)),
       ("sqrt x", lambda x, s: (np.sqrt(x), s / (2 * np.sqrt(x))))]
LEVELS = {"L0": (OPS[:1], FACT[:1]), "L1": (OPS, FACT[:1]), "L2": (OPS, FACT)}

def forms(x, s, level):
    ops, fac = LEVELS[level]
    vs, ss, labels = [], [], []
    for on, f in ops:
        v, e = f(x, s)
        for c, cn in fac:
            vs.append(c * v); ss.append(c * e); labels.append((on, cn))
    return np.stack(vs, -1), np.stack(ss, -1), labels          # (..., nM, nF)

def zmat(x, s, level):
    V, S, labels = forms(x, s, level)
    Z = np.abs(V[..., None] - pv) / np.sqrt(S[..., None] ** 2 + ps ** 2)
    return np.nan_to_num(Z, nan=np.inf), labels                 # (..., nM, nF, nP)

def null_draw(R):
    u = rng.random((R, len(mv)))
    x = np.where(frac, u, mv * 10 ** (u - 0.5))
    x = np.maximum(np.round(x / (2 * ms)), 1) * (2 * ms)   # quoted to the same decimals as the model's numbers
    return x, np.broadcast_to(ms, x.shape)

for level, R in (("L0", 20000), ("L1", 20000), ("L2", 4000)):
    Z, labels = zmat(mv, ms, level)
    order = np.argsort(Z, axis=None)[:5]
    zbest = Z.flat[order[0]]
    hits = []
    for o in order:
        i, f, j = np.unravel_index(o, Z.shape)
        on, cn = labels[f]
        form = (on if cn == "1" else f"{cn}*({on})").replace("x", M[i][0]) if on != "x" or cn != "1" else M[i][0]
        hits.append(f"{form} = {forms(mv[i:i+1], ms[i:i+1], level)[0][0, f]:.5g} ~ {P[j][0]} = {P[j][1]:.5g}"
                    f" ({Z[i, f, j]:.2f} sigma)")
    nb, nc = [], []
    for k in range(0, R, 200):
        x, s = null_draw(min(200, R - k))
        Zn = zmat(x, s, level)[0].reshape(x.shape[0], -1)
        nb.append(Zn.min(1)); nc.append((Zn < 1).sum(1))
    nb, nc = np.concatenate(nb), np.concatenate(nc)
    n_obs = int((Z < 1).sum())
    print(f"\n{level}: best match {zbest:.4f} sigma; random model numbers do at least this well in"
          f" {100*(nb <= zbest).mean():.1f}% of {R} draws (median best {np.median(nb):.4f} sigma)")
    for h in hits: print("   ", h)
    print(f"    matches within 1 sigma: {n_obs}; random: median {np.median(nc):.0f}, at least {n_obs} in"
          f" {100*(nc >= n_obs).mean():.0f}% of draws")
