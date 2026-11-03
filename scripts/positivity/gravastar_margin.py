# Uncertified: decay of the junction margin 1 - ||A^{-1/2} B C^{-1/2}|| between the top two dyadic blocks,
# global lambda_min(G), a toy PD control with no arithmetic, and a synthetic off-line zero.
import sys, time, numpy as np, scipy.linalg as sl
sys.path.insert(0, 'scripts'); import ball_orbit as bo
out = open('scripts/positivity/gravastar_margin_results.txt', 'a')
def P(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); out.write(s + "\n"); out.flush()
Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8191
Atab, Btab = bo.tables(Mmax + 2)
def K_H(x): return np.sqrt(x) * bo.kernel_over_sqrt(x, Atab, Btab)
def zero_term(u, beta, g):  # 2 Re e^{(rho-1/2)u}/(rho(1-rho)), rho = beta + i g
    rho = beta + 1j*g; return 2*np.real(np.exp((rho-0.5)*u)/(rho*(1-rho)))
def offline2(delta, g=14.134725):  # move the zero pair at 1/2+-ig to the quartet 1/2+-delta +- ig
    return lambda x: K_H(x) - zero_term(np.log(x), .5, g) + zero_term(np.log(x), .5+delta, g) + zero_term(np.log(x), .5-delta, g)
toys = {"toy sech(u)": lambda x: 2/(x + 1/x), "toy exp(-|u|/2)": lambda x: x**-0.5, "toy Gaussian exp(-u^2/8)": lambda x: np.exp(-np.log(x)**2/8)}
def gram_idx(K, idx_a, idx_b):
    m = idx_a[:, None].astype(float); n = idx_b[None, :].astype(float); hi = np.maximum(m, n); lo = np.minimum(m, n)
    return np.sqrt(m*n) * K(hi/lo)
def margin(K, k):
    a = np.arange(2**(k-2), 2**(k-1)); b = np.arange(2**(k-1), 2**k)
    A, C, B = gram_idx(K, a, a), gram_idx(K, b, b), gram_idx(K, a, b)
    try: La = np.linalg.cholesky(A); Lc = np.linalg.cholesky(C)
    except np.linalg.LinAlgError: return float('nan')
    T = sl.solve_triangular(La, sl.solve_triangular(Lc, B.T, lower=True).T, lower=True)
    return 1 - sl.svdvals(T)[0]
def lmin(K, M):
    i = np.arange(1, M+1); return sl.eigh(gram_idx(K, i, i), eigvals_only=True, subset_by_index=[0, 0])[0]
ks = [k for k in range(8, 15) if 2**k - 1 <= Mmax]
P(f"\n# run Mmax={Mmax}")
P("## prime-side K_H: per M = 2^k-1, margin of top pair, global lambda_min, M*lambda_min")
res = []
for k in ks:
    t0 = time.time(); M = 2**k - 1; mg = margin(K_H, k); lm = lmin(K_H, M); res.append((M, mg, lm))
    P(f"M={M:6d} margin={mg:.4e} lambda_min={lm:.4e} M*lambda_min={M*lm:.4f} ratio margin/lambda_min={mg/lm:.3f} ({time.time()-t0:.0f}s)")
M_, mg_, lm_ = map(np.array, zip(*res))
for lab, y in (("margin", mg_), ("lambda_min", lm_)):
    X = np.stack([np.ones_like(M_), np.log(M_), np.log(np.log(M_))], 1)
    c, r, *_ = np.linalg.lstsq(X, np.log(y), rcond=None)
    c1 = np.polyfit(np.log(M_), np.log(y), 1, cov=True)
    P(f"fit {lab}: pure power a={-c1[0][0]:.3f} +- {np.sqrt(c1[1][0,0]):.3f};  with log: a={-c[1]:.3f}, b={c[2]:.3f} (3 params / {len(y)} points: b poorly determined)")
P("\n## toy controls (no arithmetic), margin per M")
for name, K in toys.items():
    row = []
    for k in ks[:5]:
        row.append(margin(K, k))
    a = -np.polyfit(np.log(2.0**np.array(ks[:5])), np.log(np.abs(row)), 1)[0]
    P(f"{name}: " + " ".join(f"{x:.3e}" for x in row) + f"  -> slope a={a:.3f}")
P("\n## synthetic off-line first zero: 1/2+i14.13 -> quartet 1/2 +- delta + i14.13 (margin; nan = block not PD)")
for d in (0.05, 0.02, 0.01, 0.005):
    K = offline2(d); row = [margin(K, k) for k in ks]; lms = [lmin(K, 2**k-1) for k in ks[:4]]
    P(f"delta={d}: margins " + " ".join(f"{x:.3e}" for x in row) + " | lambda_min " + " ".join(f"{x:.2e}" for x in lms))
