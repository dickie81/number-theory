import json, numpy as np, matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
R = json.load(open('zeta_eigs.json')); C = json.load(open('contrast.json'))
N = np.array([r['N'] for r in R])
fig, ax = plt.subplots(1, 2, figsize=(12, 4.5))
for key, lab in [('lam_d1', 'zeta lam_min(G)/d1'), ('corr', 'zeta lam_min(corr)'), ('gen', 'zeta lam_min(G, d1*min)')]:
    ax[0].loglog(N, [r[key] for r in R], 'o-', label=lab)
x = np.linspace(50, 3000); ax[0].loglog(x, np.exp(-2.8146)*np.log(x)**0.8851/x/R[0]['lam']*R[0]['lam_d1']*0+np.exp(-2.8146)*np.log(x)**0.8851/x/0.0461914, 'k--', lw=.8, label='fit ~log^0.89 N / N')
for k, mk in [('chi19_3', 's'), ('curve13', '^')]:
    t = np.array(C[k]); t = t[t[:, 2].real > 1e-12]
    ax[0].loglog(t[:, 0].real, t[:, 2].real, mk+':', label=k+' lam_min/d1')
ax[0].set_xlabel('N'); ax[0].legend(fontsize=7); ax[0].set_title('smallest eigenvalues')
for r in R:
    if r['N'] in (300, 3000):
        for key, ls in [('v', '-'), ('vg', '--')]:
            v = np.array(r[key]); v /= v[0]; n = np.arange(1, len(v)+1)
            ax[1].semilogx(n, v*n, ls, lw=.7, label=f"N={r['N']} {'G' if key=='v' else 'G vs flat'}: n*v_n")
ax[1].set_xlabel('n'); ax[1].legend(fontsize=7); ax[1].set_title('lowest eigenvector times n')
plt.tight_layout(); plt.savefig('horizon.png', dpi=130)
