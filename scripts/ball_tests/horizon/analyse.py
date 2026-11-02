import json, numpy as np
from scipy.optimize import curve_fit
R = json.load(open('zeta_eigs.json')); N = np.array([r['N'] for r in R], float)
def fits(y, name):
    m = N >= 50; x = N[m]; Y = np.log(y[m]); res = {}
    laws = {'N^-a': (lambda x, c, a: c - a*np.log(x), [0, 1]),
            'log^b N/N': (lambda x, c, b: c - np.log(x) + b*np.log(np.log(x)), [0, 1]),
            'N^-a log^b N': (lambda x, c, a, b: c - a*np.log(x) + b*np.log(np.log(x)), [0, 1, 1]),
            '1/log^b N': (lambda x, c, b: c - b*np.log(np.log(x)), [0, 1])}
    for k, (f, p0) in laws.items():
        p, cov = curve_fit(f, x, Y, p0=p0); rms = np.sqrt(np.mean((f(x, *p)-Y)**2))
        res[k] = (p.round(4).tolist(), np.sqrt(np.diag(cov)).round(4).tolist(), float('%.2e' % rms))
    print(name); [print('  ', k, v) for k, v in res.items()]
    return res
out = {}
for key in ['lam', 'corr', 'gen']:
    y = np.array([r[key] for r in R]); out[key] = fits(y, key)
    print('   values', ['%.4g' % v for v in y])
# eigenvector localisation
for r in R:
    if r['N'] in (100, 1000, 3000):
        for key in ('v', 'vg'):
            v = np.array(r[key]); v /= np.linalg.norm(v); n = np.arange(1, len(v)+1); p = v**2
            sc = np.sign(v); sign_changes = int(np.sum(sc[1:] != sc[:-1]))
            print(r['N'], key, 'mean n %.1f' % (p@n), 'median n', int(n[np.searchsorted(np.cumsum(p), .5)]),
                  'mass n<=N/10 %.3f' % p[:len(v)//10].sum(), 'mass top half %.3f' % p[len(v)//2:].sum(), 'sign changes', sign_changes,
                  'top |v| at n=', (np.argsort(-abs(v))[:6]+1).tolist())
json.dump(out, open('fits.json', 'w'), indent=1)
