import sys, json, math, random, mpmath as mp, numpy as np
from multiprocessing import Pool
from dcore import *
N = int(sys.argv[1])
def specs():
    S = []
    for D in [5,-3,-4,8,-8,-7,12,13,-11,-15,17,-20,21,-23,24,29,-31,33,-35,37,-43,-47]:
        S.append(('kron(%d/.)' % D, 'kron', D, 0))
    for p, ks in [(5,[1]),(7,[1,2]),(11,[1,2]),(13,[1,2]),(23,[1,2]),(31,[1]),(41,[1,2]),(47,[1])]:
        for k in ks: S.append(('chi_%d^%d' % (p, k), 'prime', p, k))
    for seed in [1,2,3]: S.append(('randsign%d' % seed, 'rand', 5, seed))
    return S
def job(sp):
    label, kind, A_, B_ = sp; mp.mp.dps = 40
    c = char_kron(A_) if kind == 'kron' else char_prime(A_, B_) if kind == 'prime' else char_kron(5)
    lamc = None
    if kind == 'rand':
        rng = random.Random(B_); lamc = [mp.mpf(rng.choice([-1, 1])) for _ in range(N+1)]
    K = Kernel(c, N, lamc); q = len(c); out = []
    cplx = kind == 'prime' and 2*B_ != q-1
    for orbit in ['all', 'coprime']:
        idx = list(range(1, N+1)) if orbit == 'all' else [n for n in range(1, N+1) if math.gcd(n, q) == 1]
        for real in ([False, True] if cplx else [False]):
            G = gram(K, idx, real)
            d = pivots(G); r = [x/d[0] for x in d]
            fin = [(float(x), idx[k]) for k, x in enumerate(r) if x == x]
            below = [(idx[k], float(x)) for k, x in enumerate(r) if x == x and x < 1][:5]
            out.append(dict(label=label, q=q, parity=parity(c), orbit=orbit, symm=real, K1=float(K.K1), d1=float(d[0]),
                            PD=all(x == x and x > 0 for x in d), first_nonpos=next((idx[k] for k, x in enumerate(d) if not (x > 0)), None),
                            n_below=sum(1 for x, _ in fin[1:] if x < 1), below=below, min=min(fin[1:]),
                            at=[(k, float(r[i])) for i, k in enumerate(idx) if k in (2, 3, 5, 10, 50, 100, 200, 300, 500)],
                            last=fin[-1]))
    return out
if __name__ == '__main__':
    with Pool(8) as P: res = sum(P.map(job, specs(), chunksize=1), [])
    json.dump(res, open('res_%d.json' % N, 'w'), indent=0)
    for x in res:
        print(x['label'], x['parity'], x['orbit'], 'symm' if x['symm'] else '', 'K1=%.4f' % x['K1'], 'PD', x['PD'], 'nbelow', x['n_below'],
              'min %.4f@%d' % x['min'], 'last %.3f@%d' % x['last'], x['below'][:3])
