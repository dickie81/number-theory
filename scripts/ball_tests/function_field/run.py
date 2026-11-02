import sys, random, json, math, mpmath as mp, numpy as np
from multiprocessing import Pool
from ffcore import gram, pivots, power_sums
from curves import random_curve, lpoly, rh_ok
mp.mp.dps = 50
def analyse(args):
    label, Pc, q, N, mode = args
    mp.mp.dps = 50
    G = gram(Pc, q, N)
    idx = list(range(1, N+1)) if mode == 'all' else [n for n in range(1, N+1) if n % q]
    sub = G[np.ix_([i-1 for i in idx], [i-1 for i in idx])]
    d = pivots(sub); d1 = d[0]
    tol = mp.mpf(10)**(-30)
    r = [x/d1 for x in d]
    zero = next((idx[k] for k, x in enumerate(r) if not (x > tol)), None)
    below = next((idx[k] for k, x in enumerate(r) if x < 1), None)
    finite = [(x, idx[k]) for k, x in enumerate(r) if x > tol]
    mn = min(finite[1:]) if len(finite) > 1 else (None, None)
    return dict(label=label, Pc=Pc, q=q, g=(len(Pc)-1)//2, N=N, mode=mode, d1=float(d1),
                first_below=below, first_zero=zero, min_ratio=float(mn[0]) if mn[0] is not None else None,
                argmin=mn[1], last=float(r[-1]) if r[-1] == r[-1] else None,
                r_head=[float(x) for x in r[:12]])
def curves_list(rng, per=6):
    out = []
    for q in [2,3,4,5,7,9,11,13]:
        for g in [1,2,3]:
            seen = set(); tries = 0
            while len(seen) < per and tries < 60:
                tries += 1
                f, h = random_curve(q, g, rng)
                c, Ns = lpoly(q, g, f, h)
                if tuple(c) in seen or not rh_ok(c, q): continue
                seen.add(tuple(c)); out.append((f"y2+({h})y={f}", c, q))
        # extremal for square q: maximal (1+sqrt q T)^{2g}, minimal (1-sqrt q T)^{2g}
        r = math.isqrt(q)
        if r*r == q:
            for g in [1,2,3]:
                for sgn, nm in [(1,'maximal'),(-1,'minimal')]:
                    c = [math.comb(2*g,k)*(sgn*r)**k for k in range(2*g+1)]
                    out.append((f"{nm} g={g}" + (" (Hermitian)" if (q,g,sgn)==(9,3,1) or (q,g,sgn)==(4,1,1) else ""), c, q))
    return out
if __name__ == '__main__':
    N = int(sys.argv[1]); mode = sys.argv[2]
    rng = random.Random(2026)
    cl = curves_list(rng)
    jobs = [(l, c, q, N, mode) for l, c, q in cl]
    with Pool(8) as P:
        res = P.map(analyse, jobs)
    json.dump(res, open(f'res_{mode}_{N}.json','w'), indent=0)
    for x in res:
        print(x['q'], x['g'], x['Pc'], 'below', x['first_below'], 'zero', x['first_zero'], 'min', x['min_ratio'], '@', x['argmin'], x['label'][:30])
