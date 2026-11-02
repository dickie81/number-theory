import sys, time, math
from multiprocessing import Pool
from k2 import *
def work(q):
    ctx.prec = 96
    out = []; best = None
    G = flint.dirichlet_group(q) if hasattr(flint, 'dirichlet_group') else None
    for n in range(1, q):
        if math.gcd(n, q) != 1: continue
        c = dirichlet_char(q, n)
        if not c.is_primitive(): continue
        if mode == 'real' and not c.is_real(): continue
        K1, K2, l = char_k2(c)
        ratio = 2*(1 - abs(K2)**2/K1**2)
        rm = float(ratio.mid())
        out.append((rm, q, n, c.parity(), float(K1.mid()), float(abs(K2).mid()), bool(ratio < 1), bool(ratio > 1)))
    out.sort()
    return out[:3], sum(o[6] for o in out), sum(not o[7] for o in out), len(out)
if __name__ == '__main__':
    Q0, Q1, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    t = time.time()
    with Pool(8) as P: R = P.map(work, range(Q0, Q1+1), chunksize=4)
    allw = sorted(sum((r[0] for r in R), []))
    print('chars', sum(r[3] for r in R), 'certified d2<d1:', sum(r[1] for r in R), 'not certified >1:', sum(r[2] for r in R), 'time', time.time()-t)
    for w in allw[:25]: print('ratio %.5f q=%d n=%d a=%d K1=%.4f |K2|=%.4f fail=%s' % w[:7])
