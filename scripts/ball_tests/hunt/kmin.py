"""Where does min_k d_k/d_1 sit?  The exact k <= 3 criterion (arb) against the pivots up to N (float64).

Write B_{mn} = K(m/n)/K_1 for the cosines between the orbit vectors w_m, w_n. Then d_k/d_1 = k det B_k / det B_{k-1}, so
with u = K(2)/K_1, v = K(3)/K_1, w = K(3/2)/K_1:
    d_2/d_1 = 2(1 - |u|^2),    d_3/d_1 = 3(1 - |u|^2 - |v|^2 - |w|^2 + 2 Re(u w conj v)) / (1 - |u|^2).
By Theorem A' (x >= 1, y = 1/x), K(x) = sqrt(x) * br(x) with
    br(x) = K_1 + S(x) + (1-a)(1 - (1 + log x) y) + b(1 - y) - C_a + t_a(y),   S(x) = sum_{n<=x} chi(n) Lambda(n)(1/n - 1/x),
    t_0(y) = y + (1-y)log(1-y)/2 - (1+y)log(1+y)/2,   t_1(y) = (1+y)log(1+y)/2 + (1-y)log(1-y)/2,
and b = -log(q/pi) + gamma + log 2 - conj(L'/L(1, chi)) as in k2.py. S(2) = S(3/2) = 0 and S(3) = chi(2) log(2)/6, so
d_2/d_1 and d_3/d_1 are closed forms in K_1, L'/L(1, chi), the parity and chi(2).

    python3 kmin.py Q0 Q1 all|real N     # every (or every real) primitive character mod q, Q0 <= q <= Q1; pivots k <= N
    python3 kmin.py zeta N               # the same for zeta
    python3 kmin.py check                # the float64 Gram matrix against dirichlet/dcore.py (mpmath)
"""
import os, sys, math, time, cmath
for v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(v, '1')  # one BLAS thread per worker; the pool supplies the parallelism
from multiprocessing import Pool
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..'))
from ball_orbit import primes_upto  # noqa: E402
from flint import arb, acb, dirichlet_char, dirichlet_group, ctx  # noqa: E402
import k2  # noqa: E402
from scan import labels  # noqa: E402

GAMMA, LOG2 = 0.5772156649015329, math.log(2)


def lam(N):
    """Lambda(n) for n <= N."""
    L = np.zeros(N+1)
    for p in primes_upto(N):
        pk = p
        while pk <= N: L[pk] = math.log(p); pk *= p
    return L


def t0(y):
    with np.errstate(divide='ignore', invalid='ignore'):
        r = y + np.where(y < 1, (1-y)*np.log1p(-np.minimum(y, 1-1e-300))/2, 0) - (1+y)*np.log1p(y)/2
    return r


def t1(y):
    with np.errstate(divide='ignore', invalid='ignore'):
        return (1+y)*np.log1p(y)/2 + np.where(y < 1, (1-y)*np.log1p(-np.minimum(y, 1-1e-300))/2, 0)


def gram(N, chi, K1, b, a, zeta=False):
    """G(m, n) = sqrt(mn) K(m/n) = m br(m/n) for m >= n, from the closed form; chi = array of chi(n), n <= N."""
    Lm = lam(N); cl = chi*Lm; n_ = np.arange(N+1, dtype=float); n_[0] = 1
    A = np.cumsum(cl/n_); B = np.cumsum(cl); A[0] = B[0] = 0
    m, n = np.tril_indices(N); m = m+1; n = n+1
    x = m/n; y = n/m; k = m//n
    if zeta:
        br = A[k] - B[k]*y - np.log(x) + 1 + GAMMA - math.log(2*math.pi)*y + t0(y)
    else:
        Ca, ta = (1-LOG2, t0(y)) if a == 0 else (LOG2, t1(y))
        br = K1 + A[k] - B[k]*y + (1-a)*(1 - (1+np.log(x))*y) + b*(1-y) - Ca + ta
    G = np.zeros((N, N), dtype=complex)
    G[m-1, n-1] = m*br
    iu = np.triu_indices(N, 1); G[iu] = np.conj(G.T[iu])
    return G


def pivots(G):
    try:
        L = np.linalg.cholesky(G); return np.abs(np.diag(L))**2
    except np.linalg.LinAlgError:
        A = G.copy(); d = []
        for j in range(len(A)):
            p = A[j, j].real; d.append(p)
            if not p > 0: break
            A[j+1:, j+1:] -= np.outer(A[j+1:, j], np.conj(A[j+1:, j]))/p
        return np.array(d)


def k3_exact(K1, ell, a, q, chi2):
    """d_2/d_1 and d_3/d_1 as arb balls (chi2 = chi(2) as acb; q = 1 for zeta, with ell ignored)."""
    g = arb.const_euler(); l2 = arb(2).log(); pi = arb.pi()

    def br(x):  # x = Fraction-like (num, den)
        X = arb(x[0])/x[1]; y = 1/X
        S = chi2*l2/6 if x == (3, 1) else acb(0)
        if q == 1:
            return S - X.log() + 1 + g - (2*pi).log()*y + (y + (1-y)*(1-y).log()/2 - (1+y)*(1+y).log()/2)
        b = -(arb(q)/pi).log() + g + l2 - ell.conjugate()
        if a == 0:
            Ca = 1 - l2; ta = y + (1-y)*(1-y).log()/2 - (1+y)*(1+y).log()/2
        else:
            Ca = l2; ta = (1+y)*(1+y).log()/2 + (1-y)*(1-y).log()/2
        return K1 + S + (1-a)*(1 - (1+X.log())*y) + b*(1-y) - Ca + ta
    u = arb(2).sqrt()*br((2, 1))/K1; v = arb(3).sqrt()*br((3, 1))/K1; w = (arb(3)/2).sqrt()*br((3, 2))/K1
    au, av, aw = abs(u)**2, abs(v)**2, abs(w)**2
    r2 = 2*(1 - au)
    r3 = 3*(1 - au - av - aw + 2*(u*w*v.conjugate()).real)/(1 - au)
    return r2, r3


def chi_values(c, q, N):
    e = int(dirichlet_group(q).exponent()); out = np.zeros(N+1, dtype=complex)
    for n in range(1, N+1):
        if math.gcd(n, q) == 1:
            out[n] = cmath.exp(2j*math.pi*int(c.chi_exponent(n % q))/e)
    return out


def row(K1f, bf, a, q, chi, N, r2, r3, zeta=False):
    d = pivots(gram(N, chi, K1f, bf, a, zeta)); r = d/d[0]
    kmin = int(np.argmin(r[1:]))+2
    below = [k+1 for k in range(1, len(r)) if r[k] < 1]
    dev = max(abs(r[1]-float(r2.mid())), abs(r[2]-float(r3.mid())))
    return dict(kmin=kmin, rmin=float(r[kmin-1]), first_below=below[0] if below else None, n_below=len(below),
                pd=bool(len(d) == N and d[-1] > 0), dev=dev, r=r)


def work(args):
    q, mode, N = args
    ctx.prec = 96; out = []
    for n in labels(q, mode):
        c = dirichlet_char(q, n)
        if not c.is_primitive(): continue
        if mode == 'real' and not c.is_real(): continue
        K1, _, ell = k2.char_k2(c); a = c.parity()
        chi = chi_values(c, q, N)
        r2, r3 = k3_exact(K1, ell, a, q, acb(chi[2].real, chi[2].imag))
        K1f = float(K1.mid()); lf = complex(float(ell.real.mid()), float(ell.imag.mid()))
        bf = -math.log(q/math.pi) + GAMMA + LOG2 - lf.conjugate()
        R = row(K1f, bf, a, q, chi, N, r2, r3)
        out.append((q, n, a, K1f, float(r2.mid()), float(r3.mid()), bool(r2 < 1), bool(r2 > 1), bool(r3 < 1), bool(r3 > 1),
                    R['kmin'], R['rmin'], R['first_below'], R['n_below'], R['pd'], R['dev'],
                    [float(R['r'][k-1]) for k in (5, 10, 50, 100) if k <= N]))
    return out


def check():
    """Compare the float64 closed-form Gram matrix with dirichlet/dcore.py (mpmath) for a few characters."""
    sys.path.insert(0, os.path.join(HERE, '..', 'dirichlet'))
    import mpmath as mp
    import dcore
    mp.mp.dps = 30; N = 40; worst = 0
    for name, c in [('kron(5)', dcore.char_kron(5)), ('kron(-4)', dcore.char_kron(-4)), ('kron(-163)', dcore.char_kron(-163)),
                    ('chi_7^1', dcore.char_prime(7, 1)), ('chi_13^2', dcore.char_prime(13, 2)), ('chi_19^1', dcore.char_prime(19, 1))]:
        q = len(c); K = dcore.Kernel(c, N); Gm = dcore.gram(K, list(range(1, N+1)))
        chi = np.array([0] + [complex(c[n % q]) for n in range(1, N+1)])
        G = gram(N, chi, float(K.K1), complex(K.b), K.a)
        err = max(abs(complex(Gm[i, j]) - G[i, j]) for i in range(N) for j in range(N))/abs(G).max()
        dm = dcore.pivots(Gm); dp = pivots(G)
        perr = max(abs(float(mp.re(dm[k]))/float(mp.re(dm[0])) - dp[k]/dp[0]) for k in range(N))
        worst = max(worst, err, perr)
        print('%-11s q=%3d a=%d  rel entry err %.1e  pivot-ratio err %.1e' % (name, q, K.a, err, perr))
    # flint's b against dcore's b, matching characters by their values
    ctx.prec = 96
    for name, cd in [('kron(5)', dcore.char_kron(5)), ('kron(-4)', dcore.char_kron(-4)), ('kron(-163)', dcore.char_kron(-163)),
                     ('chi_7^1', dcore.char_prime(7, 1)), ('chi_13^2', dcore.char_prime(13, 2)), ('chi_19^1', dcore.char_prime(19, 1))]:
        q = len(cd); K = dcore.Kernel(cd, 3)
        for n in labels(q, 'all'):
            c = dirichlet_char(q, n)
            if c.is_primitive() and all(abs(complex(c(j).mid()) - complex(cd[j])) < 1e-12 for j in range(q)):
                K1, _, ell = k2.char_k2(c)
                bf = -math.log(q/math.pi) + GAMMA + LOG2 - complex(float(ell.real.mid()), float(ell.imag.mid())).conjugate()
                worst = max(worst, abs(float(K1.mid()) - float(K.K1)), abs(bf - complex(K.b)))
                print('%-11s = flint label %3d:  |K1 flint - dcore| %.1e   |b flint - dcore| %.1e' % (
                    name, n, abs(float(K1.mid()) - float(K.K1)), abs(bf - complex(K.b))))
    print('worst', worst)


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check()
    elif sys.argv[1] == 'zeta':
        N = int(sys.argv[2]); ctx.prec = 128
        K1 = 2 + arb.const_euler() - (4*arb.pi()).log()
        r2, r3 = k3_exact(K1, None, 0, 1, acb(1))
        chi = np.ones(N+1); chi[0] = 0
        R = row(float(K1.mid()), 0, 0, 1, chi, N, r2, r3, zeta=True)
        print('zeta d2/d1', r2, 'd3/d1', r3, 'min %.6f at k=%d' % (R['rmin'], R['kmin']), 'first below', R['first_below'], 'dev %.1e' % R['dev'])
    else:
        Q0, Q1, mode, N = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
        t = time.time()
        with Pool(os.cpu_count()) as P: R = sum(P.map(work, [(q, mode, N) for q in range(Q0, Q1+1)], chunksize=2), [])
        import json
        json.dump(R, open('kmin_%s_%d_%d_N%d.json' % (mode, Q0, Q1, N), 'w'))
        nf2 = sum(r[6] for r in R); nf3 = sum(r[8] and not r[6] for r in R)
        unc = sum(not (r[6] or r[7]) or not (r[8] or r[9]) for r in R)
        late = [r for r in R if r[7] and r[9] and r[12] is not None]
        print('chars', len(R), '| d2<d1 certified', nf2, '| d3<d1<=d2 certified', nf3, '| k<=3 uncertified', unc,
              '| pass k<=3 but some d_k<d_1 (k<=%d)' % N, len(late), '| not PD', sum(not r[14] for r in R),
              '| max |float-arb| at k<=3 %.1e' % max(r[15] for r in R), '| time %.0f' % (time.time()-t))
        from collections import Counter
        print('argmin k:', sorted(Counter(min(r[10], 11) for r in R).items()), '(11 = k>10)')
        for r in sorted(late, key=lambda r: r[11])[:20]:
            print('LATE q=%d n=%d a=%d K1=%.4f d2/d1=%.4f d3/d1=%.4f min %.5f@%d first_below %s n_below %d'
                  % (tuple(r[:6]) + (r[11], r[10], r[12], r[13])))
        print('closest passes (min ratio over k<=N among chars with no d_k<d_1):')
        for r in sorted([r for r in R if r[12] is None], key=lambda r: r[11])[:8]:
            print('   q=%d n=%d a=%d K1=%.4f d2/d1=%.4f d3/d1=%.4f min %.5f@%d' % (tuple(r[:6]) + (r[11], r[10])))
