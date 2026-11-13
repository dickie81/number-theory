"""The shortest-vector form of the orbit-lattice conjecture on the analogues of docs/ball-conjecture-tests.md.

(B): every nonzero integer combination of the orbit vectors w_1, ..., w_N has squared norm at least ||w_1||^2 = d_1.
For zeta, (B) for every N is equivalent to RH (Lean: PivotSharp.rh_iff_shortest), as is the pivot form (A): d_k >= d_1
for every k (PivotSharp.rh_iff_orbitLattice). This script tests (B) on the analogues where (A) is known to fail.

Integer coefficients see only the real part of a Hermitian Gram matrix: Q(a) = a^T (Re G) a. So for a complex character
(B) concerns Re G. If (B) fails at a vector whose last nonzero entry sits at index k, then d_k(Re G) <= a_k^2 d_k(Re G)
<= Q(a) < d_1: (B) fails only where (A) for Re G does, and (A) for Re G fails only where (A) for G does.

The k = 2 identity. Every orbit Gram matrix has G_nn = n G_11, so G_22 = 2 d_1, and for a real Gram matrix
  d_2 = 2 d_1 - G_12^2/d_1 < d_1  <=>  |G_12| > d_1  <=>  Q(delta_2 - sgn(G_12) delta_1) = 3 d_1 - 2|G_12| < d_1:
(B) fails on the lattice spanned by w_1, w_2 exactly when (A) fails at k = 2.

The analogues:
  curves-all   the same formula as for zeta, with the zeros of a curve's zeta function (ball-conjecture-tests.md §4), on
               n = 1..N, N <= NC, below the first forced zero q^d (next item);
  curves-cop   the same on the first NC indices prime to q, where no forced zero occurs;
  relation     Theorem C is integral. w_{q^a} = sum_j alpha_j^a P_j w_1, so if m(z) = sum_k m_k z^(d-k) is the minimal
               polynomial of Frobenius (the squarefree part of L*(z) = z^(2g) L(1/z), monic with integer coefficients),
               the integer vector with entry m_k at n = q^(d-k) has Q = 0: (B) fails for every curve at N = q^d.
               Checked in exact rational arithmetic (G is log q times a rational matrix);
  frobenius    the orbit of Frobenius powers (Hallouin-Perret): the lattice Z[z]/(m), basis 1, z, ..., z^(d-1), with
               the form T(P) = sum_j |P(alpha_j)|^2, Gram T_ij = q^min(i,j) s_|i-j| (s_k the power sums), integral, and
               T(1) = 2g. If m is irreducible then L* = m^e, and prod_j P(alpha_j) = Res(m, P)^e is a nonzero integer for
               P not 0 mod m, so AM-GM gives T(P) >= 2g: (B) holds by integrality. Searched otherwise. (A) fails at
               z^d, which depends on the lower powers (pivot 0);
  chars        every primitive Dirichlet character mod q <= QALL and every real one mod q <= QREAL, on n = 1..NCH, from
               the float64 closed form of hunt/kmin.py. The N = 2 decisions are certified in arb (hunt/k2.py), and so is
               the smallest vector below d_1 of every failure.
  zeta         the reference: under RH the Lean proof gives Q(a) >= 0.0577 = 1.249 d_1 for every integer a other than
               +-delta_1 (PivotSharp.lattice_gap).
For each case the script also reports the second minimum s_2: the least Q(a)/d_1 over integer a other than 0, +-delta_1
(Fincke-Pohst up to 1.5 d_1; recorded as None above that). (B) fails exactly when s_2 < 1; in the flat model
(G = d_1 min(m, n)) every increment delta_n - delta_(n-1) has Q = d_1, so s_2 = 1.

Usage: python3 shortest.py [QALL QREAL]   (defaults 400 10000; from this directory; writes res.json, every row, and out.txt)
       python3 shortest.py --report       (rebuilds out.txt from res.json)
"""
import sys, os, math, re, json
for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')  # one BLAS thread per worker; the pool supplies the parallelism
from fractions import Fraction as F
from multiprocessing import Pool
import numpy as np, mpmath as mp, sympy as sp
HERE = os.path.dirname(os.path.abspath(__file__))
for _d in ('function_field', 'hunt'):
    sys.path.insert(0, os.path.join(HERE, '..', _d))
from ffcore import gram as ffgram, pivots as mp_pivots, power_sums, Tval  # noqa: E402
import kmin, k2  # noqa: E402
from scan import labels  # noqa: E402
from flint import arb, acb, dirichlet_char, ctx  # noqa: E402

NC, NCH = 20, 12          # windows: curves, characters
RADIUS = 1.5              # Fincke-Pohst radius, in units of d_1
TIE = 1e-9                # float vectors within this relative distance of d_1 are rechecked exactly


def enum(G, R, thresh, max_nodes=2_000_000):
    """Fincke-Pohst on the positive definite float Gram G: the least x^T G x over integer x other than 0 and +-e_1 with
    value <= R, its x, every x with value < thresh, and whether the node budget ran out."""
    n = len(G)
    U = np.linalg.cholesky(G).T            # G = U^T U, U upper triangular
    dg = np.diag(U) ** 2
    mu = U / np.diag(U)[:, None]
    x = [0] * n
    st = dict(best=math.inf, bx=None, below=[], nodes=0, trunc=False)

    def rec(i, rem):
        st['nodes'] += 1
        if st['nodes'] > max_nodes:
            st['trunc'] = True; return
        c = -sum(mu[i, j] * x[j] for j in range(i + 1, n))
        r = math.sqrt(max(rem, 0.0) / dg[i])
        for v in range(math.ceil(c - r - 1e-9), math.floor(c + r + 1e-9) + 1):
            t = rem - dg[i] * (v - c) ** 2
            if t < -1e-12 * R: continue
            x[i] = v
            if i == 0:
                if any(x[1:]) or abs(x[0]) > 1:
                    val = R - t
                    if val < st['best']: st['best'], st['bx'] = val, list(x)
                    if val < thresh: st['below'].append((val, list(x)))
            else:
                rec(i - 1, t)
        x[i] = 0
    rec(n - 1, R)
    return st['best'], st['bx'], st['below'], st['trunc']


def cert(x, y):
    """Compare arb balls: 'lt' if x < y certainly, 'gt' if x > y certainly, else 'undecided'."""
    return 'lt' if x < y else 'gt' if x > y else 'undecided'


# ---------------------------------------------------------------------------------------------------------- curves
def load_curves():
    """The 148 L-polynomials of ball-conjecture-tests.md §4, from function_field/out_all150.txt."""
    out = []
    for line in open(os.path.join(HERE, '..', 'function_field', 'out_all150.txt')):
        m = re.match(r'(\d+) (\d+) \[([^\]]*)\]', line)
        if m: out.append((int(m.group(1)), int(m.group(2)), [int(t) for t in m.group(3).split(',')], line.split('  ')[-1].strip()))
    return out


def gram_exact(Pc, q, idx):
    """G(m, n)/log q for m, n in idx, as Fractions: ffcore's closed form."""
    T = Tval(Pc, q); top = max(idx); J = 0
    while q ** (J + 1) <= top: J += 1
    s = power_sums(Pc, q, J)
    A = [T + sum(s[:j + 1]) for j in range(J + 1)]
    B = [T - sum(F(s[i], q ** i) for i in range(1, j + 1)) for j in range(J + 1)]

    def g(m, n):
        if m < n: m, n = n, m
        j0 = 0
        while q ** (j0 + 1) * n <= m: j0 += 1
        return n * A[j0] + m * B[j0]
    return [[g(m, n) for n in idx] for m in idx]


def qexact(Gx, a):
    return sum(a[i] * a[j] * Gx[i][j] for i in range(len(a)) for j in range(len(a)) if a[i] and a[j])


def curve_window(Pc, q, idx):
    """(A) and (B) for the curve's orbit on the indices idx: pivots at dps 40, short vectors rechecked exactly."""
    G = ffgram(Pc, q, max(idx))
    sub = G[np.ix_([i - 1 for i in idx], [i - 1 for i in idx])]
    d = mp_pivots(sub); d1 = d[0]
    pd = all(x == x and x > 0 for x in d)
    tol = mp.mpf(10) ** -30
    out = dict(idx=idx, pd=pd, d2_over_d1=float(d[1] / d1),
               A_first_fail=next((idx[k] for k in range(1, len(d)) if d[k] == d[k] and d[k] < d1 * (1 - tol)), None))
    if not pd:
        return out
    Gf = np.array([[float(sub[i, j]) for j in range(len(idx))] for i in range(len(idx))])
    best, bx, below, trunc = enum(Gf, RADIUS * float(d1), float(d1) * (1 + TIE))
    Gx = gram_exact(Pc, q, idx); d1x = Gx[0][0]
    fails, ties = [], 0
    for _, x in below:
        r = qexact(Gx, x) / d1x
        if r < 1: fails.append((r, x))
        elif r == 1: ties += 1
    fails.sort()
    _, _, below2, _ = enum(Gf[:2, :2], RADIUS * float(d1), float(d1) * (1 + TIE))
    first2 = any(qexact(Gx, x + [0] * (len(idx) - 2)) < d1x for _, x in below2)
    out.update(s2=float(best / float(d1)) if bx else None, trunc=trunc, ties=ties, B_fails=bool(fails), B_first2=first2,
               B_min_over_d1=float(fails[0][0]) if fails else None,
               B_vector={idx[i]: c for i, c in enumerate(fails[0][1]) if c} if fails else None)
    return out


def curve_job(args):
    q, g, Pc, label = args
    mp.mp.dps = 40
    res = dict(q=q, g=g, Pc=Pc, label=label)
    z = sp.symbols('z')
    Lstar = sp.Poly(sum(c * z ** (2 * g - k) for k, c in enumerate(Pc)), z)
    m = sp.Poly(sp.sqf_part(Lstar.as_expr()), z)
    mc = [int(c) for c in m.all_coeffs()]
    if mc[0] < 0: mc = [-c for c in mc]
    assert mc[0] == 1, mc
    dm = len(mc) - 1
    # relation: entry m_(d-i) at n = q^i
    a = [mc[dm - i] for i in range(dm + 1)]
    Q = qexact(gram_exact(Pc, q, [q ** i for i in range(dm + 1)]), a)
    res['relation'] = dict(deg_m=dm, N=q ** dm, Q_zero=(Q == 0), vec={q ** i: a[i] for i in range(dm + 1) if a[i]})
    res['all'] = curve_window(Pc, q, list(range(1, min(NC, q ** dm - 1) + 1)))
    res['cop'] = curve_window(Pc, q, [n for n in range(1, 10 * NC) if n % q][:NC])
    # frobenius: Z[z]/(m), T_ij = q^min(i,j) s_|i-j|, an integral form
    s = power_sums(Pc, q, dm)
    T = [[q ** min(i, j) * s[abs(i - j)] for j in range(dm)] for i in range(dm)]
    A = [[F(v) for v in row] for row in T]; piv = []      # exact LDL pivots
    for k in range(dm):
        p = A[k][k]; piv.append(p)
        for i in range(k + 1, dm):
            f = A[i][k] / p
            for j in range(k + 1, dm): A[i][j] -= f * A[k][j]
    best, bx, below, _ = enum(np.array(T, dtype=float), RADIUS * 2 * g, 2 * g + 0.5)
    exact = sorted((qexact(T, x), x) for _, x in below)       # T(P) is an integer: exact
    fails = [e for e in exact if e[0] < 2 * g]
    fl = sp.factor_list(m.as_expr())[1]
    res['frobenius'] = dict(deg_m=dm, m_irreducible=(len(fl) == 1), Lstar_factors=[(str(f), e) for f, e in sp.factor_list(Lstar.as_expr())[1]],
                            A_first_fail=next((k for k in range(1, dm) if piv[k] < piv[0]), None),
                            s2=float(best / (2 * g)) if bx else None, ties=sum(1 for e in exact if e[0] == 2 * g),
                            B_fails=bool(fails), B_min=fails[0][0] if fails else None, B_vector=fails[0][1] if fails else None)
    return res


# ------------------------------------------------------------------------------------------------------ characters
def arb_ratio(K1, ell, a, q, chi, vec):
    """Q(a)/d_1 in arb for the integer vector vec (dict n -> a_n): Re of the closed form, as in kmin.exact_small.
    q = 1 means zeta (K1, ell, a ignored)."""
    N = max(vec)
    g = arb.const_euler(); l2 = arb(2).log(); pi = arb.pi()
    Lam = [arb(0)] * (N + 1)
    for p in kmin.primes_upto(N):
        pk = p
        while pk <= N: Lam[pk] = arb(p).log(); pk *= p
    A = [acb(0)] * (N + 1); B = [acb(0)] * (N + 1)
    for n in range(1, N + 1): A[n] = A[n - 1] + chi[n] * Lam[n] / n; B[n] = B[n - 1] + chi[n] * Lam[n]
    if q == 1: K1 = 2 + g - (4 * pi).log()
    else: b = -(arb(q) / pi).log() + g + l2 - ell.conjugate()

    def G(m, n):
        if m == n: return m * K1
        if m < n: m, n = n, m
        X = arb(m) / n; y = arb(n) / m; k = m // n; S = A[k] - B[k] * y
        t0 = y + (1 - y) * (1 - y).log() / 2 - (1 + y) * (1 + y).log() / 2
        if q == 1: return (m * (S - X.log() + 1 + g - (2 * pi).log() * y + t0)).real
        Ca, ta = (1 - l2, t0) if a == 0 else (l2, (1 + y) * (1 + y).log() / 2 + (1 - y) * (1 - y).log() / 2)
        return (m * (K1 + S + (1 - a) * (1 - (1 + X.log()) * y) + b * (1 - y) - Ca + ta)).real
    Q = arb(0)
    for m in vec:
        for n in vec:
            Q += vec[m] * vec[n] * G(m, n)
    return Q / K1


def lattice_row(R, d1f, certify, radius=RADIUS):
    """(B) on the float Gram R: second minimum, and the smallest vector below d_1 certified by certify(vec)."""
    best, bx, below, trunc = enum(R, radius * d1f, d1f * (1 + TIE))
    row = dict(s2=best / d1f if bx else None, trunc=trunc, B='pass', B_vec=None, B_ratio=None)
    for _, x in sorted(below)[:3]:
        vec = {i + 1: c for i, c in enumerate(x) if c}
        r = certify(vec); c = cert(r, arb(1))
        if c == 'lt':
            row.update(B='fail', B_vec=vec, B_ratio=float(r.mid())); break
        if c == 'undecided': row['B'] = 'undecided'
    return row


def char_job(args):
    q, mode = args
    ctx.prec = 96
    out = []
    for n in labels(q, mode):
        c = dirichlet_char(q, n)
        if not c.is_primitive(): continue
        real = bool(c.is_real())
        if mode == 'real' and not real: continue
        K1, K2, ell = k2.char_k2(c); a = c.parity()
        G12 = arb(2).sqrt() * K2                    # G(2, 1) = sqrt(2) K(2)
        chi = kmin.chi_values(c, q, NCH)
        K1f = float(K1.mid()); lf = complex(float(ell.real.mid()), float(ell.imag.mid()))
        bf = -math.log(q / math.pi) + kmin.GAMMA + kmin.LOG2 - lf.conjugate()
        G = kmin.gram(NCH, chi, K1f, bf, a)
        R = np.ascontiguousarray(G.real)
        dH, dR = kmin.pivots(G), kmin.pivots(R)
        row = dict(q=q, n=n, a=a, real=real, A2=cert(abs(G12), K1), B2=cert(abs(G12.real), K1),
                   A_herm=next((k + 1 for k in range(1, len(dH)) if dH[k] < K1f), None),
                   A_real=next((k + 1 for k in range(1, len(dR)) if dR[k] < K1f), None),
                   pd=bool(len(dR) == NCH and dR[-1] > 0))
        if row['pd']:
            chia = [c(j) for j in range(NCH + 1)]
            row.update(lattice_row(R, K1f, lambda vec: arb_ratio(K1, ell, a, q, chia, vec)))
        out.append(row)
    return out


def zeta_rows():
    ctx.prec = 96
    out = []
    for N in (NCH, 30):
        G = kmin.gram(N, np.ones(N + 1), 0.0, 0.0, 0, zeta=True).real
        d1 = float(2 + 0.5772156649015329 - math.log(4 * math.pi))
        row = lattice_row(np.ascontiguousarray(G), d1, lambda vec: arb_ratio(None, None, 0, 1, [acb(1)] * (max(vec) + 1), vec),
                          radius=3)
        row['N'] = N
        if row['s2'] is not None:   # certify the second minimum's vector too
            best, bx, _, _ = enum(np.ascontiguousarray(G), 3 * d1, 0)
            r = arb_ratio(None, None, 0, 1, [acb(1)] * (N + 1), {i + 1: v for i, v in enumerate(bx) if v})
            row.update(s2_vec={i + 1: v for i, v in enumerate(bx) if v}, s2_arb=str(r))
        out.append(row)
    return out


# ------------------------------------------------------------------------------------------------------------ main
def f6(x):
    return 'None' if x is None else f'{x:.6f}'


def summarise_chars(name, rows, lines):
    n = len(rows); nr = sum(r['real'] for r in rows)
    cnt = lambda f: sum(1 for r in rows if f(r))
    lines.append(f"{name}: {n} characters ({nr} real, {n - nr} complex); positive definite on n <= {NCH}: {cnt(lambda r: r['pd'])}")
    lines.append(f"  (A) for G at k = 2 (arb): fails {cnt(lambda r: r['A2'] == 'gt')}, undecided {cnt(lambda r: r['A2'] == 'undecided')}; "
                 f"(A) for G fails at some k <= {NCH} (float): {cnt(lambda r: r['A_herm'] is not None)}")
    lines.append(f"  (A) for Re G fails at some k <= {NCH} (float): {cnt(lambda r: r['A_real'] is not None)}, "
                 f"of which first at k = 2: {cnt(lambda r: r['A_real'] == 2)}")
    lines.append(f"  (B) at N = 2 (arb): fails {cnt(lambda r: r['B2'] == 'gt')}, undecided {cnt(lambda r: r['B2'] == 'undecided')}")
    lines.append(f"  (B) for N <= {NCH}: fails {cnt(lambda r: r.get('B') == 'fail')} (certified in arb), "
                 f"undecided {cnt(lambda r: r.get('B') == 'undecided')}, enumeration truncated {cnt(lambda r: r.get('trunc'))}; "
                 f"fails although (B) holds at N = 2: {cnt(lambda r: r.get('B') == 'fail' and r['B2'] == 'lt')}")
    lines.append(f"  consistency: every failure at N = 2 found by the search: "
                 f"{all(r.get('B') == 'fail' for r in rows if r['pd'] and r['B2'] == 'gt')}; "
                 f"every failure on n <= 2 is one at N = 2: {all(r['B2'] == 'gt' for r in rows if r.get('B') == 'fail' and max(r['B_vec']) <= 2)}; "
                 f"(B) at N = 2 fails iff (A) for Re G fails at k = 2: {all((r['B2'] == 'gt') == (r['A_real'] == 2) for r in rows if r['pd'])}; "
                 f"(B) fails only where (A) for Re G does: {all(r['A_real'] is not None for r in rows if r.get('B') == 'fail')}")
    for real in (True, False):
        sub = [r for r in rows if r['real'] == real]
        if sub:
            lines.append(f"  {'real' if real else 'complex'}: {len(sub)}; (A) for G fails at k = 2: {sum(1 for r in sub if r['A2'] == 'gt')}; "
                         f"(B) fails: {sum(1 for r in sub if r.get('B') == 'fail')}, at N = 2: {sum(1 for r in sub if r['B2'] == 'gt')}")
    ok = [r for r in rows if r.get('B') == 'pass' and r['s2'] is not None]
    if ok:
        m = min(ok, key=lambda r: r['s2'])
        lines.append(f"  passing characters: least second minimum s_2 = {f6(m['s2'])} (q = {m['q']}, label {m['n']}); "
                     f"s_2 < 1.01: {sum(1 for r in ok if r['s2'] < 1.01)}; s_2 above {RADIUS}: {cnt(lambda r: r.get('B') == 'pass' and r['s2'] is None)}")
    for r in rows:
        if r.get('B') == 'fail' and r['B2'] == 'lt':
            lines.append(f"  not at N = 2: q = {r['q']} label {r['n']} parity {r['a']} real {r['real']}: Q/d_1 = {f6(r['B_ratio'])} at "
                         f"{r['B_vec']}; (A) for Re G first fails at k = {r['A_real']}, for G at k = {r['A_herm']}")
        if r.get('B') == 'undecided' or r['B2'] == 'undecided' or r.get('trunc'):
            lines.append(f"  check: q = {r['q']} label {r['n']}: B = {r.get('B')}, B2 = {r['B2']}, truncated {r.get('trunc')}")


def summarise_curves(cr, lines):
    for key in ('all', 'cop'):
        rr = [x[key] for x in cr]
        cnt = lambda f: sum(1 for r in rr if f(r))
        win = sorted(set(len(r['idx']) for r in rr))
        lines.append(f"curves-{key}: {len(rr)} curves, windows of {win[0]}..{win[-1]} indices; positive definite: {cnt(lambda r: r['pd'])}")
        lines.append(f"  (A) fails in the window: {cnt(lambda r: r['A_first_fail'] is not None)} "
                     f"(at the second index: {cnt(lambda r: r['A_first_fail'] == r['idx'][1])})")
        lines.append(f"  (B) fails in the window (exact): {cnt(lambda r: r.get('B_fails'))}, on the first two indices: "
                     f"{cnt(lambda r: r.get('B_first2'))}, only beyond them: {cnt(lambda r: r.get('B_fails') and not r.get('B_first2'))}; "
                     f"(B) fails only where (A) does: {all(r['A_first_fail'] is not None for r in rr if r.get('B_fails'))}; "
                     f"curves with exact ties Q = d_1: {cnt(lambda r: r.get('ties'))}; truncated: {cnt(lambda r: r.get('trunc'))}")
        if key == 'all':
            lines.append(f"  k = 2 identity, (B) fails at N = 2 iff d_2 < d_1: "
                         f"{all((r['d2_over_d1'] < 1) == bool(r.get('B_first2')) for r in rr)}")
        ok = [r for r in rr if r['pd'] and not r.get('B_fails') and r.get('s2') is not None]
        lines.append(f"  passing curves: least second minimum s_2 = {f6(min((r['s2'] for r in ok), default=None))}; "
                     f"(A) fails but (B) holds: {cnt(lambda r: r['A_first_fail'] is not None and r['pd'] and not r.get('B_fails'))}")
    rel = [x['relation'] for x in cr]
    Ns = sorted(r['N'] for r in rel)
    lines.append(f"relation: Q = 0 exactly for {sum(r['Q_zero'] for r in rel)} of {len(rel)} curves, so (B) fails at N = q^deg(m); "
                 f"N ranges over {Ns[0]}..{Ns[-1]}, median {Ns[len(Ns) // 2]}; N <= {NC}: {sum(1 for v in Ns if v <= NC)}")
    fr = [x['frobenius'] for x in cr]
    lines.append(f"frobenius: {len(fr)} curves; m irreducible: {sum(r['m_irreducible'] for r in fr)}; "
                 f"(B) fails: {sum(r['B_fails'] for r in fr)}; curves with ties T(P) = 2g at P other than +-1: {sum(1 for r in fr if r['ties'])}; "
                 f"(A) fails below z^deg(m): {sum(1 for r in fr if r['A_first_fail'] is not None)}; "
                 f"least second minimum T(P)/2g: {f6(min((r['s2'] for r in fr if r['s2'] is not None), default=None))}")


def int_keys(data):
    """JSON turns integer keys into strings: turn the index -> coefficient maps back."""
    def fix(d, k):
        if isinstance(d.get(k), dict): d[k] = {int(i): v for i, v in d[k].items()}
    for r in data['zeta']: fix(r, 'B_vec'); fix(r, 's2_vec')
    for x in data['curves']:
        fix(x['relation'], 'vec'); fix(x['all'], 'B_vector'); fix(x['cop'], 'B_vector')
    for r in data['chars_all'] + data['chars_real']: fix(r, 'B_vec')
    return data


def report(data):
    zr, cr, ch_all, ch_real = data['zeta'], data['curves'], data['chars_all'], data['chars_real']
    lines = []
    for r in zr:
        lines.append(f"zeta, n <= {r['N']}: (B) {r['B']}; second minimum s_2 = {f6(r['s2'])} at {r.get('s2_vec')} (arb: {r.get('s2_arb')})")
    summarise_curves(cr, lines)
    summarise_chars(f"all primitive characters, q <= {data['QALL']}", ch_all, lines)
    summarise_chars(f"real primitive characters, q <= {data['QREAL']}", ch_real, lines)
    lines.append('')
    for x in cr:
        f = x['frobenius']
        if not f['m_irreducible'] or f['B_fails'] or f['ties']:
            lines.append(f"frobenius: q={x['q']} g={x['g']} L={x['Pc']} L*={f['Lstar_factors']} m irreducible={f['m_irreducible']} "
                         f"(B) fails={f['B_fails']} ties={f['ties']} s_2={f6(f['s2'])}")
    for key in ('all', 'cop'):
        for x in cr:
            r = x[key]
            if r['A_first_fail'] is not None and r['pd'] and not r.get('B_fails'):
                lines.append(f"curves-{key}, (A) fails at n = {r['A_first_fail']} but (B) holds: q={x['q']} g={x['g']} L={x['Pc']} s_2={f6(r['s2'])}")
            if r.get('B_fails') and not r.get('B_first2'):
                lines.append(f"curves-{key}, (B) fails only beyond the first two indices: q={x['q']} g={x['g']} L={x['Pc']} "
                             f"Q/d_1={f6(r['B_min_over_d1'])} at {r['B_vector']}")
    return lines


def cached(name, fn):
    """Compute fn() once and keep it in part_<name>.json, so that an interrupted run resumes where it stopped."""
    f = os.path.join(HERE, f'part_{name}.json')
    if not os.path.exists(f):
        json.dump(fn(), open(f + '.tmp', 'w'), default=str)
        os.replace(f + '.tmp', f)
    return f, json.load(open(f))


if __name__ == '__main__':
    path = os.path.join(HERE, 'res.json')
    if len(sys.argv) > 1 and sys.argv[1] == '--report':      # rebuild out.txt from res.json
        data = int_keys(json.load(open(path)))
    else:
        QALL = int(sys.argv[1]) if len(sys.argv) > 1 else 400
        QREAL = int(sys.argv[2]) if len(sys.argv) > 2 else 10000
        parts = []
        with Pool(4) as P:
            def chars(mode, q0, q1, chunk):
                f, rows = cached(f'{mode}_{q0}_{q1}', lambda: [r for rr in P.map(char_job, [(q, mode) for q in range(q0, q1 + 1)],
                                                                                    chunksize=chunk) for r in rr])
                parts.append(f); return rows
            f, cr = cached('curves', lambda: P.map(curve_job, load_curves())); parts.append(f)
            ch_all = chars('all', 3, QALL, 4)
            ch_real = [r for q0 in range(3, QREAL + 1, 2000) for r in chars('real', q0, min(q0 + 1999, QREAL), 16)]
        f, zr = cached('zeta', zeta_rows); parts.append(f)
        json.dump(dict(QALL=QALL, QREAL=QREAL, zeta=zr, curves=cr, chars_all=ch_all, chars_real=ch_real), open(path, 'w'), default=str)
        for f in parts: os.remove(f)
        data = int_keys(json.load(open(path)))                   # format what was saved
    lines = report(data)
    open(os.path.join(HERE, 'out.txt'), 'w').write('\n'.join(lines) + '\n')
    print('\n'.join(lines))
