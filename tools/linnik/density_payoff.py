#!/usr/bin/env python3
"""density_payoff.py [VARIANT ...]: what a lower density curve would buy the route, by replaying its certificate.

Each variant is a hypothetical density curve made from the committed curve `g7d` (`SieveTypeIIU22240D.lean`, read by
`route_limits.parse`). For each, the script computes an admissible window as `route_limits.py run` does (the sampled
scan, then the exact corners, moving an end inward by `10⁻⁵` while a corner fails, here with no limit on the number of
moves), replays the library's certificate on it with `mirror2.py` (`total2`, depths up to 6, `n = 340`, in exact
integers), and reports the lowest exponent `L` it passes: it starts at the library's `278/125`, which must pass, lowers
`L` by `1/1000` while `total2 < 0.999K`, and then tests once the value `1/2000` below the last one passed. These are
computations, not theorems, and nothing in the library depends on them: the variants are curves no Lean theorem gives.

Variants (several may be given; with none, all of the list below are run, in about half an hour):

* `today`: `g7d` itself.
* `ingham`: `g7d` with the trivial count on `[11/20, 4/7]` replaced by Ingham's estimate (one step, exponent
  `3/(2 − 4/7) + 10⁻⁵`, as `LinnikInghamC.charDensity_ingham_c` gives at a small `ε`), and the slack of the Ingham
  steps on `[4/7, 5/7]` set to `10⁻⁵` (it is `1/2000` on all but the last). Below `4/7` the trivial count is `g7d = 1`,
  which equals `(7/3)(1 − σ)` at `σ = 4/7`: a second place where the curve's exponent is `7/3`, besides `σ = 5/7`.
* `cap:A` (for example `cap:2.32`, `cap:30/13`): `ingham` with every step's exponent capped at `A`.
* `rawcap:A`: `g7d` with every step's exponent capped at `A`, without the change below `4/7`.
* `gm`: `ingham` with every step inside `[7/10, 8/10]` at most `max(15/(3 + 5σ), 3/(2σ), (18 − 20σ)/(6(1 − σ)))`
  at its left end, plus `10⁻⁵`: Chen–Gupta–Li's bound (their Theorem 1.2 at `q₁ = q`) without its first term, the
  term that gives `4/(1 + σ)`. On `[7/10, 8/10]` the maximum is Guth and Maynard's `15/(3 + 5σ)`.
* `V+hb`, for any variant `V` above: also every step on `[15/19, 11/12]` at most `2 + 10⁻⁵` (Heath-Brown's density
  estimate for the characters to one modulus, exponent `2` for `15/19 ≤ σ ≤ 1`; the step containing `15/19` is split
  there).
* `classical`: `g7d` without Chen–Gupta–Li, its steps on `[5/7, 131/168]` replaced by steps of `1/1680` with the
  classical exponents and the slack `1/2000` of the library's steps: Ingham's `3/(2 − σ₊) + 1/2000` up to `3/4` and
  Huxley's `3/(3σ₋ − 1) + 1/2000` from `3/4` (the forms of `LinnikInghamC.charDensity_ingham_c` and of
  `LinnikHuxStep.charDensity_gen`, whose parameters at this width were checked for the first Huxley step only). Its
  search starts at `23/10` (`STARTS`), since `278/125` fails. The window is then set at `3/4`, where Ingham's and
  Huxley's exponents are both `12/5`.

Needs Python 3 only (and `mirror2.py`, which uses all cores).
"""
import os
import re
import subprocess
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import route_limits as rl  # noqa: E402

N = 340
OK = 0.999
START = Fr(278, 125)
STARTS = {'classical': Fr(23, 10)}   # the search's first L for a variant that fails at START
STEP, FINE = Fr(1, 1000), Fr(1, 2000)
SLACK = Fr(1, 100000)
DEFAULT = ['today', 'ingham', 'rawcap:30/13', 'cap:2.33', 'cap:2.325', 'cap:2.32', 'cap:2.315', 'cap:30/13', 'gm',
           'today+hb', 'ingham+hb', 'cap:30/13+hb', 'gm+hb', 'classical']


def ingham(pieces):
    """The trivial count on `[11/20, 4/7]` replaced by one Ingham step; every Ingham step's slack cut to `10⁻⁵`."""
    out = []
    for lo, hi, A in pieces:
        if A is None and (lo, hi) == (Fr(1, 2), Fr(4, 7)):
            out += [(lo, Fr(11, 20), None), (Fr(11, 20), hi, 3 / (2 - hi) + SLACK)]
        elif A is not None and Fr(4, 7) <= lo and hi <= Fr(5, 7) and A > 3 / (2 - hi):
            out.append((lo, hi, 3 / (2 - hi) + SLACK))
        else:
            out.append((lo, hi, A))
    return out


def cap(pieces, A0):
    return [(lo, hi, A if A is None else min(A, A0)) for lo, hi, A in pieces]


def gm(pieces):
    def terms(s):
        return max(Fr(15) / (3 + 5 * s), Fr(3) / (2 * s), (18 - 20 * s) / (6 * (1 - s)))
    return [(lo, hi, min(A, terms(lo) + SLACK) if A is not None and Fr(7, 10) <= lo and hi <= Fr(8, 10) else A)
            for lo, hi, A in pieces]


def hb(pieces):
    X, A2 = Fr(15, 19), 2 + SLACK
    out = []
    for lo, hi, A in pieces:
        if A is not None and lo < X < hi:
            out += [(lo, X, A), (X, hi, min(A, A2))]
        elif A is not None and lo >= X:
            out.append((lo, hi, min(A, A2)))
        else:
            out.append((lo, hi, A))
    return out


def classical(pieces):
    """The steps on `[5/7, 131/168]` replaced by steps of `1/1680`: Ingham's `3/(2 − σ₊) + 1/2000` up to `3/4`, Huxley's
    `3/(3σ₋ − 1) + 1/2000` from `3/4`."""
    lo0, hi0, slack = Fr(5, 7), Fr(131, 168), Fr(1, 2000)
    steps, x = [], lo0
    while x < hi0:
        y = x + Fr(1, 1680)
        steps.append((x, y, 3 / (2 - y) + slack if y <= Fr(3, 4) else 3 / (3 * x - 1) + slack))
        x = y
    assert x == hi0
    out = []
    for lo, hi, A in pieces:
        if A is not None and lo0 <= lo and hi <= hi0:
            if lo == lo0:
                out += steps
            continue
        out.append((lo, hi, A))
    assert all(p[1] == q[0] for p, q in zip(out, out[1:]))
    return out


def curve(name):
    base, _, extra = name.partition('+')
    pieces = rl.parse('g7d')
    if base == 'today':
        pass
    elif base == 'ingham':
        pieces = ingham(pieces)
    elif base.startswith('cap:'):
        pieces = cap(ingham(pieces), Fr(base[4:]))
    elif base.startswith('rawcap:'):
        pieces = cap(pieces, Fr(base[7:]))
    elif base == 'gm':
        pieces = gm(ingham(pieces))
    elif base == 'classical':
        pieces = classical(pieces)
    else:
        raise SystemExit(f'unknown variant {name}')
    if extra == 'hb':
        pieces = hb(pieces)
    elif extra:
        raise SystemExit(f'unknown variant {name}')
    return pieces


def window(pieces, L):
    """The sampled scan, then the exact corners: each failing end moves inward by `10⁻⁵` until every corner passes
    (with no limit on the moves: the scan allows the Halász–Montgomery branch on every piece, the corners only on the
    top one, so for a curve far below `g7d` the scan's lower end can be a hundred steps too low). `None` if a corner
    at `m = 1` fails or the ends meet."""
    w = rl.window(pieces, L)
    if w is None:
        return None
    W1, W2 = round(w[0] * 100000), round(w[1] * 100000)
    while W1 < W2 and Fr(W2, 100000) * L > 1:
        fails, _, _ = rl.corners(pieces, L, W1, W2)
        if not fails:
            return W1, W2
        ends = {f[0] for f in fails}
        if 'one' in ends:
            return None
        W1 += 'lo' in ends
        W2 -= 'hi' in ends
    return None


def total2(pieces, L):
    w = window(pieces, L)
    if w is None:
        return None, None
    out = subprocess.run([sys.executable, os.path.join(HERE, 'mirror2.py'), str(w[0]), str(w[1]), str(N)],
                         capture_output=True, text=True, check=True).stdout
    return w, float(re.search(r'total2/K ([0-9.]+)', out).group(1))


def least(name):
    pieces = curve(name)
    print(f'{name}: largest exponent {float(max(A for _, _, A in pieces if A is not None)):.6f}', flush=True)
    L = STARTS.get(name, START)
    w, t = total2(pieces, L)
    print(f'  L = {L} ({float(L):.4f}): window {w}, total2/K {t}', flush=True)
    if t is None or t >= OK:
        return None
    good = L
    while True:
        L = good - STEP
        w, t = total2(pieces, L)
        print(f'  L = {L} ({float(L):.4f}): window {w}, total2/K {t}', flush=True)
        if t is None or t >= OK:
            break
        good = L
    mid = good - FINE
    w, t = total2(pieces, mid)
    print(f'  L = {mid} ({float(mid):.4f}): window {w}, total2/K {t}', flush=True)
    if t is not None and t < OK:
        good = mid
    return good


def main():
    names = sys.argv[1:] or DEFAULT
    found = [(n, least(n)) for n in names]
    print('\nlowest L passed (total2 < 0.999K at n = 340; steps of 1/1000, then one of 1/2000):')
    for n, L in found:
        print(f'  {n:16s} {f"fails at {STARTS.get(n, START)}" if L is None else f"{L} = {float(L):.4f}"}')


if __name__ == '__main__':
    main()
