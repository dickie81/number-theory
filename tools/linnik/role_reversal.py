#!/usr/bin/env python3
"""role_reversal.py [L]: what role reversals recover of the dropped terms whose largest prime is above the window.

At the window that `density_payoff.py` computes for the curve `g7d` at `L` (with none, `89/40`, where it is the
library's `[41479, 47555]/10⁵`), write `u₁ = U₁/D`, `u₂ = U₂/D` and `v = u₂ − u₁` as in `dropped_mass.py`, and let `p`
be a prime of exponent `a` in the gap `(u₂, 1/2)` above the window. The certificate decomposes `S(𝒜_p, p)` into
`S(𝒜_p, z₀)`, a Type I term, less the terms `S(𝒜_{p p₂}, p₂)`, which have sign `+` in `S(𝒜, z_top)`. Those with
`a + a₂ ≥ 1 − u₁` (`a₂` the exponent of `p₂`, and then `1 − u₁ − a ≤ a₂ ≤ (1 − a)/2`) it can neither evaluate nor
decompose, since the split at `X′ = x^{1 − u₂}` would leave cofactors below the window, and it drops them; their
integers with no product of primes in `𝒰` are lost. This is the row `gap, yes` of `dropped_mass.py`. The script measures
two role reversals against that loss.

1. Reverse `S(𝒜_p, p)`. Its integers are the `n = p q` with `q` a prime of exponent `b = 1 − a`. Counted by `q`, it is
   `S(𝒜_q, z₀)`, a Type I term since `b < 1 − u₂`, less the terms `S(𝒜_{q p₂}, p₂)` with `z₀ ≤ p₂ ≤ p^{1/2}`, of sign
   `+`. Those with `b + a₂ < 1 − u₁` have `q p₂` in the reflected window. The others, with
   `max(v, a − u₁) ≤ a₂ ≤ a/2`, can be neither evaluated nor decomposed (`q p₂` is above `X′`), and dropping them loses
   their integers with no product of primes in `𝒰`.
2. Reverse a dropped term of the row. Its integers are the `n = p ℓ` with `ℓ = p₂ m`, `m` without prime factors below
   `p₂`. Counted by `ℓ`, with `p` sifted, it is `S(𝒜_ℓ, z₀)`, a Type I term since `ℓ < x^{1 − u₂}`, less the terms
   `S(𝒜_{ℓ p₄}, p₄)` with `z₀ ≤ p₄ ≤ p^{1/2}`, of sign `−`, which must therefore all be evaluated; none can be
   decomposed, since `ℓ p₄` is above `X′`. Those with `a₄ < a − u₁` are evaluated by their cofactor, whose exponent
   `a − a₄` is in the window. For the others, with `max(v, a − u₁) ≤ a₄ ≤ a/2`, some product of `p₂`, the primes of `m`
   and `p₄` must have its exponent in `𝒰`. The reversal is valid for `(p, ℓ)` if this holds for every such `a₄`. The
   script tests that exactly, but for finitely many `a₄`, since the `a₄` that pass form a union of intervals. Where it
   is valid, the term's integers are all evaluated. Validity for each `(p, ℓ)` separately is more than a certificate
   could use, which needs it on whole cells, so the mass it rescues is an upper bound.

The masses, in units of `x/log x` as in `dropped_mass.py`, are integrals over `a` and `a₂` by the midpoint rule with
200 points each. The densities are `ω(g/a₂)/(a a₂²)` with `g = 1 − a − a₂` for the dropped terms and
`ω((a − a₂)/a₂)/(b a₂²)` for the terms of reversal 1. At each point the share of integers with no product of primes in
`𝒰` is estimated from 40 cofactors, factored as in `dropped_mass.py`. The script prints, for every 25th `a`, the loss of
the row, the loss of reversal 1 and the part of the row's loss that reversal 2 rescues, each per unit of `a`; then the
totals, and the number of the 200 values of `a` at which reversal 1 loses less than the row. A `±` is an estimate of
one standard error of the cofactors' sampling. The row's loss is `dropped_mass.py`'s row `gap, yes` computed another
way. These are computations, not theorems, and nothing in the library depends on them.

Needs Python 3 only (and `dropped_mass.py` and `density_payoff.py`); about a minute.
"""
import os
import random
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import density_payoff as dp  # noqa: E402
import dropped_mass as dm  # noqa: E402
import route_limits as rl  # noqa: E402

NA, NB, M = 200, 200, 40


def subset_sums(xs):
    out = [0.0]
    for e in xs:
        out += [s + e for s in out]
    return out


def reversible(a, a2, m, lo, hi, v):
    """whether for every a4 in [max(v, a - lo), a/2], but for finitely many, a sum of some of a2, the exponents m
    and a4 lies in (lo, hi) or (1 - hi, 1 - lo)"""
    if dm.visible([a2] + m, lo, hi):
        return True
    lo4, hi4 = max(v, a - lo), a / 2
    ivs = sorted((l - s, h - s) for s in subset_sums([a2] + m) for l, h in ((lo, hi), (1 - hi, 1 - lo)))
    cur = lo4
    for l, h in ivs:
        if l > cur:
            break
        cur = max(cur, h)
    return cur >= hi4


def main():
    L = Fr(sys.argv[1]) if len(sys.argv) > 1 else Fr(89, 40)
    w = dp.window(rl.parse('g7d'), L)
    if w is None:
        raise SystemExit(f'L = {L}: no window')
    U1, U2 = (w[0] * dm.DEN + 99999) // 100000, w[1] * dm.DEN // 100000
    lo, hi = U1 / dm.DEN, U2 / dm.DEN
    v = hi - lo
    rng = random.Random(12345)
    da = (0.5 - hi) / NA
    tot = [0.0] * 3                      # the row's loss, reversal 1's loss, the part of the first reversal 2 rescues
    var = [0.0] * 3
    better = 0
    print(f'L = {L} ({float(L):.4f}): window [{w[0]}, {w[1]}]/10^5, gap ({hi:.5f}, 0.5)')
    for i in range(NA):
        a = hi + da * (i + 0.5)
        b = 1 - a
        per = [0.0] * 3
        # the row: the terms (p, p2) with a + a2 >= 1 - lo
        l2, h2 = max(v, 1 - lo - a), (1 - a) / 2
        d2 = (h2 - l2) / NB
        for k in range(NB):
            a2 = l2 + d2 * (k + 0.5)
            g = 1 - a - a2
            f = dm.omega(g / a2) / (a * a2 * a2)
            if f == 0:
                continue
            lost = ok = 0
            for _ in range(M):
                m = dm.cofactor(rng, g, a2)
                if dm.visible([a, a2] + m, lo, hi):
                    continue
                lost += 1
                ok += reversible(a, a2, m, lo, hi, v)
            for q, c in ((0, lost), (2, ok)):
                per[q] += f * d2 * c / M
                var[q] += (f * d2 * da) ** 2 * (c / M) * (1 - c / M) / M
        # reversal 1: the terms (q, p2) with b + a2 >= 1 - lo
        l2, h2 = max(v, a - lo), a / 2
        d2 = (h2 - l2) / NB
        for k in range(NB):
            a2 = l2 + d2 * (k + 0.5)
            g = a - a2
            f = dm.omega(g / a2) / (b * a2 * a2)
            if f == 0:
                continue
            lost = sum(not dm.visible([b, a2] + dm.cofactor(rng, g, a2), lo, hi) for _ in range(M))
            per[1] += f * d2 * lost / M
            var[1] += (f * d2 * da) ** 2 * (lost / M) * (1 - lost / M) / M
        for q in range(3):
            tot[q] += per[q] * da
        better += per[1] < per[0]
        if i % 25 == 0:
            print(f'  a = {a:.4f}: the row loses {per[0]:.3f}, reversal 1 {per[1]:.3f}; reversal 2 rescues '
                  f'{per[2]:.3f} (per unit of a)')
    sd = [x ** 0.5 for x in var]
    print(f'the row loses {tot[0]:.5f} ± {sd[0]:.5f}; reversal 1 loses {tot[1]:.5f} ± {sd[1]:.5f}, less than the row '
          f'at {better} of the {NA} values of a; reversal 2 rescues at most {tot[2]:.5f} ± {sd[2]:.5f}')


if __name__ == '__main__':
    main()
