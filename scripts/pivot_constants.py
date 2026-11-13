"""The numbers of the proof of the margin d_k ≥ 1.249·d_1: Section 4 of papers/orbit-lattice, replayed.

A cross-check of the Lean proof (PivotPhi, PivotMinorFT, PivotCert, PivotSharp, PivotTop in lib/core/) for readers
without Lean. CI does not run it. Exact rational arithmetic (fractions, sympy) except where it says floating point.

It prints, in the order of the paper:

1. the test function: the identity 1 − K(x) = (4/3)(1 − sinc²x) − (1/3)(1 − sinc²2x), φ̂(0) = (999/1000)·4π/45, the
   polynomial P(t) behind K ≤ 1, the expansion behind 1 − K(x) ≤ (7/36)x⁴, and that of H(iy) behind the pole bound;
2. the minorant's mass: κ(A) = 15/(2A) − 175/(8A²) + 375/(16A³), Σ_{k<30}κ(10·2^k), Σb_j and ∫μ/φ̂(0) > 7/8;
3. the interval certificate of PivotCert.mu_le, replayed cell by cell with the same bounds, and its least margins:
   400 cells of y ∈ [1, 2) for s ≥ 20, 320 cells of [12, 20), 460 cells of [1/2, 12), and (0, 1/2];
4. the pole's share 5/1332, d = 7/8 − 5/1332 and c_0 = (999/1000)(2/45)(13/10);
5. the top vertex: lcm(1, …, n) ≤ 3ⁿ for n ≤ 2000, the Mertens constants, the rooms and the prime terms at d = 17/20
   (floating point).

    python3 scripts/pivot_constants.py      # needs sympy; about a second
"""

import math
from fractions import Fraction as F

import sympy as sp

# ---------------------------------------------------------------------------------------------------------------
# 1. The test function φ(s) = (999/1000)(1 − K(s/5))/s², K(x) = sinc²x(1 + sin²x/3)

X = sp.symbols("X", positive=True)
lhs = sp.Rational(4, 3) * (1 - sp.sin(X) ** 2 / X**2) - sp.Rational(1, 3) * (1 - sp.sin(2 * X) ** 2 / (4 * X**2))
rhs = 1 - sp.sin(X) ** 2 / X**2 * (1 + sp.sin(X) ** 2 / 3)
assert sp.simplify(sp.expand_trig(lhs - rhs)) == 0
print("1 − K(x) = (4/3)(1 − sinc²x) − (1/3)(1 − sinc²2x): yes")

PHI0 = sp.Rational(999, 1000) * sp.pi * (sp.Rational(25, 9) * sp.Rational(2, 5) ** 3
                                          - sp.Rational(25, 144) * sp.Rational(4, 5) ** 3)
assert sp.simplify(PHI0 - sp.Rational(999, 1000) * 4 * sp.pi / 45) == 0
print("φ̂(0) = (999/1000)·4π/45 =", float(PHI0))

t = sp.symbols("t", real=True)
q = 1 - t / 6 + t**2 / 120
P = sp.expand((t * q**2 * (1 + t * q**2 / 3) - t) * 622080000 / t**3)
assert P == (t**7 - 80 * t**6 + 2880 * t**5 - 60800 * t**4 + 822400 * t**3 - 7252800 * t**2 + 39744000 * t
             - 110592000)
crude = -110592000 + sum(cf * sp.Rational(4, 3) ** e for cf, e in ((39744000, 1), (822400, 3), (2880, 5), (1, 7)))
assert crude < 0
print("K ≤ 1: tq²(1 + tq²/3) − t = t³P(t)/622080000, and P < 0 on [0, 4/3] (crude bound", float(crude), ")")

a = sp.symbols("a", real=True)
e = sp.expand(1 - (1 - a / 6) ** 2 * (1 + a * (1 - a / 6) ** 2 / 3))
assert e == sp.Rational(7, 36) * a**2 - a**3 / 18 + a**4 / 162 - a**5 / 3888
print("1 − (1 − a/6)²(1 + a(1 − a/6)²/3) =", e)
p = lambda x: 1 + x**2 / 6 + x**4 / 120  # noqa: E731
hp = sp.expand(1 - sp.Rational(4, 3) * p(a) ** 2 + sp.Rational(1, 3) * p(2 * a) ** 2)
assert hp == sp.Rational(8, 45) * a**4 + a**6 / 18 + sp.Rational(7, 1200) * a**8
bound = sp.Rational(8, 45) + (sp.Rational(1, 18) + sp.Rational(17, 600)) / 400 + sp.Rational(7, 1200) / 400**2
assert bound <= sp.Rational(1, 5)
print("H(iy), polynomial part:", hp, "; |H(iy)| ≤", float(bound), "·a⁴ ≤ a⁴/5 for a ≤ 1/20")

# ---------------------------------------------------------------------------------------------------------------
# 2. The mass of the minorant μ = φλ − r

A, w = sp.symbols("A w", positive=True)
phihat = lambda u: sp.Rational(999, 1000) * sp.pi * (  # noqa: E731  (|u| ≤ 2/5)
    sp.Rational(25, 9) * (sp.Rational(2, 5) - u) ** 3 - sp.Rational(25, 144) * (sp.Rational(4, 5) - u) ** 3)
kappa = sp.simplify(1 - 2 * sp.Rational(1, 4) * sp.integrate((2 - w) * phihat(w / A), (w, 0, 2)) / PHI0)
KAPPA = sp.Rational(15, 2) / A - sp.Rational(175, 8) / A**2 + sp.Rational(375, 16) / A**3
assert sp.simplify(kappa - KAPPA) == 0
SK = sum(KAPPA.subs(A, 10 * 2**k) for k in range(30))
assert SK >= sp.Rational(12351, 10000)
BUMPS = [(F(3, 2), F(193, 10**6)), (F(2), F(23, 500000)), (F(3), F(1021, 10**6)), (F(7, 2), F(593, 10**6)),
         (F(4), F(71, 125000)), (F(9, 2), F(617, 10**6)), (F(7), F(1433, 10**6)), (F(15, 2), F(39, 500000)),
         (F(17, 2), F(3, 250000))]
SB = sum(b for _, b in BUMPS)
MASS = sp.Rational(23, 100) + sp.Rational(693, 1000) * SK - 4 * sp.pi * sp.Rational(SB.numerator, SB.denominator) / PHI0
assert MASS > sp.Rational(7, 8)
print("κ(A) =", KAPPA, "; Σ_{k<30} κ(10·2^k) =", float(SK), "; Σb_j =", SB, "; ∫μ/φ̂(0) =", float(MASS))

# ---------------------------------------------------------------------------------------------------------------
# 3. The interval certificate of PivotCert, with the same bounds

L2LO, L2HI, LPIHI = F(6931471803, 10**10), F(6931471808, 10**10), F(11558, 10000)
assert float(L2LO) < math.log(2) < float(L2HI) and math.log(math.pi) < float(LPIHI)


def u(x):
    """u(x) = min(1, x²/3 − 2x⁴/45 + x⁶/315) ≥ 1 − sinc²x."""
    return min(F(1), x * x * (F(1, 3) - x * x * (F(2, 45) - x * x * F(1, 315))))


def T(y):
    """T(y) = S_8(y) + y²/147456 ≥ S_n(y) = Σ_{k<n} u(y/2^k) for every n."""
    return sum(u(y / 2**k) for k in range(8)) + y * y / 147456


def ebar(s2):
    """ē(t) at s2 = t, the Stirling error: Re ψ(¼ + it/2) ≥ log(t/2) − ē(t)."""
    b2 = s2 * s2 / 4
    r = F(81, 16) + b2
    return F(9) / (8 * r) + F(81) / (192 * r * r) + F(1, 4) / (F(1, 16) + b2) + F(5, 4) / (F(25, 16) + b2) + F(1, 3000)


def lg(y):
    """2v + 2v³/3 ≤ log y, v = (y − 1)/(y + 1), for y ≥ 1."""
    v = (y - 1) / (y + 1)
    return v * (2 + F(2, 3) * v * v)


def loglo(p):
    """A lower bound for log p, p ≥ 1/2, after halving."""
    if p < 1:
        return lg(2 * p) - L2HI
    k = 0
    while k < 20 and p / 2 ** (k + 1) >= 1:
        k += 1
    return k * L2LO + lg(p / 2**k)


def glo(sa):
    """g(s) = log(s/2π) − ē(2s) ≥ glo(s_a) for s ≥ s_a ≥ 1/2."""
    return loglo(sa) - L2HI - LPIHI - ebar(2 * sa)


def ell(z):
    """ℓ = 1 − x²/6 + x⁴/120 − x⁶/5040 ≤ sinc x, as a function of z = x²; it decreases in z."""
    return 1 - z * (F(1, 6) - z * (F(1, 120) - z * F(1, 5040)))


def rho(a):
    """ρ(a) = 7a/36 − a²/18 + a³/162 − a⁴/3888, 1 − K(x) ≤ x²ρ(x²) for x² ≤ 6; largest at a = 3."""
    return a * (F(7, 36) - a * (F(1, 18) - a * (F(1, 162) - a * F(1, 3888))))


def phiup(sa, sb):
    """φ ≤ phiup(s_a, s_b) on [s_a, s_b], when ℓ(s_b/5) > 0 and s_b² ≤ 150."""
    lb = ell(sb * sb / 25)
    b1 = F(999, 1000) * (1 - lb * lb * (1 + sa * sa / 25 * lb * lb / 3)) / (sa * sa)
    b2 = F(999, 1000) * rho(min(sb * sb / 25, F(3))) / 25
    return min(b1, b2)


def one(D):
    """sinc²z ≥ one(D) for |z| ≤ D/2."""
    if D > 6:
        return F(0)
    lb = ell(D * D / 4)
    return lb * lb if lb > 0 else F(0)


def rlo(sa, sb):
    """r ≥ rlo(s_a, s_b) on [s_a, s_b] ⊆ [0, ∞)."""
    return sum(b * (one(max(g - sa, sb - g)) + one(sb + g)) for g, b in BUMPS)


C23, C693 = F(23, 100), F(693, 1000)
# s ≥ 20: s = 10·2^j·y, j ≥ 1, y ∈ [1 + i/400, 1 + (i + 1)/400]
m1 = min(loglo(10 * F(400 + i, 400)) - L2HI - LPIHI - ebar(40 * F(400 + i, 400))
         - (C23 + C693 * (u(2 * F(401 + i, 400)) + T(F(401 + i, 400)) - 1)) for i in range(400))
# 12 ≤ s < 20: s ∈ [12 + i/40, 12 + (i + 1)/40]
m0 = min(glo(F(480 + i, 40)) - (C23 + C693 * T(F(481 + i, 400))) for i in range(320))
assert m1 > 0 and m0 > 0
print(f"s ≥ 20: 400 cells pass, least margin {float(m1):.5f}; [12, 20): 320 cells pass, least margin {float(m0):.5f}")
# 1/2 ≤ s < 12: s ∈ [1/2 + i/40, 1/2 + (i + 1)/40]
least, flat = None, 0
for i in range(460):
    sa, sb = F(20 + i, 40), F(21 + i, 40)
    delta = C23 + C693 * T(sb / 10) - glo(sa)
    if delta <= 0:
        flat += 1
        continue
    assert ell(sb * sb / 25) > 0 and sb * sb <= 150
    lo = rlo(sa, sb)
    assert phiup(sa, sb) * delta <= lo
    rel = (lo - phiup(sa, sb) * delta) / lo
    if least is None or rel < least[0]:
        least = (rel, sa, sb)
print(f"[1/2, 12): 460 cells pass, {flat} with λ ≤ g and {460 - flat} with φ_up·Δ ≤ r_lo; least relative margin "
      f"{float(least[0]):.4f} on [{float(least[1])}, {float(least[2])}]")
# 0 < s ≤ 1/2
C0 = C23 + C693 * T(F(1, 20)) + L2HI + LPIHI + ebar(F(0))
assert F(1, 3000) * (C0 / 4 + F(1, 2)) <= rlo(F(0), F(1, 2))
print(f"(0, 1/2]: (C_0/4 + 1/2)/3000 = {float(F(1, 3000) * (C0 / 4 + F(1, 2))):.6f} ≤ r_lo = "
      f"{float(rlo(F(0), F(1, 2))):.6f}")

# ---------------------------------------------------------------------------------------------------------------
# 4. The pole and the constants of the theorem

share = 1 / (6000 * PHI0 / (2 * sp.pi))
assert sp.simplify(share - sp.Rational(5, 1332)) == 0
d = sp.Rational(7, 8) - sp.Rational(5, 1332)
assert d >= sp.Rational(17, 20)
c0 = sp.Rational(999, 1000) * sp.Rational(2, 45) * sp.Rational(13, 10)
d1 = 2 + sp.EulerGamma - sp.log(4 * sp.pi)
print("pole share 5/1332; d =", d, "=", float(d), "; c_0 =", c0, "=", float(c0), "; d_1 =", sp.N(d1, 15),
      "; c_0/d_1 =", sp.N(c0 / d1, 6))

# ---------------------------------------------------------------------------------------------------------------
# 5. The top vertex (floating point except the lcm check)

lcm, top = 1, 0.0
for n in range(1, 2001):
    lcm = lcm * n // math.gcd(lcm, n)
    assert lcm <= 3**n
    top = max(top, math.log(lcm) / n)
print(f"lcm(1, …, n) ≤ 3ⁿ for n ≤ 2000; the largest ψ(n)/n there is {top:.5f} < log 3 = {math.log(3):.5f}")
print(f"Mertens constants: log 3 − 1 + (1 + log 3)/3 = {math.log(3) - 1 + (1 + math.log(3)) / 3:.4f}; at y = 1600, "
      f"log 4 − 1 + 0.37 + 0.01 = {math.log(4) - 1 + 0.38:.4f}")


def vm(n):
    """Λ(n)."""
    for p_ in range(2, n + 1):
        if n % p_ == 0:
            m = n
            while m % p_ == 0:
                m //= p_
            return math.log(p_) if m == 1 else 0.0
    return 0.0


M = [0.0]
for n in range(1, 2002):
    M.append(M[-1] + vm(n) / n)
D = 17 / 20
for p_ in (2, 3, 5, 7):
    room = D + math.log(p_) - M[p_ - 1]
    print(f"p = {p_}: room {room:.4f}, term Λ(p) − Λ(p)²/(p·room) = {math.log(p_) - math.log(p_) ** 2 / (p_ * room):.4f}")
f = lambda p_, r: math.log(p_) - math.log(p_) ** 2 / (p_ * r)  # noqa: E731
print(f"p = 11 with room ≥ d − 0.43: {f(11, D - 0.43):.4f}; p = 2003 with room ≥ d − 0.81: {f(2003, D - 0.81):.4f}")
print(f"the true rooms: min over [8, 2001] of room − d = {min(math.log(q_) - M[q_ - 1] for q_ in range(8, 2002)):.4f}")
