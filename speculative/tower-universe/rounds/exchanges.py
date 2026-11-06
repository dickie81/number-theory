"""The numbers from the discussion between the rounds: who an embedded observer registers, how long a new prime waits,
and the counts behind "primes as matter" and "2 as photons". Exact arithmetic up to 10^7, asymptotics at our epoch."""
import math
import numpy as np

N7 = 10 ** 7
s = np.ones(N7 + 1, bool); s[:2] = False
for p in range(2, int(N7 ** 0.5) + 1):
    if s[p]: s[p * p::p] = False
P = np.nonzero(s)[0]
L = math.log(8.07e60)                      # log N at our epoch: one integer per Planck time, t0 = 13.787 Gyr
LL = math.log(L)

print("== Who an embedded observer registers ==")
w = np.log(P) / (P.astype(float) ** 2 - 1)  # species p clicks with strength log p / p^k at rate 1/p^k
tot = w.sum() + 1 / N7                      # the tail beyond 10^7 is about 1/10^7
print(f"total click weight per tick {tot:.5f} (−ζ′(2)/ζ(2) = 0.56996)")
for p in (2, 3, 5, 7, 11, 13):
    print(f"  species {p:2d}: {100 * w[P == p][0] / tot:5.1f}% of what the observer registers")
big = (w[P > 100].sum() + 1 / N7) / tot
print(f"  primes above 100 together: {100 * big:.2f}% of what is registered, but {100 * (1 - math.log(100) / L):.1f}%"
      f" of Σ log n at our epoch")

print("\n== How long a new prime waits ==")
pi = np.cumsum(s)
print(f"primes in (N/2, N], which divide no integer up to N: {100 * (pi[N7] - pi[N7 // 2]) / pi[N7]:.2f}% at N = 10^7;"
      f" {100 * (1 - 0.5 * (L - 1 - 1 / L) / (L - math.log(2) - 1 - 1 / (L - math.log(2)))):.2f}% at our epoch")
print("a prime born at tick p first divides an integer at 2p (twice the age), then once every p ticks")

print("\n== Primes as matter, composites as radiation ==")
print(f"composites per prime at our epoch: N/π(N) − 1 ≈ {L - 1 - 1 / L - 1:.1f}  (measured: ~1.6e9 photons per baryon)")
print(f"the share of primes changes by {100 / L:.2f}% per e-fold of time;"
      f" Ω_m changes by {100 * 3 * 0.685 * 0.95:.0f}% (3·Ω_Λ·H·t): a factor {3 * 0.685 * 0.95 * L:.0f}")
# Sathe–Selberg: π_k(x) ≈ (x/log x)·G((k−1)/log log x)·(log log x)^(k−1)/(k−1)!
z = 1 / LL
G = math.exp(np.sum(-np.log1p(-z / P) + z * np.log1p(-1 / P))) / math.gamma(z + 1)
share2 = 1 / L + G * LL / L
print(f"integers with at most two prime factors at our epoch: ≈ {100 * share2:.1f}% (primes {100 / L:.2f}%);"
      f" the cut is a free choice")

print("\n== 2 and its multiples as photons ==")
B2 = 1.0346538                              # Σ_{n≤x} Ω(n) = x·log log x + B2·x + o(x)
print(f"prime factors per integer at our epoch ≈ {LL + B2:.2f}, of which 2s: 1 on average,"
      f" so 2s are {100 / (LL + B2):.0f}% of all quanta")
print(f"share of Σ log n carried by 2s: log 2/(log N − 1) = {100 * math.log(2) / (L - 1):.2f}%;"
      f" share of what an embedded observer registers: {100 * w[0] / tot:.1f}%, the same at every epoch")
print("each 2-click joins tick N to tick N/2, so on the inside redshift 1 + z = N/n it comes from z = 1;"
      " a 4-click from z = 3, an 8-click from z = 7")
