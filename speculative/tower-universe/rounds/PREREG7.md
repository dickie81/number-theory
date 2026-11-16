# Pre-registration, round 7: an observer made of the tower

Written 2026-11-06, before computing.

**The two observers.**
- **Embedded.** The observer is the current vector w_N. It observes a past integer n through the full inner product
  G(N, n) = N·kos(N/n).
- **3D.** The same, but with the shadows p_N · p_n in the drawn slice.

**The click.** A click is a kink in G(N, n) as N advances. Measure it by the second difference
D(N) = G(N+1, n) − 2G(N, n) + G(N−1, n).

**Prediction, from the closed form.** kos′ jumps by Λ(m)/m² at x = m and nowhere else. So G(·, n) has a kink of
strength Λ(m)/m = log p/p^k exactly when N = n·p^k. At each tick N, there is one click per prime-power divisor p^k of
N, against the past integer N/p^k. A prime N clicks only once, against n = 1, with strength log N/N.

**Tests, for N ≤ 3000.**
- With n = 1 and n = 6, compare measured and predicted click strengths (largest relative error).
- AUC for picking out the click times from the score D(N) + 1/N (the smooth background is about −1/N), for both
  observers.
- Total click strength per tick (summed over all n < N), at primes against composites.
