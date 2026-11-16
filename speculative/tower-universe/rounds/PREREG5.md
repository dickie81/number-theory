# Pre-registration, round 5: the same questions from the 3D slice

Written 2026-11-06, before computing.

## Q5. How many dimensions does it take to see the primes?

An observer limited to the first K zeros (2K real dimensions) scores each integer m by the Fejér-tapered
reconstruction:

  S_K(log m) = −Σ_{k≤K} (1 − γ_k/γ_{K+1})·cos(γ_k log m).

- **Measure.** AUC for telling the prime powers in [2, M] from the other integers in [2, M]:
  - 0.5 means blind; 1 means perfect.
  - K = 1, 2, 3, 5, 10, 20, 50, 100, 300, 1000, 2999.
  - M = 30, 100, 1000.
- **The drawn 3D slice** (first zero's plane plus one axis of the second) lies between K = 1 and K = 2.

## Q6. Room in 3D

In the slice, check whether p_1, p_2, p_3 span R³. If they do, every later integer arrives at angle 0: nothing new can
arrive after n = 3.

## Q7. The evolving outer product Σ_{n≤N} w_n w_n^†

Its nonzero eigenvalues are those of G_N. Report, at N = 64, 256, 1024 and 4096:
- the share of the trace in the top 3 axes;
- the effective dimension e^S, with S the entropy of the normalised eigenvalues;
- the participation ratio.

Report the same for the N → ∞ limit predicted from the zeros. That limit is D^{-1/2}·C₀·D^{-1/2} with
C₀(ρ,ρ') = 2/(2 + i(γ − γ')) and D = diag|ρ|²: the outer product's bulk is scale-free, so it freezes.
