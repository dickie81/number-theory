# Results of round 11 (PREREG11.md): can a hyperplane's geometry explain DESI?

Raw output: `dgp11.out` (from `dgp11.py`, pre-registered) and `dgp11b.out` (from `dgp11b.py`, a check added after the
result).

## The tower's hyperplane: no

A geometry that is the same at every epoch forces a power law (`H ∝ a^{−k}`). Against DESI DR2 BAO:

| Model | χ² (11 dof) | Δχ² against ΛCDM |
|---|---|---|
| Flat ΛCDM, Ω_m = 0.2975 | 10.27 | 0 |
| Best power law, p = 0.912 | 96.97 | 86.7 (9.3σ) |

The window's own law (p = ½) gives χ² = 5436 (round 2).

## Q14: DGP braneworld self-acceleration

**BAO alone (pre-registered).** χ² = 15.09, p = 0.18, at Ω_m = 0.260 and Ω_rc = 0.137. That is Δχ² = 4.82 (2.2σ) against
ΛCDM, so it passes the Δχ² < 9 bar. The crossover distance is `r_c = 1.35` Hubble lengths, put in by hand.

**BAO plus the CMB shift parameter (added after the result).** R = 1.7502 ± 0.0046 (Planck 2018 compressed, Chen,
Huang & Wang 2019), with radiation included:

| Model | χ² | Ω_m | BAO part | R |
|---|---|---|---|---|
| Flat ΛCDM | 12.81 | 0.307 | 11.67 | 1.7453 |
| DGP self-accelerating | 191.78 | 0.382 | 140.78 | 1.7173 |

DGP is worse by Δχ² = 179 (13.4σ). The first grid stopped at Ω_m = 0.36, at its edge. Widening it moved the DGP best
fit to 0.382, an interior point, and the verdict didn't change.

**Verdict.** A brane geometry can fit DESI's BAO shape alone, but the classic version fails by 13σ once the CMB is
added. It also needs a second scale (`r_c`), which the tower cannot supply: its only scales are the tick and the epoch
itself, and tying `r_c` to the epoch makes the model self-similar again.
