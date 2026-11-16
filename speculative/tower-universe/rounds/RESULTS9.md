# Results of round 9 (PREREG9.md): real quantum bits against the tower's coin

Raw output: `round9.out` (from `round9.py`) and `round9b.out` (from `round9b.py`, a check added after the data were
seen).

**Data.** The first 2·10⁸ bits of `anubits_1` (ANU, vacuum fluctuations), from Zenodo 4440318: Kavulich, Van Deren and
Schlosshauer, Phys. Lett. A 388, 127032 (2021), CC-BY. They were read by a range request and stream-decompressed. The
segmented Ω sieve matches the plain sieve on [1, 10⁶].

| Sequence | n | S1 patterns, max \|z\| | Bias, max \|z\| | Lags, max \|z\| | S2 drift D | S3 tones | Fingerprints |
|---|---|---|---|---|---|---|---|
| Tower, from its origin | 1 | 1.36 | 0.27 | 1.01 | −0.682 | +0.995 | 1/1 |
| Tower, late (10¹²) | 4 | 2.12 | 1.43 | 2.10 | +0.090 ± 0.152 | +0.004 ± 0.044 | 0/4 |
| Tower, late (10¹⁵) | 4 | 1.71 | 1.43 | 1.45 | −0.224 ± 0.613 | −0.047 ± 0.050 | 0/4 |
| ANU quantum bits | 20 | 3.62 | 1.93 | 2.78 | −0.255 ± 0.739 | +0.008 ± 0.027 | 0/20 |
| Pseudo-random (PCG64) | 20 | 3.35 | 1.51 | 2.37 | +0.087 ± 0.709 | −0.010 ± 0.037 | 0/20 |

The ± values are standard deviations across sequences. The largest S1 \|z\| values are maxima over 8n correlated
z-scores, and the pseudo-random control is just as high.

**All three predictions held.**
- The tower from its origin carries the fingerprints.
- The quantum and pseudo-random bits carry none.
- The tower's late windows carry none either, and are indistinguishable from the quantum bits on S1–S3.

One miss in a side estimate: I predicted a drift spread of about 0.5, and it came out about 0.7. The decision doesn't
depend on it.

**Check added after seeing the data.** The four 10¹² windows had a drift spread of only 0.15. Forty more windows at 10¹²
gave D = +0.004 ± 0.685, against −0.047 ± 0.591 for 40 fair-coin runs (Levene p = 0.28). It was a fluke.

**Conclusion.** Randomness tests at our epoch cannot tell the tower's hidden variables from true quantum randomness.
The quantum data are consistent with the hypothesis, but give it no support.
