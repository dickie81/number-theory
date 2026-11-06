# Results of round 6 (PREREG6.md): prime packets

Raw output: `packets.out` (from `packets.py`). Primes `p ≤ 2048`, with `λ_N` exact at `N = p − 1` and `N = p`.

**Verdict.** The packets are not identical quanta: a packet's size is set by its gap (Spearman 0.90–0.94). But each
packet has a nearly fixed core, the prime's own kick.

| Window | Packets | Prime's kick, quartiles (integers' worth) | CV | Prime's share of packet, median | Packet size |
|---|---|---|---|---|---|
| [256, 512) | 42 | 2.18 / 2.49 / 2.94 | 0.20 | 0.45 | 1.84 + 0.69·gap |
| [512, 1024) | 74 | 2.27 / 2.54 / 2.87 | 0.19 | 0.41 | 1.76 + 0.74·gap |
| [1024, 2048) | 136 | 2.23 / 2.56 / 2.93 | 0.21 | 0.39 | 1.72 + 0.77·gap |

Packet sizes by gap, in integers' worth (window [1024, 2048)):

| Gap | Packet size | Packets |
|---|---|---|
| 2 (twin primes) | 3.2 | 26 |
| 6 | 6.4 | 35 |
| 34 | 27.8 | 1 |

The other windows give the same pattern: gap 2 is about 3.0 and gap 6 about 6.

**What the kick depends on.**
- It doesn't depend on the gap before the prime (Spearman −0.03, 0.17, 0.03 across the windows).
- It is weakly lower when the gap after is long (Spearman −0.19 to −0.42). The kick depends only on integers up to p,
  so this is likely p's residue class, which also shapes the next gap.

**On average.** `1/λ₂₀₄₈ = 5652` over 309 primes, about 18 per prime. The asymptotic value is `1/0.0429 ≈ 23`.
