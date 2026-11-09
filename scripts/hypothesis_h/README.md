# Hypothesis (H) hunt scripts

Companion to `docs/hypothesis-h-hunt.md` (short character sums at `x=q^{7/18}`).

| File | Role |
|---|---|
| `seed.txt` | Shuffled-opening seed `20261109` |
| `moments_bookkeeping.py` | Exponents for moments k=1..8, Burgess vs V, (H) price |
| `short_sum_counts.py` | FFT counts `#χ: |S_I|≥V`, E₄, log-log α fit |

Reuses the discrete-log FFT pattern of `scripts/cgl_s3/blocks.py`.
| `j6_anatomy_bookkeeping.py` | LoD 6/7 vs FI/HB/FKM; Kl3/Deligne vs geometric |
| `j6_k_decompose.py` | Per-k N(kq) decomposition of J6; localize excess |
| `trilinear_S.py` | Exact S(r)=sum e(r n1 n2 n3/q); max/RMS vs geo/need |
