"""Post-hoc check (not pre-registered): is the late tower coin's drift spread smaller than chance?"""
import math, sys
import numpy as np
from scipy import stats as st
HERE = sys.path[0]
src = open(f"{HERE}/round9.py").read()
exec(src.split("t0 = time.time()")[0].replace("import mpmath as mp", "import mpmath as mp, time"))
L = 10 ** 7
xd = np.unique(np.round(np.exp(np.linspace(math.log(1e3), math.log(L), 4000))).astype(int))
D = lambda x: float(np.mean(np.cumsum(x, dtype=np.int64)[xd - 1] / np.sqrt(xd)))
pm = lambda Om: np.where(Om % 2 == 0, 1, -1).astype(np.int8)
base = sieve(int(math.isqrt(10 ** 12 + 50 * 10 ** 9 + L)) + 1)
late = [D(pm(omega_window(10 ** 12 + j * 10 ** 9, L, base))) for j in range(4, 44)]
rng = np.random.default_rng(7)
fair = [D(rng.choice(np.array([-1, 1], np.int8), L)) for _ in range(40)]
for nm, v in (("tower, late (10^12), 40 new windows", late), ("fair coin (PCG64), 40 runs", fair)):
    v = np.array(v); print(f"{nm:38s}: drift D = {v.mean():+.3f} ± {v.std(ddof=1):.3f} (sd)")
print(f"Levene test for equal spread: p = {st.levene(late, fair).pvalue:.2f}")
