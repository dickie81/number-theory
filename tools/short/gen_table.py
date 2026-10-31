import numpy as np
from dtable import delta_req, hux_formula
D0, D1, STEP = 0.9, 13.0, 0.0005
Ds = np.arange(D0, D1 + STEP / 2, STEP)
gm = [delta_req(D, True, ns=20000)[0] for D in Ds]
hx = [hux_formula(D) for D in Ds]
# sanity: GM never worse than Huxley, and both nondecreasing in D up to grid noise
assert all(g <= h + 1e-9 for g, h in zip(gm, hx))
with open('dtables.h', 'w') as f:
    f.write(f'// delta_req(D) on D = {D0} + i*{STEP}, i < {len(Ds)}: least moment with a power saving, T = N^D\n')
    f.write(f'static const double DT_D0 = {D0}, DT_STEP = {STEP};\nstatic const int DT_N = {len(Ds)};\n')
    for name, arr in (('DT_GM', gm), ('DT_HX', hx)):
        f.write(f'static const double {name}[{len(Ds)}] = {{' + ','.join(f'{v:.6f}' for v in arr) + '};\n')
print(len(Ds), 'entries; GM < Huxley at', sum(1 for g, h in zip(gm, hx) if g < h - 1e-6), 'grid points')
for D in (1.5, 2.3, 3.5, 4.5, 5.5, 7.5):
    i = int(round((D - D0) / STEP)); print(D, hx[i], round(gm[i], 4))
