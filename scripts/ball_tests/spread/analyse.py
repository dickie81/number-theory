import json, numpy as np
R = {int(k): v for k, v in json.load(open('spread_6000.json')).items()}; Ns = sorted(R)
def ent(b):  # effective number of blocks exp(H) / total blocks
    p = np.array(b); p = p[p > 0]; return float(np.exp(-(p*np.log(p)).sum()))
summary = {}
for key, vk in [('a', 'v'), ('b', 'u')]:
    print('=== problem', key)
    for N in Ns:
        rows = []
        for i in range(5):
            b = R[N][key][i]['blocks']; rows.append('%d:max%.2f@j%d,eff%.1f/%d' % (i+1, max(b), int(np.argmax(b)), ent(b), len(b)))
        b0 = np.round(R[N][key][0]['blocks'], 3).tolist()
        print(N, 'lam1=%.3e' % R[N][key][0]['lam'], 'blocks1', b0); print('    ', ' '.join(rows))
    # overlaps consecutive and with fixed N=100 vector, and fixed-block weights
    print(' overlaps |<x_N,x_N_prev>|, |<x_N,x_100>|, weight in blocks j=0..3 (n<16):')
    prev = None; x100 = np.array(R[100][key][0][vk])
    for N in Ns:
        x = np.array(R[N][key][0][vk])
        o1 = abs(np.dot(x[:len(prev)], prev)) if prev is not None else float('nan')
        o2 = abs(np.dot(x[:100], x100))
        print('  ', N, '%.3f %.3f' % (o1, o2), 'w(n<16)=%.3f' % sum(R[N][key][0]['blocks'][:4]), 'w(top block)=%.3f' % R[N][key][0]['blocks'][-1])
        prev = x
