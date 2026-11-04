import json, numpy as np, matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
R = {int(k): v for k, v in json.load(open('spread_6000.json')).items()}; C = {int(k): v for k, v in json.load(open('curve.json')).items()}
fig, ax = plt.subplots(1, 3, figsize=(16, 4.5))
for N in [100, 300, 1000, 3000, 6000]:
    ax[0].plot(R[N]['a'][0]['blocks'], 'o-', label=f'N={N}'); ax[1].plot(R[N]['b'][0]['blocks'], 'o-', label=f'N={N}')
ax[0].set_title('(a) bottom eigvec of G: weight per dyadic block j'); ax[1].set_title('(b) bottom gen. eigvec (M-norm): weight per block j')
for N in [168, 169, 300]: ax[0].plot(C[N]['blocks_a'], 'k--' if N == 169 else 'k:', lw=1, label=f'curve F13 N={N}')
Ns = sorted(R); x100a = np.array(R[100]['a'][0]['v']); x100b = np.array(R[100]['b'][0]['u'])
ax[2].semilogx(Ns, [abs(np.dot(np.array(R[N]['a'][0]['v'])[:100], x100a)) for N in Ns], 'o-', label='(a) |<v_N,v_100>|')
ax[2].semilogx(Ns, [abs(np.dot(np.array(R[N]['b'][0]['u'])[:100], x100b)) for N in Ns], 's-', label='(b) |<u_N,u_100>|')
ax[2].semilogx(Ns, [sum(R[N]['b'][0]['blocks'][:4]) for N in Ns], '^-', label='(b) weight n<16')
ax[2].set_title('overlap with fixed vector'); [a.legend(fontsize=7) for a in ax]; ax[0].set_xlabel('j (n in [2^j,2^j+1))'); ax[1].set_xlabel('j')
plt.tight_layout(); plt.savefig('spread.png', dpi=120)
