import json, numpy as np, math
R = {int(k): v for k, v in json.load(open('eig_big.json')).items()}; Ns = np.array(sorted(R)); F = np.array([R[N]['f'][:100] for N in Ns])
x = 1/np.log(Ns)
def ext(col, deg):
    A = np.vander(x, deg+1); c, res, *_ = np.linalg.lstsq(A, col, rcond=None); return c[-1], np.sqrt(np.mean((A@c-col)**2))
E1 = np.array([ext(F[:, i], 1)[0] for i in range(100)]); E2 = np.array([ext(F[:, i], 2)[0] for i in range(100)])
raw = F[-1]
cands = {'p/(p+1)': lambda p, k: p/(p+1), 'phi/n: 1-1/p': lambda p, k: 1-1/p, '1-1/(p+1)^2 *?': lambda p, k: 1-1/(p+1)}
print('n  raw(N=8000)  extrap a+b/logN  extrap quad  p/(p+1)')
for n in [2,3,4,5,7,8,9,11,13,16,25,27,32,49,64,81]:
    print(n, '%.4f %.4f %.4f' % (raw[n-1], E1[n-1], E2[n-1]))
def mult_err(f):
    e = [abs(f[a*b-1]-f[a-1]*f[b-1]) for a in range(2, 100) for b in range(a+1, 100) if math.gcd(a, b) == 1 and a*b <= 100]
    return max(e), np.mean(e)
for nm, f in [('raw', raw), ('ext1', E1), ('ext2', E2)]: print(nm, 'multiplicativity err (ab<=100) max %.4f mean %.4f' % mult_err(f))
ps = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
for nm, f in [('raw', raw), ('ext1', E1)]:
    print(nm, 'p(1-f(p)):', [round(p*(1-f[p-1]), 3) for p in ps])
    print(nm, '(p+1)(1-f(p)):', [round((p+1)*(1-f[p-1]), 3) for p in ps])
for nm, f in [('raw', raw), ('ext1', E1)]:
    print(nm, 'g=mu*f at p^k (p=2,3,5; k=1..4):', [[round(f[p**k-1]-(f[p**(k-1)-1] if k>1 else 1), 4) for k in range(1, 5) if p**k <= 100] for p in (2, 3, 5)])
json.dump(dict(raw=raw.tolist(), ext1=E1.tolist(), ext2=E2.tolist()), open('f_extrap.json', 'w'))
