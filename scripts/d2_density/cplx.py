import numpy as np
rng=np.random.default_rng(2)
def sieve(n):
    s=np.ones(n+1,bool);s[:2]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=0
    return np.nonzero(s)[0].astype(float)
ps=sieve(2*10**4);M=400000;Z=np.zeros(M,complex)
for p in ps:
    e=np.exp(2j*np.pi*rng.random(M)); Z+=-np.log(p)*e/(p-e)
u=Z.real
for t in (0.5*np.log(27/4),1.5*np.log(4/3)): print(t,(u>t).mean())
print('limit density', 0.5*((u>0.5*np.log(27/4)).mean()+(u>1.5*np.log(4/3)).mean()))
