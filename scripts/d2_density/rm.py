import numpy as np
def sieve(n):
    s=np.ones(n+1,bool);s[:2]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=0
    return np.nonzero(s)[0].astype(float)
allp=sieve(10**8)
P=1e5; ps=allp[allp<P]; tp=allp[allp>=P]
def Y(ps):
    lg=np.log(ps); return -lg/(ps-1), lg/(ps+1), 1/(ps+1), ps/(2*(ps+1))
ta,tb,tw0,tw1=Y(tp)
tmean=np.sum(tw1*(ta+tb)); tvar=np.sum(tw1*(ta**2+tb**2))-np.sum((tw1*(ta+tb))**2)
tvar+=np.log(1e8)/1e8
a,b,w0,w1=Y(ps)
def phi(t):
    L=np.zeros_like(t,dtype=complex)
    for i in range(len(ps)):
        L+=np.log(w0[i]+w1[i]*(np.exp(1j*a[i]*t)+np.exp(1j*b[i]*t)))
    return np.exp(L+1j*tmean*t-tvar*t*t/2)
t=np.linspace(1e-7,120,24001); ph=phi(t)
print('|phi| at end',abs(ph[-1]), 'tail mean,var',tmean,tvar)
np.save('phi.npy',np.vstack([t,ph]))
def sf(x): return 0.5+np.trapz(np.imag(np.exp(-1j*t*x)*ph)/t,t)/np.pi
for x in [0.9547712524,0.4315231086,0.0]: print(x, sf(x))
print('density', 0.5*(sf(0.9547712524)+sf(0.4315231086)))
