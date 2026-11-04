import numpy as np
def sieve(n):
    s=np.ones(n+1,bool);s[:2]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=0
    return np.nonzero(s)[0].astype(float)
allp=sieve(10**6); t=np.linspace(1e-7,150,30001)
t0,t1=0.5*np.log(27/4),1.5*np.log(4/3)
for y in [5,10,20,50,100,300,1000,10**4,10**5]:
    ps=allp[allp<=y]; L=np.zeros_like(t,dtype=complex)
    for p in ps:
        a=-np.log(p)/(p-1); b=np.log(p)/(p+1); w=p/(2*(p+1))
        L+=np.log(1/(p+1)+w*(np.exp(1j*a*t)+np.exp(1j*b*t)))
    ph=np.exp(L-1e-6*t*t)  # tiny gaussian smoothing for atoms
    sf=lambda x:0.5+np.trapezoid(np.imag(np.exp(-1j*t*x)*ph)/t,t)/np.pi
    m=np.sum([(p/(2*(p+1)))*(-np.log(p)/(p-1)+np.log(p)/(p+1)) for p in ps])
    print('y=%6d  P(>t0)=%.4f P(>t1)=%.4f'%(y,sf(t0),sf(t1)))
