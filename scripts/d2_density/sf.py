import numpy as np
t,ph=np.load('phi.npy'); t=t.real
def sf(x): return 0.5+np.trapezoid(np.imag(np.exp(-1j*t*x)*ph)/t,t)/np.pi
for x in [0.9547712524,0.4315231086,0.0,-1]: print(x, sf(x))
print('density', 0.5*(sf(0.9547712524)+sf(0.4315231086)))
