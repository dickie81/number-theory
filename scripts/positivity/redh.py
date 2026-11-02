import numpy as np, math
NMAX=10000
mu=np.ones(NMAX+1,dtype=int); mu[0]=0
isp=np.ones(NMAX+1,bool); isp[:2]=False
for p in range(2,NMAX+1):
    if isp[p]:
        isp[2*p::p]=False; mu[p::p]*=-1; mu[p*p::p*p]=0
phi=np.arange(NMAX+1,dtype=float)
for p in range(2,NMAX+1):
    if isp[p]: phi[p::p]*=(1-1/p)
M=np.cumsum(mu)
for N in [100,1000,3000,10000]:
    Sphi=phi[1:N+1].sum(); Smu=(mu[1:N+1]**2/phi[1:N+1]).sum()
    cs=math.sqrt(Sphi*Smu)
    # Hadamard: log det(R D R^T) <= sum log diag; diag_i = sum_{j: j=1 or i|j} phi(j)
    diag=np.array([phi[1]+ (phi[i:N+1:i].sum() - (phi[1] if i==1 else 0)) for i in range(1,N+1)])
    had=0.5*(np.log(diag).sum()-np.log(phi[1:N+1]).sum())   # bound on log|M|
    print(f"N={N} M={M[N]} |M|/sqrtN={abs(M[N])/math.sqrt(N):.3f} CS_bound={cs:.1f} (=N*{cs/N:.2f}) Hadamard_bound=exp({had:.0f}) trivial={N}")
