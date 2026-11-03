"""Prime-phase alignment up to T*=2 pi e^{2L} (Zhu's barrier). Float64 is adequate here (O(1) sums, no cancellation).
Also: Weil-form lambda_min (Zhu convention, mpmath dps 50, K=48 sine modes) for fake prime sets at L=0.8."""
import numpy as np, math, random, pickle, mpmath as mp
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
from multiprocessing import Pool
import hpcore as h
out=[]; P=lambda *a: (out.append(" ".join(str(x) for x in a)), print(*a, flush=True))
def realset(L):
    return [(float(y),float(w)) for y,w in h.lam_list(L)]
def fakeset(L,seed,mode):
    r=random.Random(seed); s=realset(L)
    if mode=="jit": return [(y+0.05*r.gauss(0,1),w) for y,w in s]
    if mode=="flip3": return [(y,-w if abs(math.exp(y)-3)<1e-6 else w) for y,w in s]
    # random 'primes': each integer n>=2 prime w.p. 1/log n (Cramer), plus their powers
    N=int(math.exp(2*L)); ps=[n for n in range(2,N+1) if r.random()<1/math.log(n)] if mode=="cramer" else None
    o=[]
    for p in ps:
        q=p
        while math.log(q)<2*L: o.append((math.log(q),2*math.log(p)/math.sqrt(q))); q*=p
    return o
def align(s,L,tmin=1.0):
    T=2*math.pi*math.exp(2*L); t=np.arange(tmin,T,0.002)
    y=np.array([a for a,_ in s]); w=np.array([b for _,b in s]); S=(w[None,:]*np.cos(np.outer(t,y))).sum(1) if len(t)*len(y)<4e7 else sum(wi*np.cos(t*yi) for yi,wi in s)
    A=np.abs(w).sum(); return S.max()/A, S.min()/A, np.mean(S/A), np.std(S/A), t[np.argmax(S)], A, (t,S/A)
def kron(L,s,tmax):  # best simultaneous approx: min over t in [1,tmax] of max_p ||t log p/2pi|| over primes only
    ys=[y for y,w in s if w!=0]; t=np.arange(1,tmax,0.001); best=1
    D=np.zeros_like(t)
    for y in ys: D=np.maximum(D,np.abs(((t*y/(2*math.pi))+0.5)%1-0.5))
    return D.min(), t[np.argmin(D)]
P("1. alignment of the prime comb on [1, T*]: max S/A (1 = perfect alignment), min, mean, sd; A = total weight")
curves={}
for L in (0.8,1.0,1.2,1.5,2.0):
    for lab,s in (("real",realset(L)),("jit",fakeset(L,1,"jit")),("flip3",fakeset(L,1,"flip3"))):
        mx,mn,mu,sd,tm,A,c=align(s,L); curves[(L,lab)]=c
        P(" L=%.1f %-6s #terms %3d A=%.3f  max %.3f at t=%.1f  min %+.3f  mean %+.3f sd %.3f"%(L,lab,len(s),A,mx,tm,mn,mu,sd))
    cr=[align(fakeset(L,sd_,"cramer"),L)[0] for sd_ in range(20)]
    P(" L=%.1f cramer(20 sets): max S/A mean %.3f sd %.3f range %.3f-%.3f"%(L,np.mean(cr),np.std(cr),min(cr),max(cr)))
P("\n2. Kronecker: min over t in [1,T*] of max over primes p of ||t log p / 2pi|| (0 = all phases aligned)")
for L in (0.8,1.0,1.2,1.5):
    T=2*math.pi*math.exp(2*L); s=realset(L)
    d,t=kron(L,[(y,w) for y,w in s if abs(round(math.exp(y))-math.exp(y))<1e-6 and all(round(math.exp(y))%q or round(math.exp(y))==q for q in range(2,int(math.exp(y)**.5)+1))],T)
    P(" L=%.1f primes %s  best %.4f at t=%.2f   (Dirichlet heuristic ~ T^{-1/k})"%(L,[round(math.exp(y)) for y,w in s if all(round(math.exp(y))%q or round(math.exp(y))==q for q in range(2,int(math.exp(y)**.5)+1))],d,t))
open("hp3_results_part.txt","w").write("\n".join(out)+"\n")
pickle.dump(curves,open("/workspace/hp3_curves.pkl","wb"))
