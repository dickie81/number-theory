"""Run high-precision Weil-form spectra (Zhu convention) and pickle results. mpmath, not interval-certified."""
import mpmath as mp, math, pickle, sys, time, random
from multiprocessing import Pool
import hpcore as h
def Krule(L): return max(48, int(5*L*2*math.pi*math.exp(2*L)/math.pi)+8)
EST={0.3:3,0.4:5,0.5:7,0.6:9,0.7:13,0.8:17,0.9:23,1.0:30,1.1:38,1.2:49}
def task(a):
    L,odd,ctl,dK=a; mp.mp.dps=max(40, EST.get(L,50)+30)
    K=Krule(L)+dK; kw={}
    if ctl=="jit": r=random.Random(5); kw["jit"]={n:mp.mpf(0.05*r.gauss(0,1)) for n in range(2,2000)}
    if ctl=="flip": kw["flip"]=(3,)
    t=time.time(); M,ks=h.form(L,K,odd=odd,**kw); E,V=h.eig(M)
    return (L,odd,ctl,dK),dict(K=K,ks=ks,E=[mp.nstr(e,25) for e in E[:8]],v0=[mp.nstr(x,mp.mp.dps) for x in V[0]] if ctl=="real" else None,
                              v1=[mp.nstr(x,mp.mp.dps) for x in V[1]] if ctl=="real" else None,dps=mp.mp.dps,sec=time.time()-t)
if __name__=="__main__":
    Ls=[0.3,0.4,0.5,0.6,0.7,0.8,0.9,1.0,1.1,1.2]
    tasks=[(L,o,"real",0) for L in Ls for o in (False,True)]+[(1.0,False,"real",24),(0.8,False,"real",16)]
    tasks+=[(L,o,c,0) for L in (0.5,0.6,0.8,1.0) for o in (False,True) for c in ("jit","flip")]
    tasks.sort(key=lambda a:-a[0])
    res={}
    with Pool(7) as P:
        for k,v in P.imap_unordered(task,tasks):
            res[k]=v; print(k,v["K"],v["E"][0][:12],v["E"][1][:10],"%.0fs"%v["sec"],flush=True)
            pickle.dump(res,open("/workspace/hp1_res.pkl","wb"))
