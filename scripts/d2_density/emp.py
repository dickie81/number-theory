import sys,time,numpy as np
import os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from k2 import *
from multiprocessing import Pool
def work(q):
    ctx.prec=80; m=np.arange(1,q,dtype=np.int64); res=[]
    for n in m[(m*m)%q==1]:
        c=dirichlet_char(q,int(n))
        if not c.is_primitive(): continue
        K1,K2,l=char_k2(c)
        r=2*(1-abs(K2)**2/K1**2)
        res.append((q,c.parity(),float(l.real.mid()),float(r.mid()),float(K1.mid())))
    return res
if __name__=='__main__':
    Q0,Q1=int(sys.argv[1]),int(sys.argv[2]);t=time.time()
    with Pool(8) as P: R=sum(P.map(work,range(Q0,Q1+1),chunksize=16),[])
    import json; json.dump(R,open(f'emp_{Q0}_{Q1}.json','w'))
    for a in (0,1):
        S=[x for x in R if x[1]==a]; f=sum(x[3]<1 for x in S)
        lo=sum(x[3]<1 and x[2]<0 for x in S)
        print('parity',a,'n',len(S),'fail',f,f/len(S),'fail with l<0',lo,'thresh-pred',sum(x[2]>-2*(-0.4773856262 if a==0 else -0.2157615543) for x in S))
    print('time',time.time()-t)
