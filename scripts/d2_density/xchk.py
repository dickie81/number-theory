import json
from multiprocessing import Pool
from big import init,ell
R=json.load(open('emp_60000_64000.json'))
Ds=[(q if a==0 else -q) for q,a,l,r,k in R][:600]; L=[l for q,a,l,r,k in R][:600]
if __name__=='__main__':
    with Pool(8,initializer=init) as p: P=p.map(ell,Ds)
    d=[abs(a-b) for a,b in zip(L,P)]; print('maxdiff',max(d),'n',len(d))
