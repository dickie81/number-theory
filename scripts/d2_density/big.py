import sys,json,random,time
from multiprocessing import Pool
import cypari2
P=None
def init():
    global P; P=cypari2.Pari(); P.default('realprecision',19); P.default('parisizemax',10**9)
def ell(D):
    L=P.lfuncreate(D); return float(P.lfun(L,1,1)/P.lfun(L,1))
def fund(rng,X0,X1,sign,n):
    pp=cypari2.Pari(); out=set()
    while len(out)<n:
        d=rng.randrange(X0,X1)*sign
        if pp.isfundamental(d): out.add(d)
    return sorted(out)
if __name__=='__main__':
    X0,X1,n=int(float(sys.argv[1])),int(float(sys.argv[2])),int(sys.argv[3])
    rng=random.Random(X0); Ds=fund(rng,X0,X1,1,n)+fund(rng,X0,X1,-1,n)
    t=time.time()
    with Pool(8,initializer=init) as pool: ls=pool.map(ell,Ds,chunksize=8)
    json.dump(list(zip(Ds,ls)),open(f'big_{X0}.json','w')); print(X0,'done',time.time()-t)
