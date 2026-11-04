import sys,json
from multiprocessing import Pool
import cypari2
from big import init,ell
import big
if __name__=='__main__':
    X0,X1=int(float(sys.argv[1])),int(float(sys.argv[2]))
    pp=cypari2.Pari()
    Ds=[s*d for s in (1,-1) for d in range(X0,X1) if pp.isfundamental(s*d)]
    with Pool(8,initializer=init) as pool: ls=pool.map(ell,Ds,chunksize=16)
    json.dump(list(zip(Ds,ls)),open(f'exh_{X0}_{X1}.json','w')); print(X0,len(Ds),'done')
