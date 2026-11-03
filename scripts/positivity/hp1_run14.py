import pickle, hp1_run as r
from multiprocessing import Pool
r.EST[1.4]=78
if __name__=="__main__":
    with Pool(2) as P: out=P.map(r.task,[(1.4,False,"real",0),(1.4,True,"real",0)])
    pickle.dump(dict(out),open("/workspace/hp1_res14.pkl","wb")); print([ (k,v["E"][:3],v["sec"]) for k,v in out])
