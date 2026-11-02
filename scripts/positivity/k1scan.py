import numpy as np, math, dcore as dc
from fractions import Fraction
from run import mkchi, gramM, pivots
rows=[]
for p in [5,7,11,13,17,19,23,29,31,37,41,43]:
    for kk in range(1,p-1):
        f=mkchi(dc.char_prime(p,kk)); K1=f(1).real
        piv=pivots(gramM(f,list(range(1,9))))
        rows.append((K1,piv.min()<1-1e-9,p,kk))
rows.sort()
fails=[r for r in rows if r[1]]; ok=[r for r in rows if not r[1]]
print(len(rows),"chars;",len(fails),"fail (k<=8)")
print("max K1 among pass:",max(r[0] for r in ok)," min K1 among fail:",min(r[0] for r in fails))
import collections
for lo,hi in [(0,1),(1,1.5),(1.5,2),(2,3),(3,100)]:
    s=[r for r in rows if lo<=r[0]<hi]; print(lo,hi,len(s),sum(r[1] for r in s))
