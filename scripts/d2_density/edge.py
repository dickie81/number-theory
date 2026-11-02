import json,glob,numpy as np
from scipy.stats import norm
t={1:0.954771,-1:0.431523}
fs=['emp_3_10000.json','emp_20000_25000.json','emp_60000_64000.json','exh_100000_120000.json','exh_200000_210000.json','exh_400000_410000.json','big_1000000.json','big_10000000.json','big_100000000.json']
def ed(m,s,g,k,x):
  z=(x-m)/s; return norm.sf(z)+norm.pdf(z)*(g/6*(z*z-1)+k/24*(z**3-3*z)+g*g/72*(z**5-10*z**3+15*z))
print('model edgeworth(+,-)',ed(-0.43778,0.86346,-0.0768,0,t[1]),ed(-0.43778,0.86346,-0.0768,0,t[-1]))
for f in fs:
  R=json.load(open(f))
  if f.startswith('emp'): R=[((q if a==0 else -q),l) for q,a,l,r,k in R]
  for s in (1,-1):
    l=np.array([l for d,l in R if (d>0)==(s>0)]);m,sd=l.mean(),l.std();z=(l-m)/sd;g=(z**3).mean();k=(z**4).mean()-3
    print('%-24s %+d n=%5d rate %.4f | mean %.3f sd %.3f skew %+.3f exkurt %+.3f | normal %.4f edgeworth %.4f'%(f,s,len(l),(l>t[s]).mean(),m,sd,g,k,norm.sf((t[s]-m)/sd),ed(m,sd,g,k,t[s])))
