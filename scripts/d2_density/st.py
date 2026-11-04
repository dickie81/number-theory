import json,glob,math,numpy as np
t={1:0.954771,-1:0.431523};pr={1:0.051123,-1:0.160911}
for f in sorted(glob.glob('exh_*.json')):
  R=json.load(open(f))
  for s in (1,-1):
    D=np.array([d for d,l in R if (d>0)==(s>0)]);l=np.array([l for d,l in R if (d>0)==(s>0)]);n=len(l);r=(l>t[s]).mean()
    sk=((l-l.mean())**3).mean()/l.std()**3
    c2=[(l[(D%8+8)%8==k]>t[s]).mean() if ((D%8+8)%8==k).any() else None for k in (1,5,0,4)]
    print(f,s,n,'rate %.4f z %+.2f mean %.4f sd %.4f sk %.3f'%(r,(r-pr[s])/math.sqrt(pr[s]*(1-pr[s])/n),l.mean(),l.std(),sk),'byD%8(1,5,0,4)',[None if c is None else round(c,4) for c in c2])
