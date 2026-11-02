import json,math,glob
t={1:0.5*math.log(27/4),-1:1.5*math.log(4/3)}; pr={1:0.051123,-1:0.160911}
for f in sorted(glob.glob('big_*.json'),key=lambda s:int(s[4:-5])):
    R=json.load(open(f))
    for s in (1,-1):
        S=[l for D,l in R if (D>0)==(s>0)]; n=len(S); k=sum(l>t[s] for l in S); r=k/n
        m=sum(S)/n; sd=(sum((l-m)**2 for l in S)/n)**.5
        print(f,'+' if s>0 else '-',n,'rate %.4f z=%+.2f mean %.3f sd %.3f'%(r,(r-pr[s])/math.sqrt(pr[s]*(1-pr[s])/n),m,sd))
