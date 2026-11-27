from random import Random
import json
from pathlib import Path
rng=Random(42)
def gram(h):return [[sum(x*y for x,y in zip(a,b)) for b in h] for a in h]
def stats(h):
 n=len(h);g=gram(h);energy=sum(g[i][j]**2 for i in range(n) for j in range(n) if i!=j);d=[[8*((2*n-1)-h[i][j]*sum(g[i][k]*h[k][j] for k in range(n))) for j in range(n)] for i in range(n)];return energy,d
for n in [8,12,16]:
 for trial in range(100):
  h=[[rng.choice([-1,1]) for j in range(n)] for i in range(n)];steps=0
  while True:
   e,d=stats(h);v,i,j=min((d[i][j],i,j) for i in range(n) for j in range(n))
   if v>=0:break
   h[i][j]*=-1;steps+=1
  if e:
   print(n,'trial',trial,'energy',e,'mindelta',min(map(min,d)),'H',h)
   Path('research/full_conjecture/round14/spectral/trap'+str(n)+'.json').write_text(json.dumps({'n':n,'H':h,'energy':e,'minimumDelta':min(map(min,d))},indent=2))
   break
 else:print(n,'no trap')
