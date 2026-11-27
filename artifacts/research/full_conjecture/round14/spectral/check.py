"""Exact stdlib certificates for entry-flip traps and tensor persistence."""
from itertools import combinations
from collections import Counter
from pathlib import Path
import json

def decode(words,n):return [[1-2*((word>>j)&1) for j in range(n)] for word in words]
def encode(h):return [sum(int(x<0)<<j for j,x in enumerate(r)) for r in h]
def energy_words(words,n):return 2*sum((n-2*(x^y).bit_count())**2 for x,y in combinations(words,2))
def gram(h):return [[sum(x*y for x,y in zip(a,b)) for b in h] for a in h]
def stats(h):
 n=len(h);g=gram(h);tr=list(map(list,zip(*h)));k=gram(tr)
 d=[[8*((2*n-1)-h[i][a]*sum(g[i][j]*h[j][a] for j in range(n))) for a in range(n)] for i in range(n)]
 return g,k,d

def pair_delta(h,g,k,d,c1,c2):
 n=len(h);i,a=divmod(c1,n);j,b=divmod(c2,n)
 if i==j:interaction=16*(h[i][a]*h[i][b]*k[a][b]-1)
 elif a==b:interaction=16*(h[i][a]*h[j][a]*g[i][j]-1)
 else:interaction=16*h[i][a]*h[i][b]*h[j][a]*h[j][b]
 return d[i][a]+d[j][b]+interaction

def flip_energy(words,n,cells):
 w=words[:]
 for c in cells:i,j=divmod(c,n);w[i]^=1<<j
 return energy_words(w,n)

words=[84,44,30,230,133,73,111,51];a=decode(words,8);base=energy_words(words,8);assert base==152
g,k,d=stats(a);assert Counter(x for row in d for x in row)=={8:21,40:28,72:15}
for c in range(64):assert flip_energy(words,8,[c])-base==d[c//8][c%8]
pairs=Counter()
for c1,c2 in combinations(range(64),2):
 delta=flip_energy(words,8,[c1,c2])-base
 assert delta==pair_delta(a,g,k,d,c1,c2);pairs[delta]+=1
assert min(pairs)==0 and pair_delta(a,g,k,d,0,5)==0
triple_min=min(flip_energy(words,8,cells)-base for cells in combinations(range(64),3));assert triple_min==-24
path=[energy_words(words,8)]+[flip_energy(words,8,[0,5,60][:i]) for i in range(1,4)];assert path==[152,160,152,128]
# Every even-order one-cell change is8mod16; tested over allnormalizedH4.
local4=Counter()
for flags in range(512):
 h=[[1]*4 for i in range(4)]
 for i in range(1,4):
  for j in range(1,4):h[i][j]=1-2*((flags>>((i-1)*3+j-1))&1)
 gg,kk,dd=stats(h);e=energy_words(encode(h),4)
 assert all(x%16==8 for row in dd for x in row)
 if min(x for row in dd for x in row)>0:local4[e]+=1
assert local4=={0:6}

def tensor(a,b):return [[x*y for x in ar for y in br] for ar in a for br in b]
def walsh(m):return [[1-2*((i&j).bit_count()%2) for j in range(m)] for i in range(m)]
lifts=[]
for m in [2,4]:
 h=tensor(a,walsh(m));n=len(h);w=encode(h);e=energy_words(w,n);gg,kk,dd=stats(h)
 assert e==152*m**3 and min(x for row in dd for x in row)==16*m-8
 minpair=10**100;pairwitness=None;directchecks=0
 for index,(c1,c2) in enumerate(combinations(range(n*n),2)):
  delta=pair_delta(h,gg,kk,dd,c1,c2)
  if delta<minpair:minpair=delta;pairwitness=[c1,c2]
  if m==2 or index%257==0:
   assert flip_energy(w,n,[c1,c2])-e==delta;directchecks+=1
 assert minpair==32*(m-1)>0
 lifts.append(dict(hadamardFactor=m,order=n,energy=e,minimumSingleIncrease=16*m-8,minimumPairIncrease=minpair,pairWitness=pairwitness,allPairFormulasEvaluated=n*n*(n*n-1)//2,directPairRecomputations=directchecks))
out={'passed':True,'baseRowsNegativeBitmasks':words,'baseEnergy':base,'singleIncreaseCounts':dict(sorted(Counter(x for row in d for x in row).items())),'allBasePairs':2016,'basePairIncreaseCounts':dict(sorted(pairs.items())),'allBaseTriples':41664,'minimumTripleChange':triple_min,'optimalBarrier':8,'barrierWitnessPath':path,'allNormalizedOrderFourCases':512,'orderFourLocalMinima':dict(local4),'tensorLifts':lifts}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
