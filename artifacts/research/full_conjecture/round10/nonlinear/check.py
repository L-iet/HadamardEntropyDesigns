"""Original stdlib exact certificates for quantitative encoding obstructions."""
from itertools import combinations
from fractions import Fraction as F
from pathlib import Path
from random import Random
import json

def rank(v):
 b={}
 for x in v:
  while x:
   i=x.bit_length()-1
   if i not in b:b[i]=x;break
   x^=b[i]
 return len(b)

def nullity_graph(m,edges):
 rows=[(1<<m)-1 for i in range(m)]
 for i in range(m):rows[i]^=1<<i
 for i,j in edges:rows[i]^=1<<j;rows[j]^=1<<i
 return m-rank(rows)
allgraphs=0
for m in [2,4,6]:
 pairs=list(combinations(range(m),2))
 for flags in range(1<<len(pairs)):
  edges=[edge for i,edge in enumerate(pairs) if (flags>>i)&1]
  assert nullity_graph(m,edges)<=len(edges)+1
  allgraphs+=1
matchings=[]
for a in range(2,7):
 q=2*a-3;m=2*q+4;edges=[(2*i,2*i+1) for i in range(q)]
 assert nullity_graph(m,edges)==2*a-2
 matchings.append(dict(a=a,m=m,edges=q,nullity=2*a-2))

fourier=[]
for r in [4,5,6]:
 for t,dim in [([0,1,2,3],2),([0,1,2,4],3)]:
  n=(1<<r)-4;s=sorted(set(range(1<<r))-set(t))
  spectra=[sum(1-2*((z&c).bit_count()%2) for z in s) for c in range(1<<r)]
  count=sum(x!=0 for x in spectra[1:]);expected=(1<<(r-2))-1 if dim==2 else 5*(1<<(r-3))-1
  assert count==expected
  fourier.append(dict(seedBits=r,complement=t,nonconstantFourierModes=count,bilinearRank=n-2*(r-dim)-2))

candidates=[]
for r in [5,6]:
 t=[0,1,2,4];s=sorted(set(range(1<<r))-set(t));n=len(s);m=n-4;a=r-3
 mons=[x for x in range(1<<r) if x.bit_count()<=r-2]
 gen=[sum(int(z&x==x)<<i for i,z in enumerate(s)) for x in mons]
 rng=Random(r);words=set()
 while len(words)<m:
  w=0
  for g in gen:
   if rng.getrandbits(1):w^=g
  if w.bit_count()==n//2:words.add(w)
 words=sorted(words);bad=0;energy=F(0);nonzero=0
 for x,y in combinations(words,2):
  q=n-2*(x^y).bit_count();assert q%4==0
  bad+=(q//4)%2;nonzero+=int(q!=0);energy+=2*F(q*q,n*n)
 assert bad>=2*a-3 and energy>=32*F(2*a-3,n*n)
 observed=[sum(((x>>i)&1)<<j for j,x in enumerate(words)) for i in range(n)]
 collision=sum(F(observed.count(x)**2,n*n) for x in set(observed))
 candidates.append(dict(seedBits=r,seedAtoms=n,bits=m,complementAffineCodimension=a,parityBadPairs=bad,nonzeroCorrelationPairs=nonzero,momentError=str(energy),certifiedLowerBound=str(32*F(2*a-3,n*n)),observableCollision=str(collision),balancedTruthWords=words))

def paley(p):
 chi=lambda x:0 if x%p==0 else 1 if pow(x%p,(p-1)//2,p)==1 else -1
 h=[[1]*(p+1)]+[[1]+[chi(j-i)-int(i==j) for j in range(p)] for i in range(p)]
 assert all(sum(x*y for x,y in zip(a,b))==(p+1)*int(i==j) for i,a in enumerate(h) for j,b in enumerate(h))
 return h

def affine_basis(t):
 ans=[t[0]]
 for x in t[1:]:
  if rank([z^ans[0] for z in ans[1:]]+[x^ans[0]])>len(ans)-1:ans.append(x)
 return ans

def solve(a,b):
 n=len(b);a=[sum(v<<j for j,v in enumerate(row))|(z<<n) for row,z in zip(a,b)]
 for j in range(n):
  k=next(k for k in range(j,n) if (a[k]>>j)&1);a[j],a[k]=a[k],a[j]
  for k in range(n):
   if k!=j and (a[k]>>j)&1:a[k]^=a[j]
 return [(a[j]>>n)&1 for j in range(n)]

def switch(r,t,h):
 t=set(t);s=sorted(set(range(1<<r))-t);truth=dict(zip(s,h));before=sorted(map(tuple,truth.values()));a=r-(len(affine_basis(sorted(t)))-1);moves=[]
 while len(affine_basis(sorted(t)))<r+1:
  ab=affine_basis(sorted(t));redundant=min(t-set(ab));new=next(x for x in range(1<<r) if x not in t and rank([z^ab[0] for z in ab[1:]]+[x^ab[0]])==len(ab))
  t.remove(redundant);t.add(new);truth[redundant]=truth.pop(new);moves.append([redundant,new])
 assert len(moves)==a and sorted(map(tuple,truth.values()))==before
 ab=affine_basis(sorted(t));maxdeg=0
 for j in range(1,len(h)):
  f=[0]*(1<<r)
  for z,row in truth.items():f[z]=int(row[j]<0)
  mons=[0]+[1<<i for i in range(r)]
  defects=[sum(f[z]*int(z&m==m) for z in range(1<<r))%2 for m in mons]
  vals=solve([[int(z&m==m) for z in ab] for m in mons],defects)
  for z,v in zip(ab,vals):f[z]=v
  assert all(f[z]==int(row[j]<0) for z,row in truth.items())
  for i in range(r):
   for z in range(1<<r):
    if z&(1<<i):f[z]^=f[z^(1<<i)]
  maxdeg=max(maxdeg,max((z.bit_count() for z,v in enumerate(f) if v),default=0))
 assert maxdeg<=r-2
 return dict(order=len(h),seedBits=r,minimumExchanges=a,moves=moves,finalDegree=maxdeg,observableLawAndCollisionUnchanged=True)
switches=[switch(5,range(12),paley(19)),switch(6,range(16),paley(47))]
result={'passed':True,'allSmallGraphsChecked':allgraphs,'sharpBinaryMatchingExamples':matchings,'fourOmissionSpectra':fourier,'balancedApproximateCandidates':candidates,'minimumSupportExchanges':switches}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='balancedApproximateCandidates'},indent=2))
