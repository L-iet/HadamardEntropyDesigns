"""Exact stdlib checks for Plotkin and spanning-omitted-slope stability bounds."""
from itertools import product,combinations
from fractions import Fraction as F
from pathlib import Path
import json

def mul(a,b,poly,h):
 c=0
 while b:
  if b&1:c^=a
  b>>=1;a<<=1
  if a&h:a^=poly
 return c

def wr(a,h):return sum(((a&alpha).bit_count()%2)<<alpha for alpha in range(h))
def row(xs,h):
 w=wr(xs[0],h)
 for j,x in enumerate(xs[1:],1):w|=(wr(x,h)^((xs[0]^x)&1))<<(j*h)
 return w

def f2rank(v):
 b={}
 for x in v:
  while x:
   i=x.bit_length()-1
   if i not in b:b[i]=x;break
   x^=b[i]
 return len(b)

def paley(p):
 chi=lambda x:0 if x%p==0 else 1 if pow(x%p,(p-1)//2,p)==1 else -1
 h=[[1]*(p+1)]+[[1]+[chi(j-i)-int(i==j) for j in range(p)] for i in range(p)]
 assert all(sum(x*y for x,y in zip(a,b))==(p+1)*int(i==j) for i,a in enumerate(h) for j,b in enumerate(h))
 return h

plotkin=[]
for h,k in [(4,2),(4,3),(4,4),(8,5),(8,6),(8,7),(8,8),(16,12)]:
 length=k-1;bound=h//(h-k+1)
 # Translate one mixed word to zero. All remaining words have weight h/2.
 candidates=[w for w in range(1<<length) if w.bit_count()==h//2]
 adj=[sum(1<<j for j,y in enumerate(candidates) if (x^y).bit_count()==h//2) for x in candidates]
 calls=0
 def exists(cand,left):
  global calls
  calls+=1
  if left==0:return True
  if cand.bit_count()<left:return False
  while cand:
   bit=cand&-cand;cand^=bit;i=bit.bit_length()-1
   if exists(cand&adj[i],left-1):return True
  return False
 assert not exists((1<<len(candidates))-1,bound)
 plotkin.append(dict(h=h,k=k,groupBound=bound,normalizedMixedCandidates=len(candidates),excludedGroupSize=bound+1,states=calls))

cases=[]
for h,rset,poly,known_k in [(8,[1,2,4],0b1011,False),(16,[1,2,4,8],0b10011,True)]:
 s=h.bit_length()-1;p=sorted(set(range(h))-set(rset));k=len(p);n=k*h
 assert p[0]==0 and h//2<k<h and f2rank(rset)==s
 for c in range(1,h):assert {mul(c,b,poly,h) for b in range(h)}==set(range(h))
 rows={};seeds={}
 for a,b in product(range(h),repeat=2):
  xs=tuple(a^mul(t,b,poly,h) for t in p);w=row(xs,h)
  rows[(a,b)]=w;seeds[(a,b)]=xs
 assert len(set(rows.values()))==h*h
 assert all(sum(1-2*((w>>i)&1) for w in rows.values())==0 for i in range(1,n))
 assert all(sum(1-2*(((w>>i)^(w>>j))&1) for w in rows.values())==0 for i,j in combinations(range(1,n),2))
 # All cross-B row products are nonzero; each B fiber is a full h-clique.
 for (a,b),(aa,bb) in combinations(rows,2):
  dot=n-2*(rows[(a,b)]^rows[(aa,bb)]).bit_count()
  assert (dot==0)==(b==bb)
 for b in range(1,h):
  negatives=sum(mul(t,b,poly,h)&1 for t in p if t)
  assert 0<negatives<h//2
 # Character forms establish the strict uniform vertex certificate.
 masks=[]
 for t in p:
  for alpha in range(1,h):masks.append(alpha|sum(((alpha&mul(t,1<<i,poly,h)).bit_count()%2)<<(s+i) for i in range(s)))
 for t in p[1:]:masks.append(sum((mul(t,1<<i,poly,h)&1)<<(s+i) for i in range(s)))
 assert len(set(masks))==n-1 and 0 not in masks
 assert {0,*masks,*[x^y for x,y in combinations(masks,2)]}==set(range(h*h))
 out=dict(h=h,k=k,order=n,omittedSlopes=rset,omittedSlopeRank=s,atoms=h*h,exactOrthogonalityGraph=f'{h} disjoint K_{h}',collision=str(F(1,h*h)),relativeCollisionIfHadamardOrder=str(F(k,h)),TVLowerBound=str(1-F(1,k)),exactMoments=True,strictLocalVertexCharacterCertificate=True)
 if known_k:
  K=paley(11);assert len(K)==k
  allrows=set();support=set(rows.values());mask=(1<<h)-1
  for b in range(h):
   completed=set()
   for a in range(h):
    blocks=[wr(a,h)]+[wr(a^mul(t,b,poly,h),h)^(mul(t,b,poly,h)&1) for t in p[1:]]
    for kr in K:completed.add(sum((x^(mask if kr[j]<0 else 0))<<(j*h) for j,x in enumerate(blocks)))
   assert len(completed)==n and all((x^y).bit_count()==n//2 for x,y in combinations(completed,2))
   assert completed&support=={rows[(a,b)] for a in range(h)}
   assert allrows.isdisjoint(completed);allrows|=completed
  assert len(allrows)==k*h*h
  tv=F(1,2)*(h*h*abs(F(1,h*h)-F(1,k*h*h))+(k-1)*h*h*F(1,k*h*h))
  assert tv==1-F(1,k)
  out.update(HadamardKConstruction='Paley11 gives H12',completedAtoms=len(allrows),exactDistance=str(tv),globalCollision=str(F(1,n)),absoluteCollisionDeficit=str(F(1,n)-F(1,h*h)))
 cases.append(out)
result={'passed':True,'plotkinGroupBounds':plotkin,'spanningSlopeCases':cases,'noIntegerBlockRepairClaimWhenKDoesNotDivideH':True}
Path(__file__).with_name('relative_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
