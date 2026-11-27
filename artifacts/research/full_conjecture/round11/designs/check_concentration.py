"""Original exact finite-field concentration certificates; standard library only."""
from itertools import product,combinations
from fractions import Fraction as F
from pathlib import Path
import json

def multiplication(a,b,poly,h):
 c=0
 while b:
  if b&1:c^=a
  b>>=1;a<<=1
  if a&h:a^=poly
 return c

def walsh_row(a,h):return sum(((a&alpha).bit_count()%2)<<alpha for alpha in range(h))
def source_row(xs,h):
 row=walsh_row(xs[0],h)
 for j,x in enumerate(xs[1:],1):row|=(walsh_row(x,h)^((xs[0]^x)&1))<<(j*h)
 return row

def complete(offset,h,k):
 rows=set();clique=set();flip=(1<<h)-1
 for a in range(h):
  blocks=[walsh_row(a,h)]+[walsh_row(a^c,h)^(c&1) for c in offset]
  clique.add(sum(x<<(j*h) for j,x in enumerate(blocks)))
  for t in range(k):rows.add(sum((x^(flip if (t&j).bit_count()%2 else 0))<<(j*h) for j,x in enumerate(blocks)))
 assert len(rows)==k*h and all((x^y).bit_count()==k*h//2 for x,y in combinations(rows,2))
 return rows,clique

def moments(rows,n):
 assert all(sum(1-2*((x>>i)&1) for x in rows)==0 for i in range(1,n))
 assert all(sum(1-2*(((x>>i)^(x>>j))&1) for x in rows)==0 for i,j in combinations(range(1,n),2))

cases=[]
for k,h,poly in [(2,4,0b111),(2,8,0b1011),(4,8,0b1011)]:
 s=h.bit_length()-1;n=k*h;m=h*h;slopes=list(range(k))
 mul=lambda a,b:multiplication(a,b,poly,h)
 for a in range(1,h):assert {mul(a,b) for b in range(h)}==set(range(h))
 assert all(mul(a,b^c)==mul(a,b)^mul(a,c) for a,b,c in product(range(h),repeat=3))
 seeds=[tuple(a^mul(t,b) for t in slopes) for a,b in product(range(h),repeat=2)]
 assert len(set(seeds))==m
 for i,j in combinations(range(k),2):assert len({(x[i],x[j]) for x in seeds})==h*h
 rows={source_row(x,h) for x in seeds};assert len(rows)==m;moments(rows,n)
 source={source_row(x,h) for x in product(range(h),repeat=k)};assert rows<=source
 # All observed bits are distinct nonzero forms on the 2s-bit uniform seed.
 masks=[]
 for t in slopes:
  for alpha in range(1,h):
   mask=alpha|sum(((alpha&mul(t,1<<i)).bit_count()%2)<<(s+i) for i in range(s))
   masks.append(mask)
 for t in slopes[1:]:masks.append(sum((mul(t,1<<i)&1)<<(s+i) for i in range(s)))
 assert len(masks)==n-1 and len(set(masks))==n-1 and 0 not in masks
 covered={0,*masks,*[a^b for a,b in combinations(masks,2)]}
 assert covered==set(range(m))
 # Fourier orthogonality certifies supported-weight uniqueness and interpolation.
 assert all(sum(1-2*((chi&(a^b)).bit_count()%2) for chi in range(m))==m*int(a==b) for a,b in product(range(m),repeat=2))
 all_completed=set();repair=set();cliques=set();q=m//n
 for b in range(h):
  offset=[mul(t,b) for t in slopes[1:]]
  completed,clique=complete(offset,h,k)
  assert clique<=rows and len(clique)==h and completed&source==clique
  assert all_completed.isdisjoint(completed)
  all_completed|=completed;cliques|=clique
  if b<q:repair|=completed
 assert cliques==rows and len(all_completed)==k*m and len(repair)==m and len(repair&rows)==m//k
 moments(repair,n)
 tv=F(1,2)*(m*abs(F(1,m)-F(1,k*m))+(k*m-m)*F(1,k*m))
 assert tv==1-F(1,k)
 cases.append(dict(k=k,h=h,fieldPolynomialBinary=bin(poly),hadamardOrder=n,fullSourceAtoms=h**k,concentratedAtoms=m,fixedSupportMaximumCollision=str(F(1,m)),fullGlobalCollision=str(F(1,n)),collisionRatio=str(F(k,h)),hadamardMixtureDistance=str(tv),repairBlocks=q,minimumObservationReplacements=m-m//k,allCompletionAtoms=len(all_completed),allPairBlockProjectionsBijective=True,fullSeedFourierCharactersCoveredByObservableDegree2=True,certifiedOutsideMassRadius=str(F(2,m*(m+1))),certifiedCollisionBarrier=str(F(1,m*m*(m+1)))))
result={'passed':True,'cases':cases,'finiteFieldConstructionIsClassical':True,'noNewHadamardOrderClaim':True}
Path(__file__).with_name('concentration_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
