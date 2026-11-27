"""Exact original stdlib checks of sharp Hadamard-mixture distance and repair."""
from itertools import product,combinations
from fractions import Fraction as F
from pathlib import Path
from random import Random
import json

def walsh_row(a,h):return sum(((a&b).bit_count()%2)<<b for b in range(h))
def source_row(xs,h):
 row=walsh_row(xs[0],h)
 for j,x in enumerate(xs[1:],1):row|=(walsh_row(x,h)^((xs[0]^x)&1))<<(j*h)
 return row

def completion(offset,h,k):
 mask=(1<<h)-1;rows=[];clique=[]
 for a in range(h):
  blocks=[walsh_row(a,h)]+[walsh_row(a^c,h)^(c&1) for c in offset]
  clique.append(sum(x<<(j*h) for j,x in enumerate(blocks)))
  for t in range(k):rows.append(sum((x^(mask if (t&j).bit_count()%2 else 0))<<(j*h) for j,x in enumerate(blocks)))
 n=k*h
 assert len(set(rows))==n and all((x&1)==0 for x in rows)
 assert all((x^y).bit_count()==n//2 for x,y in combinations(rows,2))
 return set(rows),set(clique)

def moment_check(rows,n):
 assert all(sum(1-2*((x>>i)&1) for x in rows)==0 for i in range(1,n))
 assert all(sum(1-2*(((x>>i)^(x>>j))&1) for x in rows)==0 for i,j in combinations(range(1,n),2))

cases=[]
for k,h in [(2,4),(2,8),(4,8)]:
 n=k*h;d=h**k;assert h>2*(k-1)
 seeds=list(product(range(h),repeat=k));source={source_row(xs,h) for xs in seeds}
 assert len(source)==d;moment_check(source,n)
 # Exact row kernel identity and the shared-seed exclusion.
 pairs=list(combinations(range(d),2)) if d<=64 else [tuple(Random(i).sample(range(d),2)) for i in range(3000)]
 for i,j in pairs:
  x,y=seeds[i],seeds[j];dot=n-2*(source_row(x,h)^source_row(y,h)).bit_count()
  formula=h*sum(a==b for a,b in zip(x,y))+1-k+sum(1-2*((x[0]^x[z]^y[0]^y[z])&1) for z in range(1,k))
  assert dot==formula
  if any(a==b for a,b in zip(x,y)):assert dot>0
 allrows=set();selected=set();q=d//n;cliquecount=0
 for c in product(range(h),repeat=k-1):
  rows,clique=completion(c,h,k)
  assert len(clique)==h and rows&source==clique and allrows.isdisjoint(rows)
  allrows|=rows
  if cliquecount<q:selected|=rows
  cliquecount+=1
 assert cliquecount==h**(k-1) and len(allrows)==k*d and source<=allrows
 assert len(selected)==d and len(selected&source)==d//k
 moment_check(selected,n)
 tv=F(1,2)*(d*abs(F(1,d)-F(1,k*d))+(k*d-d)*F(1,k*d))
 assert tv==1-F(1,k)
 # Compare uniform source with the selected block union: exact sharp TV,
 # equal collision, and exact observation replacement budget.
 repairtv=F(len(source-selected),d)
 assert repairtv==tv and F(1,len(selected))==F(1,len(source))
 cases.append(dict(k=k,h=h,hadamardOrder=n,sourceAtoms=d,maximumOrthogonalSubset=h,hadamardMixtureDistance=str(tv),allCompletionAtoms=len(allrows),completedOffsetCliques=cliquecount,repairHadamardBlocks=q,minimumObservationReplacements=d-d//k,unchangedCollision=str(F(1,d)),allSourceMomentsAndRepairMomentsExact=True))
result={'passed':True,'cases':cases,'allCompletionBlocksExactlyOrthogonal':True,'completionsHaveDisjointSupports':True,'noNewHadamardOrderClaim':True}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
