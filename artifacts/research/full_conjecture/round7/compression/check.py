"""Original exact standard-library checks of finite character rewiring."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from random import Random
import json

def support(masks,s):
 return {sum(((z&m).bit_count()%2)<<j for j,m in enumerate(masks)) for z in range(1<<(2*s))}
def moments(rows,d):
 assert all(sum(1-2*((x>>j)&1) for x in rows)==0 for j in range(d))
 assert all(sum(1-2*(((x>>i)^(x>>j))&1) for x in rows)==0 for i,j in combinations(range(d),2))
def inner(x,y,n):return n-2*(x^y).bit_count()
def segment_min(a,b,c):
 # C((1-t)p+tq) where a=C(p),b=C(q),c=p dot q.
 t=(a-c)/(a+b-2*c)
 t=max(F(0),min(F(1),t))
 return t,(1-t)**2*a+t*t*b+2*t*(1-t)*c

out=[]
for s in [2,3,4]:
 h=1<<s;n=2*h;d=n-1;e=1
 original=list(range(1,h))+[b<<s for b in range(1,h)]+[e|(e<<s)]
 rows=support(original,s);assert len(rows)==h*h
 moments(rows,d)
 # Check exact inner-product formula and all consequences for orthogonal pairs.
 byseed=[sum(((z&m).bit_count()%2)<<j for j,m in enumerate(original)) for z in range(h*h)]
 for z,z2 in combinations(range(h*h),2):
  a,b=z%h,z//h;aa,bb=z2%h,z2//h
  dot=inner(byseed[z],byseed[z2],n)
  formula=h*int(a==aa)+h*int(b==bb)-1+(1-2*(((a^aa^b^bb)&e).bit_count()%2))
  assert dot==formula
  if dot==0:assert a!=aa and b!=bb and ((a^b)&1)==((aa^bb)&1)
 endpoint=list(range(1,h))+[b|(e<<s) for b in range(1,h)]+[e<<s]
 final=support(endpoint,s);assert len(final)==n and len(rows&final)==h
 assert all(inner(x,y,n)==0 for x,y in combinations(final,2))
 t,minimum=segment_min(F(1,h*h),F(1,n),F(1,2*h*h))
 assert t==F(1,h) and minimum==F(2*h-1,2*h**3)
 # Explicit nonlocal substitution algorithm.
 masks=original[:];masks[h-1],masks[-1]=masks[-1],masks[h-1]
 stages=[rows,support(masks,s)]
 for b in range(2,h):
  masks[h-1+b-1]=b|(e<<s)
  assert len(set(masks))==d and 0 not in masks
  stages.append(support(masks,s))
 assert masks==endpoint and stages[-1]==final and len(stages)-1==h-1
 drops=0;minima=[]
 for i,(old,new) in enumerate(zip(stages,stages[1:])):
  m=len(old);mm=len(new);overlap=len(old&new)
  assert mm in (m,m//2)
  if mm==m//2:
   drops+=1;assert new<=old and overlap==mm
  else:assert overlap==m//2
  a,b,c=F(1,m),F(1,mm),F(overlap,m*mm)
  tt,mi=segment_min(a,b,c);minima.append(mi)
  assert mi==(a if mm<m else F(3,4*m))
 assert drops==s-1 and min(minima)==F(3,4*h*h)
 # Complete diverse maximal overlap cliques, using only block doubling.
 rng=Random(s);completions=0
 for parity in [0,1]:
  pi={}
  for bit in [0,1]:
   aa=[a for a in range(h) if a%2==bit];bb=[b for b in range(h) if b%2==(bit^parity)]
   rng.shuffle(bb);pi.update(zip(aa,bb))
  selected={byseed[a+h*pi[a]] for a in range(h)}
  assert all(inner(x,y,n)==0 for x,y in combinations(selected,2))
  # Flip second block: mixed coordinate and all B columns.
  second_mask=sum(1<<j for j in range(h-1,d))
  completed=selected|{x^second_mask for x in selected}
  assert len(completed)==n and all(inner(x,y,n)==0 for x,y in combinations(completed,2))
  assert len(completed&rows)==h
  completions+=1
 out.append(dict(s=s,h=h,trapAtoms=h*h,compressedAtoms=n,overlap=h,jumps=len(stages)-1,rankDrops=drops,directBridgeMinimum=str(minimum),directBridgeMinimumParameter=str(t),piecewiseBridgeMinimum=str(min(minima)),maximalCliqueCompletions=completions))
result={'passed':True,'cases':out,'allMomentChecksExact':True,'allPairKernelIdentitiesVerified':True}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
