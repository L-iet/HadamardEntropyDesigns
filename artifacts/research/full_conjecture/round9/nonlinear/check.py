"""Exact original stdlib checks: restriction radicals, support repair, quadratic cliques."""
from pathlib import Path
from itertools import combinations
import json,hashlib

def basis(vectors):
 b={}
 for x in vectors:
  while x:
   j=x.bit_length()-1
   if j not in b:b[j]=x;break
   x^=b[j]
 return list(b.values())
def rank(v):return len(basis(v))
def code_gens(s,r,d):return [sum(int(z&m==m)<<i for i,z in enumerate(s)) for m in range(1<<r) if m.bit_count()<=d]
def even_basis(b):
 odd=next((x for x in b if x.bit_count()%2),None)
 return basis([x if x.bit_count()%2==0 else x^odd for x in b]) if odd is not None else b

def code_check(r,t):
 s=sorted(set(range(1<<r))-set(t));n=len(s);a=r-rank([x^t[0] for x in t])
 b=basis(code_gens(s,r,r-2));even=even_basis(b)
 gram=[sum(((x&y).bit_count()%2)<<j for j,y in enumerate(even)) for x in even]
 assert len(b)==n-a and len(even)==n-a-1 and rank(gram)==n-2*a-2
 return dict(seedBits=r,support=n,complementAffineDimension=r-a,restrictionRank=len(b),evenRestrictionDimension=len(even),bilinearRank=rank(gram),puncturedBits=n-4)

def clique_certificate(t,target,witness):
 s=sorted(set(range(16))-set(t));gens=code_gens(s,4,2);code={0}
 for x in gens:code|={y^x for y in list(code)}
 vertices=sorted(x for x in code if x.bit_count()==6 and x&1==0)
 adj=[sum(1<<j for j,y in enumerate(vertices) if (x^y).bit_count()==6) for x in vertices]
 calls=0
 def search(chosen,cand):
  nonlocal calls
  calls+=1
  if chosen==target:return True
  if chosen+cand.bit_count()<target:return False
  while cand:
   bit=cand&-cand;cand^=bit;j=bit.bit_length()-1
   if search(chosen+1,cand&adj[j]):return True
  return False
 assert not search(0,(1<<len(vertices))-1)
 assert len(witness)==target-1 and all(x in vertices for x in witness)
 assert all((x^y).bit_count()==6 for x,y in combinations(witness,2))
 # Derive a polynomial certificate for every displayed witness.
 polys=[];mons=[m for m in range(16) if m.bit_count()<=2]
 for x in witness:
  for flags in range(1<<len(gens)):
   val=0
   for j,g in enumerate(gens):
    if (flags>>j)&1:val^=g
   if val==x:polys.append([mons[j] for j in range(len(mons)) if (flags>>j)&1]);break
  else:raise AssertionError('missing polynomial')
 digest=hashlib.sha256(json.dumps([vertices,adj]).encode()).hexdigest()
 return dict(omittedLabels=t,codeSize=len(code),balancedVertices=len(vertices),excludedCliqueSize=target,maximumBits=target-1,recursiveStates=calls,witnessWords=witness,witnessMonomialMasks=polys,graphSHA256=digest)

def solve(a,b,n):
 a=[sum(x<<j for j,x in enumerate(row))|(v<<n) for row,v in zip(a,b)];r=0;piv=[]
 for j in range(n):
  k=next((k for k in range(r,len(a)) if (a[k]>>j)&1),None)
  if k is None:continue
  a[r],a[k]=a[k],a[r]
  for k in range(len(a)):
   if k!=r and (a[k]>>j)&1:a[k]^=a[r]
  piv.append(j);r+=1
 assert not any((x&((1<<n)-1))==0 and (x>>n)&1 for x in a)
 return [((a[i]>>n)&1) for i in range(n)] if piv==list(range(n)) else None

def paley(p):
 assert p%4==3 and all(p%d for d in range(2,int(p**.5)+1))
 chi=lambda x:0 if x%p==0 else 1 if pow(x%p,(p-1)//2,p)==1 else -1
 h=[[1]*(p+1)]+[[1]+[chi(j-i)-int(i==j) for j in range(p)] for i in range(p)]
 assert all(sum(x*y for x,y in zip(a,b))==(p+1)*int(i==j) for i,a in enumerate(h) for j,b in enumerate(h))
 return h

def anf(f,r):
 a=f[:]
 for j in range(r):
  for z in range(1<<r):
   if z&(1<<j):a[z]^=a[z^(1<<j)]
 return [m for m,x in enumerate(a) if x]

def repair(h,r,s,outside_basis):
 n=len(h);s=list(reversed(s));polys=[];degree=0
 for j in range(1,n):
  f=[0]*(1<<r)
  for i,z in enumerate(s):f[z]=int(h[i][j]<0)
  if len(outside_basis)==1:f[outside_basis[0]]=sum(f)%2
  else:
   mons=[0]+[1<<i for i in range(r)]
   defect=[sum(f[z]*int(z&m==m) for z in range(1<<r))%2 for m in mons]
   a=[[int(z&m==m) for z in outside_basis] for m in mons];vals=solve(a,defect,r+1);assert vals is not None
   for z,v in zip(outside_basis,vals):f[z]=v
  assert all(f[z]==int(h[i][j]<0) for i,z in enumerate(s))
  poly=anf(f,r);degree=max(degree,max((x.bit_count() for x in poly),default=0));polys.append(poly)
 return dict(order=n,seedBits=r,repairLocations=outside_basis,maximumDegree=degree,allOriginalMomentsPreserved=True)

cases=[code_check(4,[0,1,2,3]),code_check(4,[0,1,2,4]),code_check(5,[0,1,2,4]),code_check(6,[0,1,2,4]),code_check(5,list(range(12))),code_check(5,[2,4,5,9,11,14,17,18,23,24,28,31])]
cliques=[clique_certificate([0,1,2,3],6,[246,826,1372,1708,3178]),clique_certificate([0,1,2,4],8,[246,826,1372,1708,3178,3504,3606])]
repairs=[repair(paley(11),4,sorted(set(range(16))-{0,1,2,4}),[0]),repair(paley(19),5,sorted(set(range(32))-{2,4,5,9,11,14,17,18,23,24,28,31}),[2,4,5,9,11,17]),repair(paley(59),6,sorted(set(range(64))-{0,1,2,4}),[0])]
assert [x['maximumDegree'] for x in repairs]==[3,3,5]
result={'passed':True,'restrictionAndRadicalChecks':cases,'exactQuadraticClassifications':cliques,'explicitSupportSyndromeRepairs':repairs}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
