"""Original stdlib exact certificates for minimal-seed nonlinear Hadamard laws."""
from itertools import combinations
from pathlib import Path
from fractions import Fraction as F
import json

def paley(p):
 assert p%4==3 and all(p%d for d in range(2,int(p**.5)+1))
 def chi(a):
  return 0 if a%p==0 else 1 if pow(a%p,(p-1)//2,p)==1 else -1
 h=[[1]*(p+1)]+[[1]+[chi(j-i)-int(i==j) for j in range(p)] for i in range(p)]
 assert all(sum(x*y for x,y in zip(a,b))==(p+1)*int(i==j) for i,a in enumerate(h) for j,b in enumerate(h))
 return h

def rank(v):
 basis={}
 for x in v:
  while x:
   j=x.bit_length()-1
   if j not in basis:basis[j]=x;break
   x^=basis[j]
 return len(basis)

def solve(a,b,n):
 a=[sum(x<<j for j,x in enumerate(row))|(v<<n) for row,v in zip(a,b)];r=0;piv=[]
 for j in range(n):
  k=next((k for k in range(r,len(a)) if (a[k]>>j)&1),None)
  if k is None:continue
  a[r],a[k]=a[k],a[r]
  for k in range(len(a)):
   if k!=r and (a[k]>>j)&1:a[k]^=a[r]
  piv.append(j);r+=1
 if any((x&((1<<n)-1))==0 and (x>>n)&1 for x in a):return None
 return sum(((a[i]>>n)&1)<<j for i,j in enumerate(piv))

def evaluate(poly,z):return sum(int(z&m==m) for m in poly)%2

def extension(labels,values,r,degree):
 mons=[m for m in range(1<<r) if m.bit_count()<=degree]
 a=[[int(z&m==m) for m in mons] for z in labels]
 c=solve(a,values,len(mons))
 if c is None:return None
 poly=[m for j,m in enumerate(mons) if (c>>j)&1]
 assert [evaluate(poly,z) for z in labels]==values
 return poly

cases=[];manifest=[]
for p in [11,19]:
 h=paley(p);n=p+1;r=(n-1).bit_length()
 if n==12:
  seen={};labels=[]
  for row in h:
   x=sum(int(row[j]<0)<<i for i,j in enumerate([1,2,3]))
   labels.append(x+8*seen.get(x,0));seen[x]=seen.get(x,0)+1
  assert labels==[0,5,3,6,13,11,7,14,4,8,1,2]
  assert sorted(seen.values())==[1,1,1,1,2,2,2,2]
  assert not any(len({sum(int(row[j]<0)<<i for i,j in enumerate(ix)) for row in h})==12 for ix in combinations(range(1,12),4))
 else:
  labels=[sum(int(row[j]<0)<<i for i,j in enumerate(range(1,6))) for row in h]
  assert labels==[0,13,27,22,12,25,19,7,15,30,29,26,21,10,20,8,16,1,3,6]
 assert len(set(labels))==n
 binary=[sum(int(row[j]<0)<<i for i,row in enumerate(h)) for j in range(1,n)]
 assert rank(binary)==n-2 and rank(binary+[(1<<n)-1])==n-1
 assert all(rank([x for k,x in enumerate(binary) if k!=j])==n-2 for j in range(n-1))
 polys=[];degrees=[]
 for j in range(1,n):
  values=[int(row[j]<0) for row in h]
  for d in range(r+1):
   poly=extension(labels,values,r,d)
   if poly is not None:break
  assert d<=3;polys.append(poly);degrees.append(d)
 assert degrees.count(1)==(3 if n==12 else 5) and max(degrees)==3
 # Direct weighted moments of the nonlinear polynomial outputs.
 outputs=[[1-2*evaluate(poly,z) for poly in polys] for z in labels]
 assert all(sum(row[j] for row in outputs)==0 for j in range(n-1))
 assert all(sum(row[i]*row[j] for row in outputs)==0 for i,j in combinations(range(n-1),2))
 assert len(set(map(tuple,outputs)))==n
 t=sorted(set(range(1<<r))-set(labels))
 if n==20:
  basis=[2,4,5,9,11,17];assert set(basis)<=set(t) and rank([x^basis[0] for x in basis[1:]])==5
 rm_ranks={}
 for d in [2,3]:
  mons=[m for m in range(1<<r) if m.bit_count()<=d]
  rm_ranks[str(d)]=rank([sum(int(z&m==m)<<i for i,z in enumerate(labels)) for m in mons])
 assert rm_ranks['3']==n
 cases.append(dict(order=n,seedBits=r,affineObservables=degrees.count(1),nonaffineObservables=n-1-degrees.count(1),minimumPerColumnDegrees=degrees,maximumDegree=3,rmRestrictionRanks=rm_ranks,collision=str(F(1,n))))
 manifest.append(dict(order=n,seedBits=r,labels=labels,excludedLabels=t,polynomialMonomialMasks=polys,description='Bit i of a monomial mask denotes factor z_i; mask0 is constant1. Sum monomials modulo2, then output sign(-1)^f. Seed is uniform on labels.'))
# Check all four-point complement cases used by the universal H12 obstruction.
# XOR zero implies affine plane, whose indicator has degree2 and vanishes elsewhere.
plane_count=0
for t in combinations(range(16),4):
 if t[0]^t[1]^t[2]^t[3]:continue
 vals=[int(z in t) for z in range(16)];a=vals[:]
 for j in range(4):
  for z in range(16):
   if z&(1<<j):a[z]^=a[z^(1<<j)]
 assert max(m.bit_count() for m,v in enumerate(a) if v)==2
 plane_count+=1
assert plane_count==140
out={'passed':True,'cases':cases,'allFourPointAffinePlaneIndicatorsChecked':plane_count,'exactNonlinearMomentChecks':True}
here=Path(__file__).resolve().parent
(here/'encodings.json').write_text(json.dumps(manifest,indent=2)+'\n')
(here/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
