"""Exact original stdlib checks of rank-two Gram quantization and repairs."""
from fractions import Fraction as F
from itertools import combinations
from math import isqrt
from pathlib import Path
from collections import Counter
import json

def gram(h):return [[sum(a*b for a,b in zip(x,y)) for y in h] for x in h]
def defect(h):
 n=len(h);g=gram(h);return [[g[i][j]-n*int(i==j) for j in range(n)] for i in range(n)]
def energy(e):return sum(x*x for r in e for x in r)
def rank(a):
 a=[[F(x) for x in row] for row in a];r=0
 for j in range(len(a[0])):
  k=next((k for k in range(r,len(a)) if a[k][j]),None)
  if k is None:continue
  a[r],a[k]=a[k],a[r];z=a[r][j];a[r]=[x/z for x in a[r]]
  for k in range(r+1,len(a)):
   z=a[k][j]
   if z:a[k]=[x-z*y for x,y in zip(a[k],a[r])]
  r+=1
 return r

def det(a):
 a=[r[:] for r in a];n=len(a);old=1;sgn=1
 for j in range(n-1):
  k=next((k for k in range(j,n) if a[k][j]),None)
  if k is None:return 0
  if k!=j:a[j],a[k]=a[k],a[j];sgn=-sgn
  p=a[j][j]
  for i in range(j+1,n):
   for l in range(j+1,n):
    num=a[i][l]*p-a[i][j]*a[j][l];assert num%old==0;a[i][l]=num//old
   a[i][j]=0
  old=p
 return sgn*a[-1][-1]

def flip(h,cells):
 a=[r[:] for r in h]
 for i,j in cells:a[i][j]*=-1
 return a

def had(h):return energy(defect(h))==0

def repair_one(h):
 n=len(h);e=defect(h);center=next(i for i in range(n) if sum(x!=0 for x in e[i])==n-1)
 r=[row for i,row in enumerate(h) if i!=center]
 p=[[n*int(i==j)-sum(row[i]*row[j] for row in r) for j in range(n)] for i in range(n)]
 u=[p[i][0] for i in range(n)];assert all(x in (-1,1) for x in u)
 if sum(x*y for x,y in zip(u,h[center]))<0:u=[-x for x in u]
 changed=[j for j in range(n) if u[j]!=h[center][j]];assert len(changed)==1
 answer=flip(h,[(center,changed[0])]);assert had(answer)
 return center,changed[0]

def certify(h):
 n=len(h);e=defect(h);r=rank(e);en=energy(e)
 if r==2:
  lam=en//2;d=isqrt(n*n-lam);assert d*d==n*n-lam and d%2==0
  a=(n-d)//2;assert 1<=a<=n//2 and en==8*a*(n-a)
  assert abs(det(h))==n**((n-2)//2)*(n-2*a)
 else:a=None
 if en==8*(n-1):
  cell=repair_one(h)
  assert sum(had(flip(h,[(i,j)])) for i in range(n) for j in range(n))==1
 return r,en,a

# All normalized order-four sign matrices; row/column sign changes cover all
# order-four matrices without altering real rank or energy.
counts=Counter();rank2=0;repairs=0
for flags in range(1<<9):
 h=[[1]*4 for i in range(4)]
 for i in range(1,4):
  for j in range(1,4):h[i][j]=1-2*((flags>>((i-1)*3+j-1))&1)
 r,en,a=certify(h);counts[(r,en)]+=1;rank2+=r==2;repairs+=en==24
walsh=[[1-2*((i&j).bit_count()%2) for j in range(8)] for i in range(8)]
p=11;chi=lambda x:0 if x%p==0 else 1 if pow(x%p,5,p)==1 else -1
paley=[[1]*12]+[[1]+[chi(j-i)-int(i==j) for j in range(p)] for i in range(p)]
attain=[];counter=[]
for h in [walsh,paley]:
 n=len(h);assert had(h)
 for a in range(1,n//2+1):
  g=flip(h,[(0,j) for j in range(a)]);r,en,aa=certify(g)
  assert r==2 and aa==a
  attain.append(dict(n=n,A=a,energy=en,determinantMagnitude=abs(det(g))))
 g=flip(h,[(0,0),(0,2),(1,0),(1,2)]);r,en,a=certify(g)
 assert r==2 and a==4 and not had(g)
 for x in [g,list(map(list,zip(*g)))]:
  e=defect(x);edges=[(i,j) for i,j in combinations(range(n),2) if e[i][j]]
  deg=[sum(i in edge for edge in edges) for i in range(n)]
  assert sorted(d for d in deg if d)==sorted([n//2-2]*2+[2]*(n//2-2))
  assert all(abs(e[i][j])==4 for i,j in edges)
  assert not any(all(i in edge for edge in edges) for i in range(n))
  lower=F(sum(abs(e[i][j]) for i,j in edges),2*max(deg));assert lower==4
 assert had(flip(g,[(0,0),(0,2),(1,0),(1,2)]))
 counter.append(dict(n=n,rank=r,energy=en,minimumEntryRepairs=4,noOneRowOrColumnRepair=True,determinant=det(g),nonsingular=det(g)!=0))
out={'passed':True,'allNormalizedOrderFourCases':512,'orderFourRankTwoCases':rank2,'orderFourUniqueOneEntryRepairs':repairs,'orderFourRankEnergyCounts':[dict(rank=r,energy=e,count=c) for (r,e),c in sorted(counts.items())],'allEnergyParametersAttained':attain,'rectangularCounterexamples':counter}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
