"""Exact original standard-library certificates for collision ascent traps."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from collections import Counter
import json
from explore_d4 import main as enumerate_d4

def char(x,m):return 1-2*((x&m).bit_count()%2)
def moment_masks(d):return [0]+[1<<i for i in range(d)]+[(1<<i)|(1<<j) for i,j in combinations(range(d),2)]
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
  if r==len(a):break
 return r

def check_moments(w,d):
 assert sum(w)==1 and all(x>=0 for x in w)
 assert all(sum(w[x]*char(x,m) for x in range(1<<d))==int(m==0) for m in moment_masks(d))
 return sum(x*x for x in w)

small=[]
for d in [4,5]:
 w=[F(1,6) if x==0 else F(1,12) if x.bit_count() in ([2,3] if d==4 else [3]) else F(0) for x in range(1<<d)]
 c=check_moments(w,d);assert c==F(7,72)
 support=[x for x in range(1<<d) if w[x]]
 r=rank([[char(x,m) for x in support] for m in moment_masks(d)]);assert r==11
 for x in range(1<<d):
  k=x.bit_count();q=F(k*k-5*k+12,72) if d==4 else F(1,12)+F((k-3)**2,108)
  assert (q==w[x]) if x in support else (q>w[x])
 small.append(dict(bits=d,support=len(support),momentColumnRank=r,collision=str(c),strictDualExposingCertificate=True))
# Exhaust all four-bit vertices in the five-dimensional high-degree Walsh coordinates.
enumerate_d4()
path=Path(__file__).with_name('d4_vertices.json');verts=json.loads(path.read_text())
weights=[[F(x) for x in v['weights']] for v in verts];gains=[]
for i,w in enumerate(weights):
 c=check_moments(w,4)
 gain=max(sum(a*b for a,b in zip(w,v))-c for j,v in enumerate(weights) if j!=i)
 assert gain<0;gains.append(str(gain))
assert len(weights)==26 and Counter(v['collision'] for v in verts)=={'1/8':10,'7/72':16}
# Direct seven-bit example: explicitly verify full moments and interpolation.
b=[1,2,3,4,5,8,10]
support=[sum((char(z,m)==-1)<<j for j,m in enumerate(b)) for z in range(16)]
assert len(set(support))==16
w=[F(int(x in support),16) for x in range(128)]
assert check_moments(w,7)==F(1,16)
rep={0:0}
for j,x in enumerate(b):rep.setdefault(x,1<<j)
for i,j in combinations(range(7),2):rep.setdefault(b[i]^b[j],(1<<i)|(1<<j))
assert set(rep)==set(range(16))
for z in range(16):
 for x in range(128):
  l=sum(F(char(z,m)*char(x,mon),16) for m,mon in rep.items())
  assert abs(l)<=1
  if x in support:assert l==int(x==support[z])
family=[]
for s in [2,3,4]:
 h=1<<s;b=list(range(1,h))+[j<<s for j in range(1,h)]+[1|(1<<s)]
 assert len(b)==2*h-1 and len(set(b))==len(b)
 allchars={0,*b,*[x^y for x,y in combinations(b,2)]}
 assert allchars==set(range(h*h))
 rows=[tuple(char(z,m) for m in b) for z in range(h*h)]
 assert len(set(rows))==h*h
 # Uniform pairwise moments, checked as integer character sums.
 assert all(sum(row[j] for row in rows)==0 for j in range(len(b)))
 assert all(sum(row[i]*row[j] for row in rows)==0 for i,j in combinations(range(len(b)),2))
 family.append(dict(s=s,bits=len(b),hadamardOrder=2*h,support=h*h,collision=str(F(1,h*h)),globalCollision=str(F(1,2*h)),ratio=str(F(2,h)),strictRadius=str(F(2,h*h*(h*h+1)))))
out={'passed':True,'smallTraps':small,'d4Vertices':26,'d4CollisionCounts':dict(Counter(v['collision'] for v in verts)),'allD4VerticesStrictLocalMaxima':True,'directD7InterpolationCheckedOnWholeCube':True,'infiniteFamilyChecks':family}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
