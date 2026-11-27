from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json

def solve(a,b):
 a=[[F(x) for x in r]+[F(z)] for r,z in zip(a,b)];n=len(b)
 for j in range(n):
  i=next((i for i in range(j,n) if a[i][j]),None)
  if i is None:return
  a[i],a[j]=a[j],a[i];z=a[j][j];a[j]=[x/z for x in a[j]]
  for i in range(n):
   if i!=j:
    z=a[i][j];a[i]=[x-z*y for x,y in zip(a[i],a[j])]
 return tuple(r[-1] for r in a)

def main():
 h=[7,11,13,14,15];r=[[1-2*((x&m).bit_count()%2) for m in h] for x in range(16)];verts=set()
 for ix in combinations(range(16),5):
  z=solve([r[i] for i in ix],[-1]*5)
  if z is not None and all(1+sum(a*b for a,b in zip(row,z))>=0 for row in r):verts.add(z)
 out=[]
 for z in sorted(verts):
  w=[(1+sum(a*b for a,b in zip(row,z)))/16 for row in r];c=sum(x*x for x in w)
  out.append(dict(coeffs=list(map(str,z)),weights=list(map(str,w)),collision=str(c)))
 Path(__file__).with_name('d4_vertices.json').write_text(json.dumps(out,indent=2))
 print('vertices',len(verts),'collision values',sorted(set(o['collision'] for o in out)))
if __name__=='__main__':main()
