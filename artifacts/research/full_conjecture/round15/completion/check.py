# SPDX-License-Identifier: Apache-2.0
"""Original Gaussian-rational kernel search; no external packages."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
root=Path(__file__).resolve().parent
def z(a=0,b=0):return(F(a),F(b))
zero=z();one=z(1);ii=z(0,1)
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[0],-a[1])
def sub(a,b):return add(a,neg(b))
def mul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def conj(a):return(a[0],-a[1])
def div(a,b):
    q=mul(a,conj(b));norm=b[0]**2+b[1]**2;return(q[0]/norm,q[1]/norm)
phases=(one,ii,neg(one),neg(ii));phase_set=set(phases)
def total(xs):
    out=zero
    for x in xs:out=add(out,x)
    return out
def gram(a):return [[total(mul(x,conj(y)) for x,y in zip(r,s)) for s in a] for r in a]
def kernel(a,n):
    a=[row[:] for row in a];piv=[];r=0
    for j in range(n):
        hit=next((i for i in range(r,len(a)) if a[i][j]!=zero),None)
        if hit is None:continue
        a[r],a[hit]=a[hit],a[r];d=a[r][j];a[r]=[div(x,d) for x in a[r]]
        for i in range(len(a)):
            if i!=r:
                d=a[i][j];a[i]=[sub(x,mul(d,y)) for x,y in zip(a[i],a[r])]
        piv.append(j);r+=1
        if r==len(a):break
    basis=[]
    for j in range(n):
        if j in piv:continue
        v=[zero]*n;v[j]=one
        for i,k in enumerate(piv):v[k]=neg(a[i][j])
        basis.append(v)
    return basis
def extend(v):
    n=len(v);a=[[conj(x) for x in col] for col in zip(*v)]
    b=kernel(a,n);r=len(b);assert r==n-len(v[0])
    for count,tail in enumerate(product(phases,repeat=r-1),1):
        coeff=(one,)+tail
        candidate=[total(mul(c,base[i]) for c,base in zip(coeff,b)) for i in range(n)]
        if not all(x in phase_set for x in candidate):continue
        assert all(total(mul(x,y) for x,y in zip(row,candidate))==zero for row in a)
        return [row+[x] for row,x in zip(v,candidate)],count
    return None,4**(r-1)
def verify(h,r=3):
    n=len(h);v=[row[:-r] for row in h];counts=[]
    while len(v[0])<n:
        missing=n-len(v[0]);v,count=extend(v);assert v is not None
        assert count<=4**(missing-1);counts.append(count)
    assert gram(v)==[[z(n*(i==j)) for j in range(n)] for i in range(n)]
    assert sum(counts)<=sum(4**j for j in range(r))
    return dict(n=n,startingDefect=r,candidateCounts=counts,totalCandidates=sum(counts),completed=True)
records=[]
for n in (4,8):
    h=[[z((-1)**((i&j).bit_count())) for j in range(n)] for i in range(n)]
    records.append(verify(h))
    if n==8:records.append(verify(h,4))
for p in (5,13):
    residues={x*x%p for x in range(1,p)}
    chi=lambda x:0 if x%p==0 else 1 if x%p in residues else -1
    c=[[0]+[1]*p]+[[1]+[chi(j-i) for j in range(p)] for i in range(p)]
    n=p+1;h=[[z(i==j,c[i][j]) for j in range(n)] for i in range(n)]
    assert gram(h)==[[z(n*(i==j)) for j in range(n)] for i in range(n)]
    records.append(verify(h))
out=dict(passed=True,records=records,maximumCodimensionThreeCandidates=21,
         exactArithmetic='Gaussian pairs of standard-library Fraction',
         scope='Classical real completion guarantees success for defect<=3; tests do not prove that input theorem.')
(root/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
