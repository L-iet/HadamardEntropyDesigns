# SPDX-License-Identifier: Apache-2.0
"""Exact Gaussian-rational residual and phase-graph completion checks."""
from fractions import Fraction as F
from pathlib import Path
import json
root=Path(__file__).resolve().parent
def z(a=0,b=0):return(F(a),F(b))
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[0],-a[1])
def sub(a,b):return add(a,neg(b))
def mul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def conj(a):return(a[0],-a[1])
def norm(a):return a[0]**2+a[1]**2
def div(a,b):
    c=mul(a,conj(b));t=norm(b);return(c[0]/t,c[1]/t)
one=z(1);zero=z();ii=z(0,1);phases={one,neg(one),ii,neg(ii)}
def total(xs):
    out=zero
    for x in xs:out=add(out,x)
    return out
def gram(a):return[[total(mul(x,conj(y)) for x,y in zip(r,s)) for s in a] for r in a]
def rank(a):
    a=[list(map(F,r)) for r in a];k=0
    for j in range(len(a[0])):
        hit=next((i for i in range(k,len(a)) if a[i][j]),None)
        if hit is None:continue
        a[k],a[hit]=a[hit],a[k];t=a[k][j];a[k]=[x/t for x in a[k]]
        for i in range(len(a)):
            if i!=k:
                t=a[i][j];a[i]=[x-t*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a):break
    return k
def complete(v):
    n=len(v);g=gram(v)
    k=[[sub(z(n*(i==j)),g[i][j]) for j in range(n)] for i in range(n)]
    b=[[norm(k[i][j])/2-1 for j in range(n)] for i in range(n)]
    r=rank(b);assert r in (1,2) and all(x in (-1,0,1) for row in b for x in row)
    other=next((j for j in range(n) if b[0][j]==0),None)
    delta=[]
    for i in range(n):
        if b[0][i]:delta.append(z(b[0][i]))
        else:
            assert other is not None and b[other][i] in (-1,1)
            delta.append(z(0,b[other][i]))
    a=[None]*n
    for start in range(n):
        if a[start] is not None:continue
        a[start]=one;todo=[start]
        while todo:
            i=todo.pop()
            for j in range(n):
                if k[i][j]==zero or a[j] is not None:continue
                factor=add(one,mul(delta[i],conj(delta[j])))
                a[j]=conj(div(k[i][j],mul(a[i],factor)))
                assert a[j] in phases;todo.append(j)
    residual=[[a[i],mul(a[i],delta[i])] for i in range(n)]
    assert gram(residual)==k
    h=[row+tail for row,tail in zip(v,residual)]
    assert all(x in phases for row in h for x in row)
    assert gram(h)==[[z(n*(i==j)) for j in range(n)] for i in range(n)]
    return dict(n=n,blochRank=r,quaternaryCompletion=True)
records=[]
for n in (4,8):
    h=[[z((-1)**((i&j).bit_count())) for j in range(n)] for i in range(n)]
    records.append(complete([row[:-2] for row in h]))
p=5;residues={x*x%p for x in range(1,p)}
chi=lambda x:0 if x%p==0 else 1 if x%p in residues else -1
c=[[0]+[1]*p]+[[1]+[chi(j-i) for j in range(p)] for i in range(p)]
h=[[z(i==j,c[i][j]) for j in range(6)] for i in range(6)]
assert gram(h)==[[z(6*(i==j)) for j in range(6)] for i in range(6)]
records.append(complete([row[:-2] for row in h]))
# Codimension one: the residual first column has fourth-root entries.
v=[row[:-1] for row in h];g=gram(v)
k=[[sub(z(6*(i==j)),g[i][j]) for j in range(6)] for i in range(6)]
tail=[row[0] for row in k];assert all(x in phases for x in tail)
assert gram([row+[t] for row,t in zip(v,tail)])==gram(h)
# Abstract tight residual with three qubit axes, not asserted realizable
# as a quaternary partial-Hadamard complement.
r=[[z(1,1),zero],[zero,z(1,1)],[one,one],[one,neg(one)],[one,ii],[one,neg(ii)]]
k=gram(r);b=[[norm(x)/2-1 for x in row] for row in k]
assert rank(b)==3
out=dict(passed=True,completionChecks=records,codimensionOne=True,abstractResidualBlochRank=3,
         classicalAutomaticCompletionInput='Real codimension-four Hadamard completion; not proved by these finite tests.')
(root/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
