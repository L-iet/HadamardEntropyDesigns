# SPDX-License-Identifier: Apache-2.0
"""Independent exact n=5 equality/completion check from H8 minus 3 cols."""
from fractions import Fraction as F
from itertools import product
from math import prod
N,n=8,5
h=[[(-1)**((i&j).bit_count()) for j in range(N)] for i in range(N)]
v=[row[:n] for row in h]
assert all(row[0]==1 for row in v)
assert len(set(map(tuple,v)))==N
eps=[prod(row[1:]) for row in v]
z=[sum(F(eps[i]*v[i][j],N) for i in range(N)) for j in range(n)]
assert sum(t*t for t in z)==1
assert all(sum(v[i][j]*z[j] for j in range(n))==eps[i] for i in range(N))
assert all(sum(F(v[i][a]*v[i][b],N) for i in range(N))==(a==b)
           for a in range(n) for b in range(n))
vp=[[eps[i]*x for x in v[i]] for i in range(N)]
gram=[[sum(a*b for a,b in zip(x,y)) for y in vp] for x in vp]
poly=lambda q:q*q+2*q-3
assert all(poly(gram[i][j])==((n-1)*(n+3) if i==j else 0)
           for i in range(N) for j in range(N))
assert sum(F(poly(gram[i][j]),N*N) for i in range(N) for j in range(N))==n-1
k=[[N*(i==j)-gram[i][j] for j in range(N)] for i in range(N)]
types=[]; labels=[]
for i in range(N):
    matches=[a for a,j in enumerate(types) if k[i][j]==3]
    if matches: labels.append(matches[0])
    else: labels.append(len(types));types.append(i)
assert len(types)<=4
tetra=[(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]
r=[tetra[a] for a in labels]
assert all(sum(a*b for a,b in zip(r[i],r[j]))==k[i][j]
           for i in range(N) for j in range(N))
completed=[vp[i]+list(r[i]) for i in range(N)]
assert all(sum(a*b for a,b in zip(completed[i],completed[j]))==N*(i==j)
           for i in range(N) for j in range(N))
# All pairs in the entire 4-cube satisfy the parity congruence.
cube=[(1,)+x for x in product((-1,1),repeat=n-1)]
assert all((prod(x)*prod(y)*sum(a*b for a,b in zip(x,y)))%4==1
           for x in cube for y in cube)
print(dict(n=n,N=N,z=list(map(str,z)),collision='1/8',residual_types=len(types),
           completion='exact 8x8 Hadamard verified'))
