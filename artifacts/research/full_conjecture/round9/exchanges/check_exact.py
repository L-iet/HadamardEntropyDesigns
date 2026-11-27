# SPDX-License-Identifier: Apache-2.0
from fractions import Fraction as F
from itertools import product,combinations
from math import prod

cube=list(product((-1,1),repeat=4))
def chi(x,s):return prod(x[i] for i in s)
free=list(combinations(range(4),3))+[(0,1,2,3)]
features=[()]+[(i,) for i in range(4)]+list(combinations(range(4),2))
vs=[tuple(chi(x,s) for s in free) for x in cube]
assert len(set(vs))==16 and all(prod(v)==1 for v in vs)
def law(a):return [F(1,16)*(1+sum(x*y for x,y in zip(a,v))) for v in vs]
def collision(p):return sum(x*x for x in p)
def rank(a):
    a=[list(map(F,row)) for row in a];r=0
    for j in range(len(a[0])):
        pivot=next((i for i in range(r,len(a)) if a[i][j]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r]
        z=a[r][j];a[r]=[x/z for x in a[r]]
        for i in range(len(a)):
            if i!=r:
                z=a[i][j];a[i]=[x-z*y for x,y in zip(a[i],a[r])]
        r+=1
        if r==len(a):break
    return r
uniform=[tuple(F(sign if i==j else 0) for i in range(5)) for j in range(5) for sign in (-1,1)]
weighted=[tuple(F(x,3) for x in s) for s in product((-1,1),repeat=5) if prod(s)==1]
vertices=uniform+weighted
for a in weighted:
    p=law(a);assert collision(p)==F(7,72)
    for i in range(5):
        b=tuple(F((1 if a[i]>0 else -1) if j==i else 0) for j in range(5))
        q=law(b);assert collision(q)==F(1,8)
        support=[j for j in range(16) if p[j] or q[j]]
        assert len(support)==12 and all(p[j]!=q[j] for j in support)
        matrix=[[chi(cube[j],s) for j in support] for s in features]
        assert rank(matrix)==11
        for t in (F(0),F(1,4),F(1,2),F(1)):
            mixed=[(1-t)*x+t*y for x,y in zip(p,q)]
            assert min(mixed)>=0
            assert all(sum(mixed[j]*chi(cube[j],s) for j in range(16))==(s==()) for s in features)
            assert collision(mixed)==F(7,72)-t/36+t*t/18
# Independent global section certificate by every straddling vertex chord.
for i in range(5):
    for sign in (-1,1):
        t=F(sign,2);maximum=F(0)
        for a,b in combinations(vertices,2):
            if (a[i]-t)*(b[i]-t)>=0:continue
            u=(t-b[i])/(a[i]-b[i]);point=[u*x+(1-u)*y for x,y in zip(a,b)]
            value=sum(x*x for x in point);assert value<=F(1,2)
            maximum=max(maximum,value)
        assert maximum==F(1,2)
assert F(7,72)-F(3,32)==F(1,288)
print('80 circuit moves, exact moments, rank11, collision paths and all10 section bounds passed.')
