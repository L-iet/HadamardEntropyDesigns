# SPDX-License-Identifier: Apache-2.0
from fractions import Fraction as F
from itertools import product,combinations
from math import prod

d=5;cube=list(product((-1,1),repeat=d))
features=[()]+[(i,) for i in range(d)]+list(combinations(range(d),2))
def chi(x,s):return prod(x[i] for i in s)
def collision(p):return sum(x*x for x in p.values())
def feasible(p):
    return min(p.values())>=0 and all(sum(p[x]*chi(x,s) for x in p)==(s==()) for s in features)
code={tuple((-1)**((u&m).bit_count()) for m in range(1,6)) for u in range(8)}
assert len(code)==8
cosets=[];seen=set()
for x in cube:
    if x in seen:continue
    coset={tuple(a*b for a,b in zip(x,y)) for y in code}
    cosets.append(coset);seen|=coset
assert len(cosets)==4
qs=[{x:F(x in c,8) for x in cube} for c in cosets]
assert all(feasible(q) and collision(q)==F(1,8) for q in qs)
p={x:(qs[0][x]+qs[1][x])/2 for x in cube}
for t in (F(0),F(1,3),F(1,2),F(1)):
    bad={x:(1-t)*p[x]+t*qs[2][x] for x in cube}
    good={x:(1-t)*p[x]+t*qs[0][x] for x in cube}
    assert feasible(bad) and feasible(good)
    assert collision(bad)==F(1,16)-t/8+F(3,16)*t*t
    assert collision(good)==F(1,16)+t*t/16
assert F(1,16)-F(1,24)==F(1,48)

def kernel_vector(support):
    a=[[F(chi(x,s)) for x in support] for s in features]
    pivot=[];r=0
    for j in range(len(support)):
        i=next((i for i in range(r,len(a)) if a[i][j]),None)
        if i is None:continue
        a[r],a[i]=a[i],a[r];z=a[r][j];a[r]=[x/z for x in a[r]]
        for i in range(len(a)):
            if i!=r:
                z=a[i][j];a[i]=[x-z*y for x,y in zip(a[i],a[r])]
        pivot.append(j);r+=1
        if r==len(a):break
    free=next((j for j in range(len(support)) if j not in pivot),None)
    if free is None:return None
    z=[F(0)]*len(support);z[free]=1
    for i,j in enumerate(pivot):z[j]=-a[i][free]
    assert all(sum(z[j]*chi(x,s) for j,x in enumerate(support))==0 for s in features)
    return z

p={x:F(1,len(cube)) for x in cube};steps=0
while True:
    support=list(p);z=kernel_vector(support)
    if z is None:break
    if sum(p[x]*v for x,v in zip(support,z))<0:z=[-v for v in z]
    t=min(p[x]/(-v) for x,v in zip(support,z) if v<0)
    before=collision(p)
    p={x:p[x]+t*v for x,v in zip(support,z) if p[x]+t*v>0}
    assert feasible(p) and collision(p)>before
    steps+=1
assert steps<=len(cube)-len(features) and len(p)<=len(features)
print(dict(endpoint_steps=steps,final_support=len(p),collision=str(collision(p)),
           checks='exact endpoint algorithm and distinct bridge barriers passed'))
