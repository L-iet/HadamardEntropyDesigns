# SPDX-License-Identifier: Apache-2.0
from fractions import Fraction as F
from itertools import product,combinations

d=4;M=2**d;N=8
cube=list(product((-1,1),repeat=d))
sets=[(i,) for i in range(d)]+list(combinations(range(d),2))
def chi(x,s):
    out=1
    for i in s:out*=x[i]
    return out
def correct(p):
    moments={s:sum(p[x]*chi(x,s) for x in cube) for s in sets}
    f={x:sum(moments[s]*chi(x,s) for s in sets) for x in cube}
    b=max(f.values());beta=max(F(0),max(f[x]-M*p[x] for x in cube))
    q={x:(p[x]+(b-f[x])/M)/(1+b) for x in cube}
    assert min(q.values())>=0 and sum(q.values())==1
    assert all(sum(q[x]*chi(x,s) for x in cube)==0 for s in sets)
    cp=sum(t*t for t in p.values());cq=sum(t*t for t in q.values())
    e2=sum(t*t for t in moments.values())
    assert cq==F(1,M)+(cp-F(1,M)-e2/M)/(1+b)**2
    tv=sum(abs(q[x]-p[x]) for x in cube)/2
    assert tv<=b/(1+b) and cq>=cp/(1+b)**2
    qstar={x:(p[x]+(beta-f[x])/M)/(1+beta) for x in cube}
    assert min(qstar.values())>=0
    assert all(sum(qstar[x]*chi(x,s) for x in cube)==0 for s in sets)
    return q,b,cp,cq

had=[tuple((-1)**((i&j).bit_count()) for j in range(1,5)) for i in range(N)]
p={x:F(x in had,N) for x in cube}
t=F(1,2**40);p[had[0]]+=t;p[had[1]]-=t
q,b,cp,cq=correct(p)
assert cp>=F(1,N) and b<=F(1,2048*N**3)
assert 0<=F(1,N)-cq<=F(1,1024*N**4)
good=[x for x in cube if abs(N*q[x]-1)<=F(1,4*N)]
assert len(good)==N
assert all(sum(F(chi(x,s),N) for x in good)==0 for s in sets)
print('Tiny weighted perturbation: exact repair and extraction window passed.')
# Replace one row by a different cube row: quantized nonzero error.
outside=next(x for x in cube if x not in had)
candidate=had[1:]+[outside]
p={x:F(x in candidate,N) for x in cube}
q,b,cp,cq=correct(p)
assert b>=F(1,N) and F(1,N)-cq>=F(1,2*N*N)
print('Nonisotropic uniform candidate: universal-buffer gap passed; B =',b)
