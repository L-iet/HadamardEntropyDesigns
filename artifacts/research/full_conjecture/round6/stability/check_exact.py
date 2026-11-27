# SPDX-License-Identifier: Apache-2.0
from fractions import Fraction as F
from itertools import product
from math import prod, comb

n,N=5,8
A=(n-1)*N
cube=[(1,)+x for x in product((-1,1),repeat=n-1)]
had=[tuple((-1)**((i&j).bit_count()) for j in range(n)) for i in range(N)]
s=F(1,2**30)
w={x:s/F(16)+(1-s)/N*(x in had) for x in cube}
assert all(sum(w[x]*x[i]*x[j] for x in cube)==(i==j)
           for i in range(n) for j in range(n))
eps={x:prod(x[1:]) for x in cube}
z=[sum(w[x]*eps[x]*x[i] for x in cube) for i in range(n)]
h={x:eps[x]-sum(x[i]*z[i] for i in range(n)) for x in cube}
collision=sum(a*a for a in w.values());delta=F(1,N)-collision
def poly(x,y):
    q=eps[x]*eps[y]*sum(a*b for a,b in zip(x,y))
    return q*q+2*q-3
off=sum(w[x]*w[y]*poly(x,y) for x in cube for y in cube if x!=y)
variance=sum(w[x]*h[x]**2 for x in cube)
assert A*delta==2*variance+off
for x in cube:
    b=sum(w[y]*poly(x,y) for y in cube if y!=x)
    assert A*(w[x]-F(1,N))==-2*eps[x]*h[x]-b
assert delta<=F(1,1024*N**4)
e=sum(w[x]*abs(N*w[x]-1) for x in cube)
assert e<F(1,8*N*N)
good=[x for x in cube if abs(N*w[x]-1)<=F(1,4*N)]
assert len(good)==N
assert all(sum(F(x[i]*x[j],N) for x in good)==(i==j)
           for i in range(n) for j in range(n))
# Naive delete-one/renormalize from an isotropic cube destroys balance.
remaining=cube[1:]
assert sum(F(x[1],len(remaining)) for x in remaining)!=0
# Exercise a genuinely nonzero off-pair term: uniform 8-cube, n=9.
n2,N2=9,12
A2=(n2-1)*N2
delta2=F(1,N2)-F(1,2**8)
off2=F(0)
for distance in range(1,9):
    q=(-1)**distance*(n2-2*distance)
    off2+=F(comb(8,distance)*(q*q+2*q-3),2**8)
assert off2>0 and A2*delta2==2+off2
print(dict(n=n,N=N,delta=str(delta),parity_variance=str(variance),
           off_polynomial_defect=str(off),extracted_rows=len(good),
           checks='decomposition, pointwise identity, exact isotropy, deletion obstruction passed'))
