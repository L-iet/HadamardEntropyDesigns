# SPDX-License-Identifier: Apache-2.0
from fractions import Fraction as F
from itertools import product,combinations

d=4;cube=list(product((-1,1),repeat=d));s=len(cube)
features=[()]+[(i,) for i in range(d)]+list(combinations(range(d),2))
def chi(x,t):
    out=1
    for i in t:out*=x[i]
    return out
a=[[F(chi(x,t)) for x in cube] for t in features]
k=len(features)
assert all(sum(a[i][j]*a[l][j] for j in range(s))==s*(i==l)
           for i in range(k) for l in range(k))
# AA^T=sI, giving the explicit exact right inverse A^T/s.
r=[[a[i][j]/s for i in range(k)] for j in range(s)]
gamma=max(sum(map(abs,row)) for row in r)
t=F(1,1024)
p=[F(1,s)*(1+t*x[0]+t*x[1]*x[2]) for x in cube]
m=[sum(a[i][j]*p[j] for j in range(s))-(i==0) for i in range(k)]
tau=max(map(abs,m));assert min(p)>=gamma*tau
q=[p[j]-sum(r[j][i]*m[i] for i in range(k)) for j in range(s)]
assert min(q)>=0 and sum(q)==1
assert all(sum(a[i][j]*q[j] for j in range(s))==(i==0) for i in range(k))
assert all(x==F(1,s) for x in q)
assert max(abs(q[j]-p[j]) for j in range(s))<=gamma*tau
cp=sum(x*x for x in p);cq=sum(x*x for x in q)
assert cq>=cp-2*gamma*tau
print(dict(d=d,support=s,feature_rank=k,gamma=str(gamma),tau=str(tau),
           result='exact positive adaptive correction passed'))
