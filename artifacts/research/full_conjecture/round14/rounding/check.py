# SPDX-License-Identifier: Apache-2.0
"""Exact Gaussian-rational checks of the constructive phase certificate."""
from fractions import Fraction as F
from pathlib import Path
import json

def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def conj(a):return (a[0],-a[1])
def norm(a):return a[0]*a[0]+a[1]*a[1]
def sub(a,b):return add(a,(-b[0],-b[1]))
def total(xs):
    a=(F(0),F(0))
    for x in xs:a=add(a,x)
    return a
def gram(a):return [[total(mul(x,conj(y)) for x,y in zip(r,s)) for s in a] for r in a]
def had(a):
    n=len(a)
    return gram(a)==[[(F(n*int(i==j)),F(0)) for j in range(n)] for i in range(n)]
def power4(a):return mul(mul(a,a),mul(a,a))
ROOTS=[(F(1),F(0)),(F(-1),F(0)),(F(0),F(1)),(F(0),F(-1))]
def dephase(a,k,l):
    return [[mul(mul(mul(x,conj(a[k][j])),conj(a[i][l])),a[k][l]) for j,x in enumerate(r)] for i,r in enumerate(a)]
def round4(a):return [[min(ROOTS,key=lambda q:norm(sub(x,q))) for x in row] for row in a]
def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [encode(v) for v in x]
    return x

records=[]
for den in (1,2,8,64,1024):
    t=F(1,den);z=((1-t*t)/(1+t*t),2*t/(1+t*t))
    o=(F(1),F(0));m=(-F(1),F(0));nz=(-z[0],-z[1])
    a=[[o,o,o,o],[o,m,z,nz],[o,o,m,m],[o,m,nz,z]]
    # Nontrivial exact row/column gauge exercises all pivot formulas.
    gauges=[o,z,m,conj(z)]
    a=[[mul(mul(x,gauges[i]),gauges[(j+1)%4]) for j,x in enumerate(row)] for i,row in enumerate(a)]
    assert had(a)
    n=len(a);four=[[power4(x) for x in row] for row in a]
    d=F(n**4)-sum(norm(x) for row in gram(four) for x in row)
    assert d>=0
    scores=[];repairs=[]
    for k in range(n):
        for l in range(n):
            b=dephase(a,k,l);q=round4(b)
            score=sum(norm(sub(power4(x),(F(1),F(0)))) for row in b for x in row)
            eta=sum(norm(sub(x,y)) for row,rr in zip(b,q) for x,y in zip(row,rr))
            assert 4*eta<=score
            scores.append(score);repairs.append((eta,had(q)))
    assert sum(scores)==2*d
    idx=min(range(n*n),key=lambda i:scores[i])
    assert scores[idx]<=2*d/(n*n)
    eta=repairs[idx][0]
    certified=eta<F(1,n)
    bound=d/(2*n*n)
    hypothesis=bound<F(1,n)
    if hypothesis:assert certified and repairs[idx][1]
    records.append({'parameterDenominator':den,'deficit':d,'bestFourthError':scores[idx],
                    'roundingError':eta,'sufficientHypothesis':hypothesis,
                    'selectedRoundedMatrixHadamard':repairs[idx][1]})
assert any(r['sufficientHypothesis'] and r['deficit']>0 for r in records)
# A non-Hadamard unit-modulus input exercises the two-objective certificate.
t=F(1,1024);z=((1-t*t)/(1+t*t),2*t/(1+t*t))
a=[[(F(x),F(0)) for x in row] for row in
   [[1,1,1,1],[1,-1,1,-1],[1,1,-1,-1],[1,-1,-1,1]]]
a[1][2]=z
assert not had(a)
g=gram(a);beta2=max(norm(g[i][j]) for i in range(4) for j in range(4) if i!=j)
four=[[power4(x) for x in row] for row in a]
d=F(4**4)-sum(norm(x) for row in gram(four) for x in row)
# sqrt(beta2)+sqrt(d/n) <= sqrt(2*(beta2+d/n)) < sqrt2.
assert beta2+d/4<1
assert any(had(round4(dephase(a,k,l))) for k in range(4) for l in range(4))
(Path(__file__).parent/'checks.json').write_text(json.dumps(encode({'passed':True,'arithmetic':'exact Gaussian rationals','cases':records,
    'nonorthogonalInput':{'maximumCorrelationSquared':beta2,'fourthDeficit':d,'sufficientTwoObjectiveBound':True}}),indent=2)+'\n',encoding='utf-8')
print('Exact phase dephasing, averaging, and threshold rounding checks passed.')
