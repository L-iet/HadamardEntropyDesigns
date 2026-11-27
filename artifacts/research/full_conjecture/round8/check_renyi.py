# SPDX-License-Identifier: Apache-2.0
"""Exact vertex, entropy-order crossing and gradient certificates."""
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
from random import Random
import json


def dot(a,b):return sum(x*y for x,y in zip(a,b))
def parity(x):
    out=1
    for y in x:out*=y
    return out


def solve(a,b):
    n=len(b);rows=[[F(x) for x in row]+[F(y)] for row,y in zip(a,b)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if rows[i][j]),None)
        if pivot is None:return None
        rows[j],rows[pivot]=rows[pivot],rows[j]
        scale=rows[j][j];rows[j]=[x/scale for x in rows[j]]
        for i in range(n):
            if i==j:continue
            scale=rows[i][j];rows[i]=[x-scale*y for x,y in zip(rows[i],rows[j])]
    return tuple(row[-1] for row in rows)


def main():
    cube=list(product((-1,1),repeat=4))
    normals=[tuple(parity(x)*x[i] for i in range(4))+(parity(x),) for x in cube]
    assert len(set(normals))==16 and all(parity(v)==1 for v in normals)
    vertices={tuple(F(sign if i==j else 0) for i in range(5)) for j in range(5) for sign in (-1,1)}
    vertices|={tuple(F(v,3) for v in s) for s in product((-1,1),repeat=5) if parity(s)==1}
    found=set()
    for active in combinations(normals,5):
        point=solve(active,[-1]*5)
        if point is not None and all(1+dot(v,point)>=0 for v in normals):found.add(point)
    assert found==vertices and len(vertices)==26
    laws=[tuple((1+dot(v,a))/16 for v in normals) for a in vertices]
    assert len(set(laws))==26
    for law in laws:
        assert sum(law)==1 and min(law)>=0
        assert all(sum(p*x[i] for p,x in zip(law,cube))==0 for i in range(4))
        assert all(sum(p*x[i]*x[j] for p,x in zip(law,cube))==0 for i,j in combinations(range(4),2))
    uniform=[w for w in laws if max(w)==F(1,8)]
    weighted=[w for w in laws if max(w)==F(1,6)]
    assert len(uniform)==10 and len(weighted)==16
    assert all(sorted(w)==[F(0)]*5+[F(1,12)]*10+[F(1,6)] for w in weighted)
    assert F(4,3)**6+10*F(2,3)**6<8<F(4,3)**7+10*F(2,3)**7
    local_checks=0
    for alpha in (2,3,6,7,10):
        for w in laws:
            gradient=[p**(alpha-1) for p in w]
            assert all(dot(gradient,v)<dot(gradient,w) for v in laws if v!=w)
            local_checks+=1
        winner=max(sum(p**alpha for p in w) for w in laws)
        expected=8*F(1,8)**alpha if alpha<=6 else F(1,6)**alpha+10*F(1,12)**alpha
        assert winner==expected
    # Check the analytic hull decomposition on rational feasible mixtures.
    rng=Random(20261120);points=list(vertices)
    for _ in range(100):
        choices=rng.sample(points,3);weights=[F(1,6),F(1,3),F(1,2)]
        a=tuple(sum(w*p[i] for w,p in zip(weights,choices)) for i in range(5))
        b=list(map(abs,a));m=min(b);s=tuple(1 if x>=0 else -1 for x in a)
        if m==0 or parity(s)==-1:assert sum(b)<=1
        else:
            assert sum(b)-2*m<=1
            assert all(3*m*F(s[i],3)+(b[i]-m)*s[i]==a[i] for i in range(5))
    record={'passed':True,'analyticVertices':26,'exhaustiveActiveSets':4368,
            'uniformVertices':10,'weightedVertices':16,'integerExponentLocalChecks':local_checks,
            'transitionBracket':[6,7],'rationalHullMixtures':100,
            'scope':'The real-parameter theorem uses the analytic proof, not numerical interpolation.'}
    Path(__file__).with_name('renyi_checks.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Renyi checks passed: 26 vertices, 4368 active sets, 130 exact gradient certificates.')


if __name__=='__main__':main()
