# SPDX-License-Identifier: Apache-2.0
"""Exact checks of all residue bounds and explicit three-column completion."""
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import json


def dot(a,b):return sum(x*y for x,y in zip(a,b))
def parity(row):
    answer=1
    for x in row:answer*=x
    return answer


def hadamard(order):
    if order&(order-1)==0:
        h=[[1]]
        while len(h)<order:h=[r+r for r in h]+[r+[-x for x in r] for r in h]
    else:
        q=order-1;assert q in (11,19,23)
        residues={x*x%q for x in range(1,q)}
        chi=lambda x:0 if x%q==0 else (1 if x%q in residues else -1)
        h=[[1]*order]+[[1]+[chi(i-j)-(i==j) for j in range(q)] for i in range(q)]
    assert all(dot(a,b)==order*(i==j) for i,a in enumerate(h) for j,b in enumerate(h))
    return h


def check(w):
    n=len(next(iter(w)));assert all(x[0]==1 for x in w)
    m=[[sum(p*x[i]*x[j] for x,p in w.items()) for j in range(n)] for i in range(n)]
    assert all(m[i][j]==(i==j) for i in range(n) for j in range(n))
    c=sum(p*p for p in w.values());bound=F(1,4*((n+3)//4))
    assert c<=bound
    if n%4==1:
        z=[sum(p*parity(x)*x[i] for x,p in w.items()) for i in range(n)]
        zz=sum(t*t for t in z);assert zz<=1
        total=F(0)
        for x,px in w.items():
            for y,py in w.items():
                q=parity(x)*parity(y)*dot(x,y)
                assert q%4==1 and q*q+2*q-3>=0
                total+=px*py*(q*q+2*q-3)
        assert total==n+2*zz-3
        assert (n-1)*(n+3)*c<=total<=n-1
    return c


def complete_three(v):
    count=len(v);n=len(v[0]);assert count==n+3 and n%4==1
    switched=[tuple(parity(x)*y for y in x) for x in v]
    k=[[count*(i==j)-dot(x,y) for j,y in enumerate(switched)] for i,x in enumerate(switched)]
    assert all(k[i][j] in ((3,) if i==j else (-1,3)) for i in range(count) for j in range(count))
    representatives=[];types=[]
    for i in range(count):
        candidates=[t for t,j in enumerate(representatives) if k[i][j]==3]
        if not candidates:types.append(len(representatives));representatives.append(i)
        else:assert len(candidates)==1;types.append(candidates[0])
    assert len(representatives)<=4
    tetra=((1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1))
    added=[tetra[t] for t in types]
    assert all(dot(added[i],added[j])==k[i][j] for i in range(count) for j in range(count))
    h=[x+added[i] for i,x in enumerate(switched)]
    assert all(dot(x,y)==count*(i==j) for i,x in enumerate(h) for j,y in enumerate(h))


def main():
    cases=[];reconstructions=[]
    for size in (4,8,12,16,20,24,32):
        h=hadamard(size)
        for n in range(max(3,size-3),size+1):
            v=[tuple(row[:n]) for row in h]
            assert len(set(v))==size
            w={x:F(1,size) for x in v}
            assert check(w)==F(1,size)
            cases.append({'n':n,'hadamardOrder':size,'collision':str(F(1,size))})
        if size>=8:
            triples=list(combinations(range(1,size),3))
            if size>=20:triples=triples[:12]
            for remove in triples:
                v=[tuple(x[j] for j in range(size) if j not in remove) for x in h]
                complete_three(v)
            reconstructions.append({'order':size,'deletedColumnTriples':len(triples)})
    # Exact feasible examples far from the equality frontier.
    for n in range(3,8):
        w={(1,)+x:F(1,2**(n-1)) for x in product((-1,1),repeat=n-1)}
        check(w)
    out={'passed':True,'saturatingTruncations':cases,'threeColumnReconstructions':reconstructions,
         'uniformCubeCases':5,'scope':'Exact finite checks support the written universal proof.'}
    Path(__file__).with_name('residue_checks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print('All-residue and three-column completion checks passed:',len(cases),'truncations.')


if __name__=='__main__':main()
