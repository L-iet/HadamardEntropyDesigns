"""Exact four-bit pairwise-independent polytope and sign-span classification.

Standard-library only. No external research code. All combinatorial
enumerations are finite and rational; the companion proof states their scope.
"""
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parent


def solve(a,b):
    n=len(a);a=[[Fraction(x) for x in row]+[Fraction(y)] for row,y in zip(a,b)]
    for col in range(n):
        pivot=next((i for i in range(col,n) if a[i][col]),None)
        if pivot is None:return None
        a[col],a[pivot]=a[pivot],a[col]
        v=a[col][col];a[col]=[x/v for x in a[col]]
        for i in range(n):
            if i!=col and a[i][col]:
                v=a[i][col];a[i]=[x-v*y for x,y in zip(a[i],a[col])]
    return tuple(row[-1] for row in a)


def dot(a,b):return sum(x*y for x,y in zip(a,b))


def rank(a):
    a=[[Fraction(x) for x in row] for row in a];m=len(a);n=len(a[0]);k=0
    for col in range(n):
        pivot=next((i for i in range(k,m) if a[i][col]),None)
        if pivot is None:continue
        a[k],a[pivot]=a[pivot],a[k]
        v=a[k][col];a[k]=[x/v for x in a[k]]
        for i in range(k+1,m):
            if a[i][col]:
                v=a[i][col];a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==m:break
    return k


def main():
    bits=list(product((-1,1),repeat=4))
    high=[tuple(product_value(x,i) for i in range(5)) for x in bits]
    assert len(set(high))==16
    assert all(product_all(v)==1 for v in high)
    vertices=set();bases=0;singular=0
    for inds in combinations(range(16),5):
        u=solve([high[i] for i in inds],[-1]*5)
        if u is None:singular+=1;continue
        bases+=1
        if all(1+dot(v,u)>=0 for v in high):vertices.add(u)
    expected={tuple(Fraction(sign*int(i==j)) for i in range(5))
              for j in range(5) for sign in (-1,1)}
    expected.update(tuple(Fraction(x,3) for x in v) for v in high)
    assert vertices==expected
    classifications=[]
    for u in sorted(vertices):
        supported=[(1,)+x for x,v in zip(bits,high) if 1+dot(v,u)>0]
        weights=[(1+dot(v,u))/16 for v in high if 1+dot(v,u)>0]
        assert sum(weights)==1
        assert all(sum(w*p[i]*p[j] for w,p in zip(weights,supported))==int(i==j)
                   for i in range(5) for j in range(5))
        anchor=next(inds for inds in combinations(range(len(supported)),5)
                    if rank([supported[i] for i in inds])==5)
        values=set()
        for signs in product((-1,1),repeat=5):
            c=solve([supported[i] for i in anchor],signs)
            assert c is not None
            if all(dot(c,p) in (-1,1) for p in supported):values.add(c)
        nontrivial=[]
        for c in values:
            support=[i for i,x in enumerate(c) if x]
            if len(support)==1:
                assert abs(c[support[0]])==1
            else:
                assert len(support)==4
                assert all(abs(c[i])==Fraction(1,2) for i in support)
                assert len({product_all([p[i] for i in support]) for p in supported})==1
                nontrivial.append(c)
        if len(supported)==11:
            moments=[[1]+list(p[1:])+[p[i]*p[j] for i,j in combinations(range(1,5),2)] for p in supported]
            assert rank(moments)==11
            assert len(values)==10 and not nontrivial
        else:
            assert len(supported)==8 and len(values)==18 and len(nontrivial)==8
        classifications.append({'vertex':[str(x) for x in u],
            'supportSize':len(supported),'signLinearForms':len(values),
            'nontrivialForms':[[str(x) for x in c] for c in sorted(nontrivial)]})
    out={'passed':True,'activeFiveFaceSetsExhausted':bases+singular,
         'invertibleFaceSets':bases,'singularFaceSets':singular,
         'polytopeVertices':len(vertices),'classification':classifications,
         'conclusion':'any non-coordinate sign vector in a five-row orthogonal sign span uses four half-coefficients and a closed quadruple',
         'noveltyClaim':False}
    (ROOT/'classification.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print({k:v for k,v in out.items() if k!='classification'})


def product_all(a):
    out=1
    for x in a:out*=x
    return out


def product_value(x,i):
    return product_all(x[j] for j in range(4) if j!=i) if i<4 else product_all(x)


if __name__=='__main__':main()
